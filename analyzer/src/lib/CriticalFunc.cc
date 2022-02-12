#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"

#include "CriticalFunc.h"

// #include <spawn.h>
// #include <sys/wait.h>
#include <sys/stat.h>
#include <unistd.h>
#include <queue>

#include <llvm-c/Core.h>

#ifndef DEBUG_PRINT
bool DEBUG_PRINT = false;
#endif

// #define VER_DIR  "v5.2.13/collect5/"
// string VER_DIR; //= "v5.2.13/testCollect3/";
// string VER_DIR  = "v5.2.13/collect6/";

// string BASE_DIR;// = "/data/navid/MOSE/kernel-analysis/analyzer/";
// string BASE_DIR = "/data/navid/MOSE/kernel-analysis/clone11/";
string WRK_DIR, FOI_DIR;

using namespace llvm;
using namespace std;

std::set<std::string> blackListedOpCodes;
std::map<Function *, std::vector<std::vector<uint32_t>>> function_flattened_paths;

bool debug_run = false;
std::map<std::string, uint32_t> opcodeMap;
std::map<uint32_t, std::string> opcodeMapRev;

map<int, Instruction *> errPathsLastFoiUseMap;
map<int, string> errPathLastCallCheckSide;
map<Function *, set<Function *>> calleeFuncsMap;
map<string, set<tuple<string, string>>> calleeFoiLastUse;
map<string, set<string>> iCallMap;
map<string, int> funcDefinitionMap;
map<int, string> bcFileMap;
set<string> releaseTerminals;
set<string> initialFOIs;

map<int, string> insnPathToCSMap;
map<int, vector<string>> pathConditionMap;
int insnPathIndex = 0;
vector<pair<vector<uint32_t>, int>> errFlattenPaths_to_foi;
vector<pair<vector<uint32_t>, int>> normalFlattenPaths_to_foi;
vector<int> loopFlattenPaths_to_foi, conditionally_released_paths, escapingFlattenPaths_to_foi;
map<int, pair<string, int>> escapedPathsFoiStarts;
map<Function *, vector<vector<BasicBlock *>>> function_paths;

set<vector<BasicBlock *>> errPathTailSet;
map<Value *, Instruction *> equivalenceCausalMap;
BasicBlock *escapingBB;

set<pair<Function *, int>> escapingValuesSet;
map<string, set<string>> callersMap;
map<string, Module *> alreadyLoadedModules;

set<Value *> visitedUses;
int callDepth = 0;
uint32_t foi_index = -1;
string FOI;
auto MAX_VAL = std::numeric_limits<unsigned int>::max();
#define MAX_PATHS_NUM 1000
#define MAX_PATHS_LEN 500
#define MAX_EXPLORE_TRY 100000 //100k
#define MAX_ESCAPEDTO_NUM 10

void debug_print_BB(BasicBlock *BB, bool verbose = false)
{
  OP << "+=+=+=+=+=+=+=+=\n";
  if (verbose)
  {
    OP << "BB Addr: " << BB << "\n";
  }
  for (auto &I : *BB)
  {
    if (verbose)
    {
      OP << I << "\n";
      continue;
    }
    std::string opName = I.getOpcodeName(), clName;
    if (blackListedOpCodes.find(opName) != blackListedOpCodes.end())
      continue;
    auto CInsn = dyn_cast<CallInst>(&I);
    if (CInsn)
    {
      auto CF = CInsn->getCalledFunction();
      if (CF)
      {
        auto calledF = CF->stripPointerCasts();
        auto *callee = dyn_cast<Function>(calledF);
        clName = callee->getName();
      }
      else
        clName = "*";
      OP << opName << " " << clName << "\n";
    }
    else
      OP << opName << "\n";
  }
  OP << "+=+=+=+=+=+=+=+=\n";
}

Function *getCallee(CallInst *CL)
{
  if (CL->getCalledFunction())
  {
    auto calleeConst = CL->getCalledFunction()->stripPointerCasts();
    return dyn_cast<Function>(calleeConst);
  }
  return NULL;
}

FunctionType *getCalleeVal(CallInst *CL)
{
  auto CV = CL->getCalledValue();
  if (dyn_cast<InlineAsm>(CV))
    return NULL;
  Type *t = CV->getType();
  FunctionType *ft = cast<FunctionType>(cast<PointerType>(t)->getElementType());
  if (DEBUG_PRINT)
    OP << *CV << "\n"
       << *t << "\n"
       << *ft << "\n";
  return ft;
}

Module *load_module(std::string bc_file, llvm::LLVMContext &context)
{
  //load new module
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseIRFile(bc_file, Err, context);
  if (M == NULL)
  {
    OP << bc_file << ": error loading module file\n";
    return NULL;
  }
  Module *loadedModule = M.release();
  return loadedModule;
}

void Tokenize(const string &str,
              vector<string> &tokens,
              const string &delimiter = " ")
{
  if (str.length() < delimiter.length())
  {
    if (DEBUG_PRINT)
      OP << "delimiter is longer than string!\n";
    tokens.push_back(str);
    return;
  }
  string::size_type lastPos = str.find(delimiter, 0);
  if (lastPos == string::npos)
  {
    if (DEBUG_PRINT)
      OP << "delimiter not present in string!\n";
    tokens.push_back(str);
    return;
  }
  else if (lastPos == 0)
  {
    lastPos += delimiter.length();
  }
  else
  {
    tokens.push_back(str.substr(0, lastPos));
    lastPos += delimiter.length();
  }
  string::size_type pos = str.find(delimiter, lastPos);

  while (string::npos != pos)
  {
    tokens.push_back(str.substr(lastPos, pos - lastPos));
    lastPos = pos + delimiter.length();
    pos = str.find(delimiter, lastPos);
  }
  if (lastPos < str.length() && lastPos != string::npos)
    tokens.push_back(str.substr(lastPos));
}

vector<vector<uint32_t>> flattenBB(llvm::BasicBlock *BB)
{

  if (DEBUG_PRINT)
    debug_print_BB(BB);
  vector<vector<uint32_t>> flatted;
  for (auto &I : *BB)
  {
    std::string opName = I.getOpcodeName();
    if (blackListedOpCodes.find(opName) != blackListedOpCodes.end())
      continue;
    std::string operand = "";
    unsigned opcode = I.getOpcode();

    switch (opcode)
    {
    case Instruction::Alloca:
    {
      auto alloc = dyn_cast<AllocaInst>(&I);
      std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      alloc->getAllocatedType()->print(rso);

      operand = " " + rso.str();
      break;
    }
    case Instruction::Call:
    {
      auto CI = dyn_cast<CallInst>(&I);

      if (auto callee = getCallee(CI))
      {
        if (callee->getName().startswith("llvm."))
          continue; //skipp calls to llvm.

        // follow callee CFG
        if (function_flattened_paths.find(callee) != function_flattened_paths.end())
        {
          OP << "following callee: " << callee->getName() << "\n";
          auto F_paths = function_flattened_paths[callee];
          if (flatted.size() == 0)
          {
            for (auto &F_flat_path : F_paths)
            {
              flatted.push_back(F_flat_path);
            }
          }
          else
          {
            for (auto &already_flatted : flatted)
              for (auto &F_flat_path : F_paths)
              {
                already_flatted.insert(already_flatted.end(), F_flat_path.begin(), F_flat_path.end());
              } //append it to currentFlatted
          }
          break;
        }
        else
          operand += " " + callee->getName().str();
      }
      else if (auto iCall = getCalleeVal(CI))
      {
        auto sig = extractFuncSignature(iCall);
        if (iCallMap.find(sig) != iCallMap.end())
        {
          auto cleeN = *iCallMap[sig].begin();
          operand += " " + cleeN;
        }
        else
        { //it's rare
          operand += " unknownICall";
        }
      }
      else
      {
        operand += " inlineAsm";
      }
      string op_sig = opName + operand;
      uint32_t op_index;
      if (opcodeMap.find(op_sig) == opcodeMap.end())
      {
        auto new_index = (uint32_t)opcodeMap.size();
        opcodeMap[op_sig] = new_index;
        opcodeMapRev[new_index] = op_sig;
        op_index = new_index;
      }
      else
      {
        op_index = opcodeMap[op_sig];
      }

      if (flatted.size() == 0)
      {
        flatted.push_back({op_index});
      }
      else
      {
        for (auto &fltd : flatted)
        {
          fltd.push_back(op_index);
        }
      }

      if (op_sig == "call " + FOI)
      {
        foi_index = op_index;
      }
      break;
    }

    } //switch end

    if (opName != "call")
    {
      string op_sig = opName + operand;
      uint32_t op_index;
      if (opcodeMap.find(op_sig) == opcodeMap.end())
      {
        auto new_index = (uint32_t)opcodeMap.size();
        opcodeMap[op_sig] = new_index;
        opcodeMapRev[new_index] = op_sig;
        op_index = new_index;
      }
      else
      {
        op_index = opcodeMap[op_sig];
      }

      if (flatted.size() == 0)
      {
        flatted.push_back({op_index});
      }
      else
      {
        for (auto &fltd : flatted)
        {
          fltd.push_back(op_index);
        }
      }
    }
  }

  return flatted;
}

void countFuncCalls(Module *M)
{
  std::map<std::string, uint16_t> allFuncMap;
  std::string calleeKey;
  std::ofstream callerFile;
  callerFile.open(WRK_DIR + "sample_callSite.txt", std::ios::app);
  if (!callerFile.is_open())
  {
    OP << "Failed to open file:\n"
       << WRK_DIR + "sample_callSite.txt\n";
    exit(1);
  }
  for (auto &F : *M)
    for (inst_iterator i = inst_begin(F); i != inst_end(F); ++i)
    {
      CallInst *CI = dyn_cast<CallInst>(&*i);
      if (CI != NULL && CI->getCalledFunction())
      {
        llvm::Constant *calledF = CI->getCalledFunction()->stripPointerCasts();
        if (calledF == NULL)
        {
          if (DEBUG_PRINT)
            OP << "Failed to get Called Func\n";
          return;
        }
        Function *callee = dyn_cast<Function>(calledF);
        if (callee == NULL)
        {
          if (DEBUG_PRINT)
            OP << "FAILED to convert\n";
          return;
        }
        StringRef calleeName = callee->getName();
        if (calleeName.startswith("llvm."))
          continue;
        if (DEBUG_PRINT)
          OP << calleeName << " IS BEING CALLED\n";

        std::string calleeSrcPath;
        std::string callerSrcPath;
        if (DILocation *Loc = CI->getDebugLoc())
        {
          callerSrcPath = Loc->getFilename().str() +
                          +":" + std::to_string(Loc->getLine());
          callerFile << calleeName.str() << "\t" << callerSrcPath << "\n";
          if (DEBUG_PRINT)
            OP << calleeName << " is being called from " << callerSrcPath << "\n";
        }
        inst_iterator insnIter = inst_begin(callee);
        if (insnIter != inst_end(callee))
        { //not all functions has insn
          Instruction *I = dyn_cast<Instruction>(&*insnIter);
          if (DILocation *Loc = I->getDebugLoc())
          {
            calleeSrcPath = Loc->getFilename().str() +
                            +":" + std::to_string(Loc->getLine());
          }
          else
          {
            if (DEBUG_PRINT)
              OP << "NO DEBUG INFO!! on " << calleeName << "\n";
            //just double checking!!
            MDNode *N = I->getMetadata("dbg");
            if (!N)
            {
              if (DEBUG_PRINT)
                OP << "NO debug MetaData as well!\n";
            }
            else
            {
              DILocation *Lc = dyn_cast<DILocation>(N);
              if (!Loc)
                return;
              std::string FL = Lc->getDirectory().str() + Lc->getFilename().str();
              if (DEBUG_PRINT)
                OP << "BUT found this: " << FL << "\n";
            }
          }
        }
        if (DEBUG_PRINT)
          OP << calleeName << " is " << calleeSrcPath << "\n";
        calleeKey = calleeName.str() + ":" + calleeSrcPath;
        if (allFuncMap.find(calleeKey) == allFuncMap.end())
          allFuncMap[calleeKey] = 1;
        else
          allFuncMap[calleeKey] += 1;
      }
    }

  std::set<std::pair<uint16_t, std::string>> outSet;
  for (auto i = allFuncMap.begin(); i != allFuncMap.end(); ++i)
  {
    std::pair<uint16_t, std::string> p;
    p.first = i->second;
    p.second = i->first;
    outSet.insert(p);
  }

  std::ofstream countLog;
  countLog.open("countLogTmp.txt", std::ios::out);
  for (auto i = outSet.begin(); i != outSet.end(); ++i)
  {
    if (DEBUG_PRINT)
      OP << "LOG: " << i->second << " " << i->first << "\n";
    countLog << "LOG: " << i->second << " " << i->first << "\n";
  }

  callerFile.close();
  countLog.close();
}

void debug_dump_insn_operands(Instruction *Insn)
{
  OP << *Insn << "\n";
  OP << "dumping: " << Insn->getOpcodeName() << "\n";
  OP << *Insn << "\n";
  for (int i = 0; i < Insn->getNumOperands(); ++i)
  {
    auto op = Insn->getOperand(i);
    OP << *op << "\n"
       << op->getName() << "\n";
  }
}
//flatten paths of each function, it means we follow calless at most one level in call graph
//here I use indexed opCode in paths
void flatten_funcs(map<Function *, vector<vector<BasicBlock *>>> function_paths)
{
  OP << "Falttening the functions\n";

  for (auto &pair : function_paths)
  {
    auto F = pair.first;
    auto paths = pair.second;
    if (paths.size() > 1000)
    {
      continue;
    }
    if (DILocation *Loc = F->getEntryBlock().getFirstNonPHI()->getDebugLoc())
    {
      auto foi_location = Loc->getFilename().str() +
                          +":" + std::to_string(Loc->getLine());
      OP << "flattening function: " << F->getName() << "\n"
         << foi_location << "\n";
    }

    vector<vector<uint32_t>> flattedPath;
    for (auto &path : paths)
    {
      vector<uint32_t> flatted;
      for (auto &F_BB : path)
      {

        for (auto &I : *F_BB)
        {
          std::string opName = I.getOpcodeName();
          if (blackListedOpCodes.find(opName) != blackListedOpCodes.end())
            continue;
          std::string operand = "";
          unsigned opcode = I.getOpcode();

          switch (opcode)
          {
          case Instruction::Alloca:
          {
            auto alloc = dyn_cast<AllocaInst>(&I);
            std::string type_str;
            llvm::raw_string_ostream rso(type_str);
            alloc->getAllocatedType()->print(rso);

            operand = " " + rso.str();
            break;
          }
          case Instruction::Call:
          {
            auto CI = dyn_cast<CallInst>(&I);
            auto CF = CI->getCalledFunction();
            if (CF)
            { //not indirect call
              auto calledF = CF->stripPointerCasts();
              auto *callee = dyn_cast<Function>(calledF);
              if (callee->getName().startswith("llvm."))
                continue; //skipp calls to llvm.
              operand += " " + callee->getName().str();
            }
            else
            { //indirect call
              operand += " *";
            }
            break;
          }
          }
          string op_sig = opName + operand;
          uint32_t op_index;
          if (opcodeMap.find(op_sig) == opcodeMap.end())
          {
            auto new_index = (uint32_t)opcodeMap.size();
            opcodeMap[op_sig] = new_index;
            opcodeMapRev[new_index] = op_sig;
            op_index = new_index;
          }
          else
          {
            op_index = opcodeMap[op_sig];
          }
          flatted.push_back(op_index);

        } // end of Insn loop in each BB
      }
      flattedPath.push_back(flatted);
    }
    function_flattened_paths[F] = flattedPath;
  }
}

void vec_print(std::vector<uint32_t> vec)
{
  for (auto &item : vec)
  {
    OP << item << " ";
  }
  OP << "\n";
}

vector<string> readin_bc_list(void)
{
  vector<string> read_list;
  string line;
  std::ifstream bcstream;
  auto path = WRK_DIR + "bc.list";
  bcstream.open(path, std::ios::in);
  if (!bcstream.is_open())
  {
    OP << "Failed to open bc.list\n"
       << path + "\n";
    exit(1);
  }
  while (std::getline(bcstream, line))
  {
    read_list.push_back(line);
  }

  return read_list;
}

std::map<std::string, std::set<std::string>> readin_call_sites()
{
  std::map<std::string, std::set<std::string>> callSiteMap;
  std::ifstream call_sites;

  auto path = WRK_DIR + "callSites.txt";
  call_sites.open(path, std::ios::in);
  if (!call_sites.is_open())
  {
    OP << "Failed to open callSites.txt\n"
       << WRK_DIR + "callSites.txt\n";
    exit(1);
  }
  std::string line;
  while (std::getline(call_sites, line))
  {
    std::istringstream iss(line);
    std::string fnName, callSt, fullCallSt;
    vector<string> tmp;
    iss >> fnName;
    iss >> fullCallSt;
    Tokenize(fullCallSt, tmp, ":");
    callSt = tmp[0];
    if (callSt.compare(callSt.length() - 2, 2, std::string(".h")) == 0)
    {
      continue;
    }
    if (callSiteMap.find(fnName) == callSiteMap.end())
    {
      std::set<std::string> tmpList;
      tmpList.insert(callSt);
      callSiteMap[fnName] = tmpList;
    }
    else
    {
      std::set<std::string> tmpList = callSiteMap[fnName];
      if (tmpList.find(callSt) == tmpList.end())
      {
        tmpList.insert(callSt);
        callSiteMap[fnName] = tmpList;
      }
    }
  }
  call_sites.close();
  return callSiteMap;
}

bool BB_has_call_to_foi(BasicBlock *BB, string FOI, string *loc, Value *&val)
{
  for (auto &I : *BB)
  {
    auto CInsn = dyn_cast<CallInst>(&I);
    if (CInsn)
    {
      if (auto callee = getCallee(CInsn))
      { //direct call
        if (callee->getName() == FOI)
        {
          val = dyn_cast<Value>(CInsn); //out arg
          DILocation *Loc = CInsn->getDebugLoc();
          if (Loc != NULL && loc != NULL)
          {
            auto foi_location = Loc->getFilename().str() +
                                +":" + std::to_string(Loc->getLine());
            if (DEBUG_PRINT)
              OP << "FOI Location: " << foi_location << "\n";
            *loc = foi_location;
          }
          else
          {
            OP << "No DebugInfo!!\n";
          }
          return true;
        }
      }
      else if (auto iCallee = getCalleeVal(CInsn))
      {
        auto sig = extractFuncSignature(iCallee);
        if (iCallMap.find(sig) != iCallMap.end())
        {
          if (FOI == *iCallMap[sig].begin())
          {
            val = dyn_cast<Value>(CInsn); //out arg
            DILocation *Loc = CInsn->getDebugLoc();
            if (Loc != NULL && loc != NULL)
            {
              auto foi_location = Loc->getFilename().str() +
                                  +":" + std::to_string(Loc->getLine());
              if (DEBUG_PRINT)
                OP << "FOI Location: " << foi_location << "\n";
              *loc = foi_location;
            }
            else
            {
              OP << "No DebugInfo!!\n";
            }
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool isConstant(Value *V)
{
  // Invalid input.
  if (!V)
    return false;

  // The value is a constant.
  Constant *Ct = dyn_cast<Constant>(V);
  if (Ct)
    return true;

  return false;
}

bool is_returning_BB(BasicBlock *BB)
{
  auto TI = BB->getTerminator();
  if (TI == NULL)
  {
    OP << "DEBUG:: UNexpected!! BB had no terminator, maybe a malformed BB!\n";
    exit(1); //could just ignore this
  }
  if (dyn_cast<ReturnInst>(TI) != NULL)
  {
    return true;
  }

  if (TI->getNumSuccessors() != 1)
  {
    return false;
  }
  auto succ = TI->getSuccessor(0);
  return is_returning_BB(succ);
}

void debug_print_path(vector<BasicBlock *> path, bool verbose = false)
{
  for (auto &BB : path)
  {
    debug_print_BB(BB, verbose);
  }
}

set<Value *> findEquivalents(Value *, bool loose = false, const vector<BasicBlock *> *path = NULL, bool funcArg = false);

bool isValEscaping(Value *val, const vector<BasicBlock *> *path, Function *F)
{
  if (DEBUG_PRINT)
    OP << *val << "\n";
  visitedUses.clear();
  callDepth = 0;
  auto valEqs = findEquivalents(val, true, path);
  if (DEBUG_PRINT)
    for (auto &eq : valEqs)
    {
      OP << *eq << "\n";
    }
  auto lastBB = path->back();
  auto retI = lastBB->getTerminator();
  if (retI->getNumOperands() == 1)
  { //just making sure
    auto retVal = retI->getOperand(0);
    if (DEBUG_PRINT)
    {
      OP << *retVal << "\n";
      OP << *(F->getReturnType()) << "\n"
         << *(val->getType()) << "\n";
    }
    if (!isConstant(retVal) && valEqs.find(retVal) != valEqs.end())
    {
      escapingValuesSet.insert(make_pair(F, -1));
      return true;
    }
  }

  //escape via ref arg
  for (auto &arg : F->args())
  {
    Value *argVal = &arg;
    if (isConstant(argVal) || !argVal->getType()->isPointerTy())
      continue;
    if (DEBUG_PRINT)
      OP << "Arg for escape check: " << *argVal << "\n";

    if (valEqs.find(argVal) != valEqs.end())
    { //foi is being assigned to an arg
      auto argIndex = arg.getArgNo();
      escapingValuesSet.insert(make_pair(F, argIndex));
      return true;
    }
  }
  for (auto &eq : valEqs)
  {
    GlobalVariable *glbVar = dyn_cast<GlobalVariable>(eq);
    if (glbVar)
    {
      return true; //<-- no need to log this escape!
    }
  }

  return false;
}

bool identify_err_path(const vector<BasicBlock *> &path, Function *F);
void dump_path_for_anomaly_check(vector<pair<vector<BasicBlock *>, Instruction *>> totalPaths, Function *F)
{
  std::ofstream allErrPathFile;
  allErrPathFile.open(FOI_DIR + "allErrPaths.txt", std::ios::app);
  if (!allErrPathFile.is_open())
  {
    OP << "Failed to open file:\n"
       << FOI_DIR + "allErrPaths.txt\n";
    exit(1);
  }
  allErrPathFile << "[-] " << F->getName().str() << "\n";

  for (auto &memb : totalPaths)
  {
    auto const path = memb.first;
    auto TI = memb.second;

    vector<vector<uint32_t>> flattenPath;
    if (!identify_err_path(path, F)) //only interested in errPaths
      continue;

    DILocation *Loc = TI->getDebugLoc();
    string ret_loc = "";
    if (Loc != NULL)
    {
      ret_loc = Loc->getFilename().str() +
                +":" + std::to_string(Loc->getLine());
    }
    allErrPathFile << ret_loc << "\n";

    for (auto it = path.begin(), nextIt = it + 1;
         it != path.end(); ++it, ++nextIt)
    {
      BasicBlock *BB = *it;
      auto returnedPaths = flattenBB(BB);
      if (flattenPath.size() == 0)
      {
        for (auto &retPath : returnedPaths)
        {
          flattenPath.push_back(retPath);
        }
      }
      else
      {
        for (auto &alreadyPath : flattenPath)
        {
          for (auto &retPath : returnedPaths)
          {
            alreadyPath.insert(alreadyPath.end(), retPath.begin(), retPath.end());
          }
        }
      }
    } // end of for loop over path's BBs
    ///dumping the paths into file
    for (auto &flP : flattenPath)
    {
      allErrPathFile << "\t";
      for (auto &op : flP)
        allErrPathFile << op << " ";

      allErrPathFile << "\n";
    }
  }
  allErrPathFile.close();
}

// return all paths from the start of function to its end which has call foi
vector<std::tuple<vector<BasicBlock *>, string, bool, bool, string>>
locate_call_to_foi(Function &F, string FOI)
{
  OP << "locate calls to " << FOI << " in: " << F.getName() << "\n";

  BasicBlock *first_BB = &*(F.begin());
  BasicBlock *currentBB; // = first_BB;
  map<BasicBlock *, bool> visited;
  vector<pair<vector<BasicBlock *>, Instruction *>> totalPaths;
  vector<std::tuple<vector<BasicBlock *>, string, bool, bool, string>> outputPaths;

  class stackElement
  {
  public:
    vector<BasicBlock *> path;            // keeps the path from the start of Func
    vector<pair<Value *, bool>> pathCond; //keeps path condition <-- not sending it up
    bool has_foi;                         // is FOI visited in the path?
    bool loop_foi;                        // is FOI inside a loop?
    bool is_escaping;                     // is FOI result escaping?
  };
  stackElement currentPath;
  vector<stackElement> stack;
  currentPath.path.push_back(first_BB);
  currentPath.has_foi = false;
  currentPath.loop_foi = false;
  currentPath.is_escaping = false; //not used anymore
  stack.push_back(currentPath);
  int explored_paths_num = 0;
  int rounds = 0;
  BasicBlock *trueDest, *falseDest, *foiBB = NULL;
  Value *brCond, *foi_val;
  bool side;

  while (stack.size() != 0)
  {
    currentPath = stack.back();
    stack.pop_back();

    trueDest = NULL;
    falseDest = NULL;
    brCond = NULL;

    currentBB = currentPath.path.back();

    if (DEBUG_PRINT)
    {
      OP << "--------------\n";
      debug_print_BB(currentBB);
    }
    visited[currentBB] = true;
    static string foi_loc;
    Value *val;
    if (!currentPath.has_foi && BB_has_call_to_foi(currentBB, FOI, &foi_loc, val))
    {
      if (DEBUG_PRINT)
        OP << "found the foi loc: " << foi_loc << "\n"
           << *val << "\n";
      currentPath.has_foi = true;
      foiBB = currentBB;
      foi_val = val;
    }
    auto TI = currentBB->getTerminator();
    if (TI == NULL)
    {
      OP << "DEBUG:: UNexpected!! BB had no terminator, maybe a malformed BB!\n";
      continue;
    }

    if (dyn_cast<ReturnInst>(TI) != NULL)
    {
      totalPaths.push_back(make_pair(currentPath.path, TI));
      if (DEBUG_PRINT)
      {
        OP << "+*+*+*+*+*+++\n";
        debug_print_path(currentPath.path);
        OP << "+*+*+*+*+*+++\n";
      }
      if (currentPath.has_foi)
      {

        DILocation *Loc = TI->getDebugLoc();
        string ret_loc;
        if (Loc != NULL)
        {
          ret_loc = Loc->getFilename().str() +
                    +":" + std::to_string(Loc->getLine());
        }

        auto myTuple = std::make_tuple(currentPath.path, foi_loc, currentPath.loop_foi,
                                       currentPath.is_escaping, ret_loc);
        if (DEBUG_PRINT)
        {
          OP << "paired foi path: " << get<1>(myTuple) << "\n";
          OP << "++++++++\n";
          debug_print_path(currentPath.path);
          OP << "++++++++\n";
        }
        outputPaths.push_back(myTuple);
        ++explored_paths_num;
      }
      if (explored_paths_num > MAX_PATHS_NUM)
      {
        OP << "Truncating paths to foi!\n";
        return outputPaths;
      }
      continue; //give up this path
    }
    else if (BranchInst *BI = dyn_cast<BranchInst>(TI))
    {
      if (DEBUG_PRINT)
        OP << *BI << "\n";
      if (BI->isConditional())
      {
        brCond = BI->getCondition();
        if (DEBUG_PRINT)
          OP << *brCond << "\n";
        trueDest = BI->getSuccessor(0);
        falseDest = BI->getSuccessor(1);
      }
    }

    for (auto condIter = currentPath.pathCond.begin(); condIter != currentPath.pathCond.end(); ++condIter)
    {
      Value *cond = (*condIter).first;
      if (cond == brCond)
      {
        brCond = NULL;
        currentPath.pathCond.erase(condIter);
        break;
      }
    }

    if (currentPath.has_foi && currentPath.loop_foi == false)
    {
      if (DEBUG_PRINT)
        OP << *TI << "\n";
      for (unsigned i = 0, NSucc = TI->getNumSuccessors(); i < NSucc; ++i)
      {
        BasicBlock *Succ = TI->getSuccessor(i);
        bool covering = false;
        for (auto &bb : currentPath.path)
        {
          if (bb == Succ)
          {
            covering = true;
            break;
          }
          if (bb == foiBB)
          {
            covering = false;
            break;
          }
        }
        if (covering)
        {
          if (DEBUG_PRINT)
            OP << "The path is looping over FOI\n";
          currentPath.loop_foi = true;
        }
      }
    }

    for (unsigned i = 0, NSucc = TI->getNumSuccessors(); i < NSucc; ++i)
    {
      BasicBlock *Succ = TI->getSuccessor(i);
      if (Succ == trueDest)
        side = true;
      else if (Succ == falseDest)
        side = false;

      if (NSucc == 1 ||
          find(currentPath.path.begin(), currentPath.path.end(), Succ) == currentPath.path.end())
      {
        stackElement newPath = currentPath;
        // currentPath.path.push_back(Succ);
        newPath.path.push_back(Succ);
        if (brCond != NULL)
        {
          newPath.pathCond.push_back(make_pair(brCond, side));
        }
        stack.push_back(newPath);
      }
    }

    if (rounds++ > MAX_EXPLORE_TRY)
    {
      OP << "extract Rounds exceeded! for foi\n";
      break;
    }
  }

  return outputPaths;
}
///////////////
////////////////////
#define ERRNO_PREFIX 0x4cedb000
#define ERRNO_MASK 0xfffff000
#define is_errno(x) (((x)&ERRNO_MASK) == ERRNO_PREFIX)
bool isErrno(Value *V, Function *F = NULL)
{
  // Invalid input.
  if (!V)
    return false;

  if (DEBUG_PRINT)
    OP << *V << "\n"
       << *(V->getType()) << "\n";

  // The value is a constant integer.
  if (ConstantInt *CI = dyn_cast<ConstantInt>(V))
  {
    if (CI->getBitWidth() == 1)
    {
      if (DEBUG_PRINT)
        OP << CI->getValue() << "\n";
      if (CI->getValue() == 0)
        return true; //it is returning false
      else
        return false; //not an error code
    }
    const int64_t value = CI->getValue().getSExtValue();
    if (DEBUG_PRINT)
      OP << "looking at potential errno: " << value << "\n";
    // The value is an errno (negative or positive).
    if (is_errno(-value) || is_errno(value)
        // #if ERRNO_TYPE == 2
        || (-4096 < value && value < 0)
        // #endif
    )

      return true;
  }

  // #if ERRNO_TYPE == 2
  ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(V);
  if (CPN && F)
  {
    if (F->getReturnType()->isPointerTy())
      return true;
  }
  // #endif

  // The value is a constant expression.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V))
  {
    if (CE)
    {
      for (unsigned i = 0, e = CE->getNumOperands();
           i != e; ++i)
      {
        if (isErrno(CE->getOperand(i), F))
          return true;
      }
    }
  }

  return false;
}
///////////////////
bool is_foi_success_path(vector<BasicBlock *> &path)
{

  return false;
}

vector<BasicBlock *> path_reverse(vector<BasicBlock *> path)
{
  vector<BasicBlock *> revPath;
  for (vector<BasicBlock *>::reverse_iterator rit = path.rbegin();
       rit != path.rend(); ++rit)
  {
    revPath.push_back(*rit);
  }
  return revPath;
}

bool is_null_or_zero(Value *val)
{
  if (isConstant(val))
  {
    ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(val);
    if (CPN)
    {
      return true;
    }
    if (auto constInt = dyn_cast<ConstantInt>(val))
      if (constInt->getValue().getSExtValue() == 0 || isErrno(val)) // if check is against Zero or an errno
        return true;
  }
  return false;
}

//detect fallthrough for a conditional terminator:
//if either of successors eventually merges into the other one
bool has_fallthrough(Instruction *TI, const vector<BasicBlock *> &path)
{
  vector<BasicBlock *> dirtyReachPath;
  auto succ0 = TI->getSuccessor(0);
  auto succ1 = TI->getSuccessor(1);
  if (reaches(succ0, succ1, dirtyReachPath) || reaches(succ1, succ0, dirtyReachPath))
    return true;

  //look for phi node
  auto currBB = TI->getParent();
  bool begin = false;
  for (auto &bb : path)
  {
    if (!begin && bb == currBB)
      begin = true;
    if (!begin)
      continue; //wait for currBB
    Instruction *firstI = &*(bb->begin());
    if (auto phI = dyn_cast<PHINode>(firstI))
    {
      bool succ0_met = false, succ1_met = false;
      for (int i = 0; i < phI->getNumIncomingValues(); ++i)
      {
        if (succ0 == phI->getIncomingBlock(i))
          succ0_met = true;
        else if (succ1 == phI->getIncomingBlock(i))
          succ1_met = true;
      }
      if (succ0_met && succ1_met)
        return true;
    }
  }
  return false;
}

//checks if the path takes err side of currTI (which is conditional br) or not
//err side is the side that the check result is NUll --> null is failure sign but zero is success sign
//if check is against zero, then err side is the side that check result is not zero
bool is_err_side_taken(Instruction *TI, CmpInst::Predicate pred, Value *constOp, const vector<BasicBlock *> &path)
{
  auto trueSide = TI->getSuccessor(0);
  auto falseSide = TI->getSuccessor(1);
  char whichSideGoing = ' '; //should be enum T, F
  char checkAgainst = ' ';   //should be enum Z, N
  if (DEBUG_PRINT)
  {
    debug_print_BB(trueSide);
    debug_print_BB(falseSide);
  }

  if (find(path.begin(), path.end(), trueSide) != path.end())
    whichSideGoing = 'T';
  else if (find(path.begin(), path.end(), falseSide) != path.end())
    whichSideGoing = 'F';
  else
  {
    OP << "IMPOSIBLE: which side is taken??\n";
  }

  if (dyn_cast<ConstantPointerNull>(constOp))
    checkAgainst = 'N';
  else
    checkAgainst = 'Z';

  switch (pred)
  {
  case CmpInst::ICMP_EQ:
    if (checkAgainst == 'N')
    {
      if (whichSideGoing == 'T')
        return true; // == NULL
    }
    else
    {
      if (whichSideGoing == 'F')
        return true; //ret == 0
    }
    break;

  case CmpInst::ICMP_NE:
    if (checkAgainst == 'N')
    {
      if (whichSideGoing == 'F')
        return true; // != NULL
    }
    else
    {
      if (whichSideGoing == 'T')
        return true; //  != 0
    }
    break;

  case CmpInst::ICMP_SLT: //for the case of "ret < 0"
    if (whichSideGoing == 'T')
      return true; //should be true to be in err case
    break;

  case CmpInst::ICMP_SGT: //for the case of "ret > 0" <-- did not see!
    if (whichSideGoing == 'F')
      return true; //should be F to be in error case
    break;

  default:
    OP << "ATTENTION: new type of pred: " << pred << "\n";
    break;
  }

  return false;
}

vector<BasicBlock *> tail_extract(Instruction *CI, const vector<BasicBlock *> &path)
{
  vector<BasicBlock *> tail;
  auto checkBB = CI->getParent();
  bool start = false;
  for (auto &BB : path)
  {
    if (!start && checkBB == BB)
      start = true;
    if (start)
    {
      tail.push_back(BB);
    }
  }

  return tail;
}

bool match_tail(const vector<BasicBlock *> &path)
{
  for (auto &tail : errPathTailSet)
  {
    auto tailIdx = tail.size() - 1;
    for (auto rIt = path.rbegin(); rIt != path.rend(); ++rIt)
    {
      if (tail[tailIdx] != *rIt)
        break;
      if (tailIdx == 0) //matches this tail!
        return true;
      tailIdx--;
    }
  }
  return false;
}

// this function is similar to, but simpler than SanityCheck edge marker, it borrowed some code from there.
bool identify_err_path(const vector<BasicBlock *> &path, Function *F)
{
  if (DEBUG_PRINT)
    for (auto &BB : path)
    {
      debug_print_BB(BB);
    }

  if (match_tail(path))
  {
    if (DEBUG_PRINT)
      OP << "Found errPath via match tail!\n";
    return false;
  }

  auto lastBB = path.back();
  auto TI = lastBB->getTerminator();
  if (TI == NULL)
  {
    OP << "DEBUG:: UNexpected!! BB had no terminator, maybe a malformed BB!\n";
    exit(1);
  }
  auto RI = dyn_cast<ReturnInst>(TI);
  if (RI == NULL)
  {
    OP << "DEBUG:: UNexpected!! last BB is not terminating in RET!\n";
    return false;
  }
  if (DEBUG_PRINT)
    OP << *RI << "\n";
  auto RV = RI->getReturnValue();
  if (RV == NULL)
  {
    if (DEBUG_PRINT)
      OP << "void returning function!\n";
    return false;
  }

  if (isConstant(RV))
  {
    if (isErrno(RV, F))
    {
      return true;
    }
    else
    {
      return false;
    }
  }

  vector<Value *> working_list;
  set<Value *> visited_vals;
  working_list.push_back(RV);
  set<Value *> arg_list;
  for (Argument &arg : F->args())
  {
    arg_list.insert((Value *)(&arg));
  }

  while (!working_list.empty())
  {
    auto WV = working_list.back();
    working_list.pop_back();

    if (arg_list.find(WV) != arg_list.end())
    { //skip non-constant function args
      continue;
    }
    if (auto LI = dyn_cast<LoadInst>(WV))
    {

      Value *LPO = LI->getPointerOperand();
      for (const auto &U : LPO->users())
      { //find associated store insn
        if (LI == U)
        {
          continue;
        }
        StoreInst *SI = dyn_cast<StoreInst>(U);
        if (SI == NULL)
        {
          continue;
        }
        auto storeBB = SI->getParent();
        if (find(path.begin(), path.end(), storeBB) == path.end())
        {           //found BB is not on this path, ignore it!
          continue; //what if no store were found on this path??
        }
        if (DEBUG_PRINT)
          OP << *SI << "\n";

        if (LPO == SI->getPointerOperand())
        {
          Value *SVO = SI->getValueOperand();
          if (isConstant(SVO))
          {
            if (isErrno(SVO, F))
            {
              return true;
            }
            else if (auto conV = dyn_cast<ConstantInt>(SVO))
            {
              //stored val is const but not errno, check for explicit 0, true, and false
              if (conV->getBitWidth() == 1)
              { //returning boolian
                if (DEBUG_PRINT)
                  OP << conV->getValue() << "\n";
                if (conV->getValue() == 0)
                  return true; //it is returning false
                else
                  return false; //not an error code: is "return true;""
              }
              if (conV->getValue().getSExtValue() == 0)
              {
                return false; //it is a return 0;
              }

              break; //the constant being returned is not errNo, 0, true, or false
            }
          }
          else
          {
            if (DEBUG_PRINT)
            {
              OP << "should follow this:\n";
              OP << *SVO << "\n";
            }
            if (visited_vals.find(SVO) == visited_vals.end())
            {
              working_list.push_back(SVO);
              visited_vals.insert(SVO);
            }
            break;
          }
        }
      }
    }
    else if (auto CI = dyn_cast<CallInst>(WV))
    {
      auto CF = CI->getCalledFunction();
      if (CF)
      { //not indirect call
        auto calledF = CF->stripPointerCasts();
        auto *callee = dyn_cast<Function>(calledF);
        auto clName = callee->getName();
        if (clName == "PTR_ERR" || clName == "ERR_PTR")
        {
          return true;
        }
      }
    }
    else if (auto BI = dyn_cast<BitCastInst>(WV))
    {
      if (DEBUG_PRINT)
        OP << *BI << "\n";
      auto BCO = BI->getOperand(0);
      if (isConstant(BCO))
      {
        if (isErrno(BCO, F))
        {
          return true;
        }
      }
      else
      {
        if (DEBUG_PRINT)
        {
          OP << "should follow this:\n";
          OP << *BCO << "\n";
        }
        if (visited_vals.find(BCO) == visited_vals.end())
        {
          working_list.push_back(BCO);
          visited_vals.insert(BCO);
        }
      }
    }
    else if (auto TI = dyn_cast<TruncInst>(WV))
    {
      if (DEBUG_PRINT)
        OP << *TI << "\n";
      // debug_dump_insn_operands(TI);
      auto TIO = TI->getOperand(0);
      if (isConstant(TIO))
      {
        if (isErrno(TIO, F))
        {
          return true;
        }
      }
      else
      {
        if (DEBUG_PRINT)
        {
          OP << "should follow this:\n";
          OP << *TIO << "\n";
        }
        if (visited_vals.find(TIO) == visited_vals.end())
        {
          working_list.push_back(TIO);
          visited_vals.insert(TIO);
        }
      }
    }
    else if (auto GEP = dyn_cast<GetElementPtrInst>(WV))
    {
      Value *PO = GEP->getPointerOperand();

      if (isConstant(PO))
      {
        if (isErrno(PO, F))
        {
          return true;
        }
      }
      else
      {
        if (DEBUG_PRINT)
        {
          OP << "should follow this:\n";
          // debug_dump_insn_operands(dyn_cast<Instruction>(SVO));
          OP << *PO << "\n";
        }
        if (visited_vals.find(PO) == visited_vals.end())
        {
          working_list.push_back(PO);
          visited_vals.insert(PO);
        }
      }
    }
    else if (auto UI = dyn_cast<UnaryInstruction>(WV))
    {
      Value *UO = UI->getOperand(0);
      if (isConstant(UO))
      {
        if (isErrno(UO, F))
        {
          return true;
        }
      }
      else
      {
        // debug_dump_insn_operands(dyn_cast<Instruction>(SVO));
        if (DEBUG_PRINT)
          OP << *UO << "\n";
        if (visited_vals.find(UO) == visited_vals.end())
        {
          working_list.push_back(UO);
          visited_vals.insert(UO);
        }
      }
    }
    else if (auto BO = dyn_cast<BinaryOperator>(WV))
    {
      Value *BO1 = BO->getOperand(0);
      Value *BO2 = BO->getOperand(1);
      if (isConstant(BO1))
      {
        if (isErrno(BO1, F))
        {
          return true;
        }
      }
      else
      {
        // debug_dump_insn_operands(dyn_cast<Instruction>(SVO));
        if (DEBUG_PRINT)
          OP << *BO1 << "\n";
        if (visited_vals.find(BO1) == visited_vals.end())
        {
          working_list.push_back(BO1);
          visited_vals.insert(BO1);
        }
      }
      if (isConstant(BO2))
      {
        if (isErrno(BO2, F))
        {
          return true;
        }
      }
      else
      {
        // debug_dump_insn_operands(dyn_cast<Instruction>(SVO));
        if (DEBUG_PRINT)
          OP << *BO2 << "\n";
        if (visited_vals.find(BO2) == visited_vals.end())
        {
          working_list.push_back(BO2);
          visited_vals.insert(BO2);
        }
      }
    }
    else if (auto PN = dyn_cast<PHINode>(WV))
    {
      // Check each incoming value.
      for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
      {
        Value *IV = PN->getIncomingValue(i);
        // The incoming value is a constant.
        if (isConstant(IV))
        {
          if (isErrno(IV, F))
            return true;
        }
        else
        {
          if (DEBUG_PRINT)
            OP << *IV << "\n";
          if (visited_vals.find(IV) == visited_vals.end())
          {
            working_list.push_back(IV);
            visited_vals.insert(IV);
          }
        }
      }
    }
    else if (auto SI = dyn_cast<SelectInst>(WV))
    {
      Value *SVT = SI->getTrueValue();
      Value *SVF = SI->getFalseValue();
      if (isConstant(SVT))
      {
        if (isErrno(SVT, F))
        {
          return true;
        }
      }
      else
      {
        // debug_dump_insn_operands(dyn_cast<Instruction>(SVO));
        if (DEBUG_PRINT)
          OP << *SVT << "\n";
        if (visited_vals.find(SVT) == visited_vals.end())
        {
          working_list.push_back(SVT);
          visited_vals.insert(SVT);
        }
      }
      if (isConstant(SVF))
      {
        if (isErrno(SVF, F))
        {
          return true;
        }
      }
      else
      {
        if (DEBUG_PRINT)
          OP << *SVF << "\n";
        if (visited_vals.find(SVF) == visited_vals.end())
        {
          working_list.push_back(SVF);
          visited_vals.insert(SVF);
        }
      }
    }
    else if (auto ICI = dyn_cast<ICmpInst>(WV))
    {
      if (DEBUG_PRINT)
        OP << "DEBUG: Ignoring icmp insn for error path detection. May introduce FP.\n";
      // do nothing!
    }
    else
    {
      OP << "Cover more LLVM IR!\n";
      exit(1);
    }
  }

  for (auto rit = path.rbegin(); rit != path.rend(); ++rit)
  {
    auto currBB = *rit;
    string foi_loc;
    Value *foi_value;
    if (BB_has_call_to_foi(currBB, FOI, &foi_loc, foi_value))
      break;
    auto currTI = currBB->getTerminator();
    if (auto currBI = dyn_cast<BranchInst>(currTI))
    {
      if (currBI->isConditional())
      {
        auto cond = currBI->getCondition();
        if (DEBUG_PRINT)
          OP << *currBI << "\n"
             << *cond << "\n";

        if (auto CI = dyn_cast<ICmpInst>(cond))
        {
          auto pred = CI->getPredicate();
          if (DEBUG_PRINT)
            OP << pred << "\n";

          Value *constOperand;
          if (isConstant(CI->getOperand(0)))
            constOperand = CI->getOperand(0);
          else if (isConstant(CI->getOperand(1)))
            constOperand = CI->getOperand(1);

          else
          {
            if (DEBUG_PRINT)
            {
              OP << "To be zero/Null check at least one operand should be const.\n";
              OP << *CI << "\n";
            }
            continue;
          }

          if (is_null_or_zero(constOperand))
          {
            if (has_fallthrough(currTI, path))
              continue;

            if (!is_err_side_taken(currTI, pred, constOperand, path))
              break;
            if (DEBUG_PRINT)
              OP << *RV << "\n";

            Type *retValTy = NULL;
            retValTy = RV->getType();
            if (!retValTy)
            {
              OP << "Unexpected return Value! failed to retrieve ret val type!\n"
                 << *RV << "\n";
              exit(1);
            }
            if (DEBUG_PRINT)
              OP << *retValTy << "\n";
            if (retValTy && retValTy->isIntegerTy())
            {
              if (DEBUG_PRINT)
              {
                OP << "Identified errPath via null/zero check instead of errno:\n";
                if (DILocation *Loc = CI->getDebugLoc())
                {
                  auto check_location = Loc->getFilename().str() +
                                        +":" + std::to_string(Loc->getLine());
                  OP << check_location << "\n";
                }
              }

              auto tail = tail_extract(CI, path); //extract the path tail from CI to the ret
              errPathTailSet.insert(tail);

              return true;
            }
          }
        }

        break;
      }
    }
  }
  return false;
}

set<BB_path> extract_func_paths(Function &F)
{
  set<BB_path> outputPaths;

  if (DEBUG_PRINT)
  {
    if (DILocation *Loc = F.getEntryBlock().getFirstNonPHI()->getDebugLoc())
    {
      auto foi_location = Loc->getFilename().str() +
                          +":" + std::to_string(Loc->getLine());
      OP << "flattening function: " << F.getName() << "\n"
         << foi_location << "\n";
    }
    OP << "path extraction for: " << F.getName() << "\n";
  }
  auto first_BB = &F.getEntryBlock();
  BasicBlock *currentBB;
  map<BasicBlock *, bool> visited;
  class stackElement
  {
  public:
    vector<BasicBlock *> path; // keeps the path from the start of Func
  };
  stackElement currentPath;
  vector<stackElement> stack;
  currentPath.path.push_back(first_BB);
  stack.push_back(currentPath);
  int rounds = 0;
  while (stack.size() != 0)
  {
    currentPath = stack.back();
    stack.pop_back();

    currentBB = currentPath.path.back();
    if (DEBUG_PRINT)
      debug_print_BB(currentBB, true);

    auto TI = currentBB->getTerminator();
    if (TI == NULL)
    {
      OP << "DEBUG:: UNexpected!! BB had no terminator, maybe a malformed BB!\n";
      continue;
    }

    if (dyn_cast<ReturnInst>(TI) != NULL)
    {
      outputPaths.insert(currentPath.path);
      auto num = outputPaths.size();
      if (DEBUG_PRINT)
        OP << "number of paths: " << num << "\n";
      if (num > MAX_PATHS_NUM)
      {
        OP << "Truncating the paths!!\n";
        break;
      }
      continue; //finish up this path
    }

    for (unsigned i = 0, NSucc = TI->getNumSuccessors(); i < NSucc; ++i)
    {
      BasicBlock *Succ = TI->getSuccessor(i);

      if (NSucc == 1 ||                                                                           //if there is just one Succ, go to it
          find(currentPath.path.begin(), currentPath.path.end(), Succ) == currentPath.path.end()) // if the succ is not visited on curent path
      {
        stackElement newPath = currentPath; //not already visited
        newPath.path.push_back(Succ);
        stack.push_back(newPath);
      }
    }

    if (rounds++ > MAX_EXPLORE_TRY)
    {
      OP << "extract Rounds exceeded!\n";
      break;
    }
  }

  return outputPaths;
}

void dump_flattenPaths(vector<pair<vector<uint32_t>, int>> &flattenPaths_to_foi,
                       map<int, string> &insnPathToCSMap, map<int, vector<string>> &pathConditionMap, bool isErrDump, bool afterEscape = false)
{
  std::ofstream FullOutFile;
  if (isErrDump)
  {
    if (afterEscape)
      FullOutFile.open(FOI_DIR + "escErrFullPathInsnSeq.txt", std::ios::app);
    else
      FullOutFile.open(FOI_DIR + "errFullPathInsnSeq.txt", std::ios::app);
  }
  else
  {
    if (afterEscape)
      FullOutFile.open(FOI_DIR + "escFullPathInsnSeq.txt", std::ios::app);
    else
      FullOutFile.open(FOI_DIR + "fullPathInsnSeq.txt", std::ios::app);
  }

  if (!FullOutFile.is_open())
  {
    OP << "Failed to open log files in " << FOI_DIR << "\n";
    exit(1);
  }
  std::ofstream PreOutFile;
  if (isErrDump)
  {
    if (afterEscape)
      PreOutFile.open(FOI_DIR + "escErrPrePathInsnSeq.txt", std::ios::app);
    else
      PreOutFile.open(FOI_DIR + "errPrePathInsnSeq.txt", std::ios::app);
  }
  else
  {
    if (afterEscape)
      PreOutFile.open(FOI_DIR + "escPrePathInsnSeq.txt", std::ios::app);
    else
      PreOutFile.open(FOI_DIR + "prePathInsnSeq.txt", std::ios::app);
  }

  if (!PreOutFile.is_open())
  {
    OP << "Failed to open log files in " << FOI_DIR << "\n";
    exit(1);
  }

  std::ofstream PostOutFile;
  if (isErrDump)
  {
    if (afterEscape)
      PostOutFile.open(FOI_DIR + "escErrPostPathInsnSeq.txt", std::ios::app);
    else
      PostOutFile.open(FOI_DIR + "errPostPathInsnSeq.txt", std::ios::app);
  }
  else
  {
    if (afterEscape)
      PostOutFile.open(FOI_DIR + "escPostPathInsnSeq.txt", std::ios::app);
    else
      PostOutFile.open(FOI_DIR + "postPathInsnSeq.txt", std::ios::app);
  }
  if (!PostOutFile.is_open())
  {
    OP << "Failed to open log files in " << FOI_DIR << "\n";
    exit(1);
  }

  std::ofstream insnPath2CS;
  if (isErrDump)
    insnPath2CS.open(FOI_DIR + "errInsnPath_Map_CS.txt", std::ios::app);
  else
    insnPath2CS.open(FOI_DIR + "insnPath_Map_CS.txt", std::ios::app);

  if (!insnPath2CS.is_open())
  {
    OP << "Failed to open log files in " << FOI_DIR << "\n";
    exit(1);
  }

  std::ofstream pathCondMap;
  if (isErrDump)
    pathCondMap.open(FOI_DIR + "errPathConditionMap.txt", std::ios::app);
  else
    pathCondMap.open(FOI_DIR + "pathConditionMap.txt", std::ios::app);

  if (!pathCondMap.is_open())
  {
    OP << "Failed to open log files in " << FOI_DIR << "\n";
    exit(1);
  }
  std::ofstream pathLastFoiCallUseMap;
  std::ofstream pathLastCallCheckSide;
  if (isErrDump)
  {
    pathLastFoiCallUseMap.open(FOI_DIR + "errPathLastFoiCallUseMap.txt", std::ios::app);
    pathLastCallCheckSide.open(FOI_DIR + "errPathLastFoiCallSide.txt", std::ios::app);

    if (!pathLastFoiCallUseMap.is_open() || !pathLastCallCheckSide.is_open())
    {
      OP << "Failed to open log files in " << FOI_DIR << "\n";
      exit(1);
    }
  }
  string print_status;
  for (auto &element : flattenPaths_to_foi)
  {
    auto iPath = element.first;
    auto pathIndex = element.second;
    insnPath2CS << "[" << pathIndex << "]"
                << " " << insnPathToCSMap[pathIndex] << "\n";
    pathCondMap << "[" << pathIndex << "]\n";
    for (auto &line : pathConditionMap[pathIndex])
    {
      pathCondMap << line << "\n";
    }
    pathCondMap << "\n";
    FullOutFile << pathIndex << "- ";
    PreOutFile << pathIndex << "- ";
    PostOutFile << pathIndex << "- ";
    print_status = "pre";
    for (auto &item : iPath)
    {
      FullOutFile << item << " ";
      if (item == foi_index)
      {
        print_status = "post";
        PreOutFile << foi_index << "\n";
      }
      if (print_status == "pre")
        PreOutFile << item << " ";
      if (print_status == "post")
        PostOutFile << item << " ";
    }

    FullOutFile << "\n";
    if (print_status == "post")
      PostOutFile << "\n";

    if (isErrDump)
    {
      auto callInsn = errPathsLastFoiUseMap[pathIndex];
      string lCallName;
      if (callInsn)
      {
        if (auto cl = getCallee(dyn_cast<CallInst>(callInsn)))
        {
          lCallName = cl->getName().str();
        }
        else if (auto icl = getCalleeVal(dyn_cast<CallInst>(callInsn)))
        {
          auto sig = extractFuncSignature(icl);
          if (iCallMap.find(sig) != iCallMap.end())
          {
            lCallName = *iCallMap[sig].begin();
            if (iCallMap[sig].size() > 1)
            {
              if (DEBUG_PRINT)
              {
                OP << "FIXIT: multiple possible iCallee.\n"
                   << *callInsn << "\n";
                for (auto &e : iCallMap[sig])
                  OP << e << "\n";
              }
            }
          }
        }
        else
        {
          OP << "FIXIT: last call was not call/iCall insn";
          exit(1);
        }
        pathLastFoiCallUseMap << pathIndex << "- ";
        pathLastFoiCallUseMap << lCallName << "\n";
        if (DILocation *Loc = callInsn->getDebugLoc())
        { //record the line info
          string callerSrcPath = Loc->getFilename().str() +
                                 +":" + std::to_string(Loc->getLine());
          pathLastFoiCallUseMap << callerSrcPath << "\n";
        }
      }

      if (errPathLastCallCheckSide.find(pathIndex) != errPathLastCallCheckSide.end())
      {
        auto side = errPathLastCallCheckSide[pathIndex];
        pathLastCallCheckSide << pathIndex << "- " << side << "\n";
      }
    }
  }
  FullOutFile.close();
  // OPoutFile.close();
  insnPath2CS.close();
  PostOutFile.close();
  PreOutFile.close();
  pathLastFoiCallUseMap.close();
  pathLastCallCheckSide.close();
}

void dump_calleesFoiLastUse(void)
{

  std::ofstream calleesFoiLastUseMap;
  calleesFoiLastUseMap.open(WRK_DIR + "calleesFoiLastUseMap.txt", std::ios::out);
  if (!calleesFoiLastUseMap.is_open())
  {
    OP << "Failed to open file:\n"
       << WRK_DIR + "calleesFoiLastUseMap.txt\n";
    exit(1);
  }
  //dump calleeFoiLastUse[] into file
  for (auto it = calleeFoiLastUse.begin(); it != calleeFoiLastUse.end(); ++it)
  {
    auto lastN = it->first;
    auto calleeList = it->second;
    calleesFoiLastUseMap << lastN << ": ";
    for (auto &memb : calleeList)
    {
      auto cl = get<0>(memb);
      auto side = get<1>(memb);
      calleesFoiLastUseMap << cl << "|" << side << " ";
    }
    calleesFoiLastUseMap << "\n";
  }
  calleesFoiLastUseMap.close();
}

void dump_loopAndConditionalPaths(vector<int> &loopPathIDs, vector<int> &condPathIDs,
                                  vector<int> &escapingPathIDs, bool afterEscape = false)
{
  std::ofstream loopPathFile;
  loopPathFile.open(FOI_DIR + "loopFoiInsnPaths.txt", std::ios::app);
  if (!loopPathFile.is_open())
  {
    OP << "Failed to open file:\n"
       << FOI_DIR + "loopFoiInsnPaths.txt\n";
    exit(1);
  }
  for (auto &id : loopPathIDs)
  {
    loopPathFile << id << "\n";
  }
  loopPathFile.close();

  std::ofstream condPathFile;
  condPathFile.open(FOI_DIR + "conditionalReleasePaths.txt", std::ios::app);
  if (!condPathFile.is_open())
  {
    OP << "Failed to open file:\n"
       << FOI_DIR + "conditionalReleasePaths.txt\n";
    exit(1);
  }
  for (auto &id : condPathIDs)
  {
    condPathFile << id << "\n";
  }
  condPathFile.close();

  std::ofstream escapingPathFile;
  if (afterEscape)
    escapingPathFile.open(FOI_DIR + "doubleEscapingInsnErrPaths.txt", std::ios::app);
  else
    escapingPathFile.open(FOI_DIR + "escapingInsnErrPaths.txt", std::ios::app);

  if (!escapingPathFile.is_open())
  {
    OP << "Failed to open file:\n"
       << FOI_DIR + "escapingInsnErrPaths.txt\n";
    exit(1);
  }
  for (auto &id : escapingPathIDs)
  {
    escapingPathFile << id << "\n";
  }
  escapingPathFile.close();

  if (afterEscape)
  {
    std::ofstream escapingPathFoiStartsFile;
    escapingPathFoiStartsFile.open(FOI_DIR + "escapedPathsFoiStarts.txt", std::ios::app);
    if (!escapingPathFoiStartsFile.is_open())
    {
      OP << "Failed to open file:\n"
         << FOI_DIR + "escapedPathsFoiStarts.txt\n";
      exit(1);
    }
    for (auto &elem : escapedPathsFoiStarts)
    {
      auto pathId = elem.first;
      auto currFoi = elem.second.first;
      auto argIdx = elem.second.second;
      escapingPathFoiStartsFile << pathId << ": " << currFoi << " " << argIdx << "\n";
    }
    escapingPathFoiStartsFile.close();
  }
}

void dump_calleesMap()
{
  std::ofstream calleesMapFile;
  calleesMapFile.open(WRK_DIR + "calleesMap.txt", std::ios::app);
  if (!calleesMapFile.is_open())
  {
    OP << "Failed to open file:\n"
       << WRK_DIR + "calleesMap.txt\n";
    exit(1);
  }
  for (auto mIt = calleeFuncsMap.begin(); mIt != calleeFuncsMap.end(); ++mIt)
  {
    Function *caller = mIt->first;
    set<Function *> callees = mIt->second;
    calleesMapFile << "[" << caller->getName().str() << "]"
                   << "\n";
    for (auto &cle : callees)
    {
      calleesMapFile << "\t" << cle->getName().str() << "\n";
    }
  }
}

set<BasicBlock *> findReachableBBs(BasicBlock *, map<BasicBlock *, uint32_t> *distanceMap = NULL);

Instruction *findNullCheckInsn(Value *foi_val, set<Value *> &eqSet)
{
  uint32_t currentDistance = MAX_VAL;
  Instruction *nullChekInsn = NULL;
  map<BasicBlock *, uint32_t> distanceMap;
  auto foiReachableBBs = findReachableBBs(dyn_cast<Instruction>(foi_val)->getParent(), &distanceMap);

  //first use the foi_val for null finding
  auto foi_users = foi_val->users();
  for (const auto &UI : foi_users)
  { // UI: usrs iterator
    Value *useVal = &(*UI);
    if (DEBUG_PRINT)
      OP << *useVal << "\n";
    auto cmpInsn = dyn_cast<ICmpInst>(useVal);
    if (cmpInsn)
    {
      if (foiReachableBBs.find(cmpInsn->getParent()) == foiReachableBBs.end())
      { // this use/icmp is not important
        continue;
      }
      Value *compareTo;
      if (cmpInsn->getOperand(0) == foi_val)
      {
        compareTo = cmpInsn->getOperand(1);
      }
      else if (cmpInsn->getOperand(1) == foi_val)
      {
        compareTo = cmpInsn->getOperand(0);
      }
      else
      {
        OP << "Imposible happened!! compare insn is not comparing call insn!\n";
        exit(1);
      }
      ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(compareTo);
      if (CPN)
      {
        nullChekInsn = cmpInsn;
        return nullChekInsn;
      }
    }
  }

  //now use equivanlents
  for (auto &eqVal : eqSet)
  {
    if (DEBUG_PRINT)
    {
      OP << *eqVal << "\n";
    }
    auto users = ((Value *)eqVal)->users();

    for (const auto &UI : users)
    { // UI: usrs iterator
      Value *useVal = &(*UI);
      if (DEBUG_PRINT)
        OP << *useVal << "\n";
      auto cmpInsn = dyn_cast<ICmpInst>(useVal);
      if (cmpInsn)
      {
        if (foiReachableBBs.find(cmpInsn->getParent()) == foiReachableBBs.end())
        { // this use/icmp is not important
          continue;
        }
        Value *compareTo;
        if (cmpInsn->getOperand(0) == eqVal)
        {
          compareTo = cmpInsn->getOperand(1);
        }
        else if (cmpInsn->getOperand(1) == eqVal)
        {
          compareTo = cmpInsn->getOperand(0);
        }
        else
        {
          OP << "Imposible happened!! compare insn is not comparing call insn!\n";
          exit(1);
        }
        ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(compareTo);
        if (CPN)
        {
          auto candidateBB = cmpInsn->getParent();
          auto candidateDist = distanceMap[candidateBB];
          if (candidateDist < currentDistance)
          { //we are interested in the closest null check to foi
            nullChekInsn = cmpInsn;
            currentDistance = candidateDist;
            if (currentDistance == 0)
              return nullChekInsn;
          }
        }
      }
    }
  } // end of nullCheck find
  return nullChekInsn;
}

Instruction *findZeroCheckInsn(Value *target_val, set<Value *> &eqSet)
{
  // bool isNullChecked = false;
  uint32_t currentDistance = MAX_VAL; //some intitial large unsigned
  Instruction *zeroChekInsn = NULL;
  map<BasicBlock *, uint32_t> distanceMap;
  auto foiReachableBBs = findReachableBBs(dyn_cast<Instruction>(target_val)->getParent(), &distanceMap);

  //first use the target_val for null finding
  auto target_users = target_val->users();
  for (const auto &UI : target_users)
  { // UI: usrs iterator
    Value *useVal = &(*UI);
    if (DEBUG_PRINT)
      OP << *useVal << "\n";
    auto cmpInsn = dyn_cast<ICmpInst>(useVal);
    if (cmpInsn)
    {
      if (foiReachableBBs.find(cmpInsn->getParent()) == foiReachableBBs.end())
      { // this use/icmp is not important
        continue;
      }
      Value *compareTo;
      if (cmpInsn->getOperand(0) == target_val)
      {
        compareTo = cmpInsn->getOperand(1);
      }
      else if (cmpInsn->getOperand(1) == target_val)
      {
        compareTo = cmpInsn->getOperand(0);
      }
      else
      {
        OP << "Imposible happened!! compare insn is not comparing call insn!\n";
        exit(1);
      }
      if (auto constInt = dyn_cast<ConstantInt>(compareTo))
        if (constInt->getValue().getSExtValue() == 0 || isErrno(compareTo))
        { // if check is against Zero or an errno
          zeroChekInsn = cmpInsn;
          return zeroChekInsn; //here is the best case, directly checking target_val
        }
    }
  }

  //now use equivanlents
  for (auto &eqVal : eqSet)
  {
    if (DEBUG_PRINT)
    {
      OP << *eqVal << "\n";
    }
    auto users = ((Value *)eqVal)->users();

    for (const auto &UI : users)
    { // UI: usrs iterator
      Value *useVal = &(*UI);
      if (DEBUG_PRINT)
        OP << *useVal << "\n";
      auto cmpInsn = dyn_cast<ICmpInst>(useVal);
      if (cmpInsn)
      {
        if (foiReachableBBs.find(cmpInsn->getParent()) == foiReachableBBs.end())
        { // this use/icmp is not important
          continue;
        }
        Value *compareTo;
        if (cmpInsn->getOperand(0) == eqVal)
        {
          compareTo = cmpInsn->getOperand(1);
        }
        else if (cmpInsn->getOperand(1) == eqVal)
        {
          compareTo = cmpInsn->getOperand(0);
        }
        else
        {
          OP << "Imposible happened!! compare insn is not comparing call insn!\n";
          exit(1);
        }
        if (auto constInt = dyn_cast<ConstantInt>(compareTo))
          if (constInt->getValue().getSExtValue() == 0 || isErrno(compareTo))
          {
            auto candidateBB = cmpInsn->getParent();
            auto candidateDist = distanceMap[candidateBB];
            if (candidateDist < currentDistance)
            { //we are interested in the closest null check to foi
              zeroChekInsn = cmpInsn;
              currentDistance = candidateDist;
              if (currentDistance == 0)
                return zeroChekInsn;
            }
          }
      }
    }
  } // end of nullCheck find
  return zeroChekInsn;
}

//////////////////////
void debug_print_flatPath(vector<uint32_t> path)
{
  for (auto &id : path)
    OP << id << " ";
}

// void process_condOperand(Value *op, vector<set<Value *>> *eqSets, string *fl)
void process_condOperand(Value *op, map<Value *, string> &visitedVals, string &fl)
{
  // auto visitedVals = *valsMap;
  if (isConstant(op))
  {
    if (auto cInt = dyn_cast<ConstantInt>(op))
      fl += to_string(*(cInt->getValue().getRawData())) + " ";
    else if (dyn_cast<ConstantPointerNull>(op))
      fl += "NULL ";
    else if (auto gVar = dyn_cast<GlobalVariable>(op))
      fl += gVar->getName().str() + " ";
    else //ignore other types of const
    {
      OP << "DEBUG: Uncovered const\n";
      OP << *op << "\n";
    }
  }
  else
  { // operand is not constant
    if (DEBUG_PRINT)
      OP << *op << "\n";
    if (visitedVals.find(op) != visitedVals.end())
    {
      fl += visitedVals[op] + " ";
    }
    else
    {
      int count = visitedVals.size();
      fl += "var" + to_string(count) + " ";
      visitedVals[op] = "var" + to_string(count);
    }
  }
}

vector<string> flatten_PathCond(vector<pair<Value *, bool>> &pathCond)
{
  vector<string> output_conds;
  vector<set<Value *>> eqSets;
  map<Value *, string> valsMap;
  for (auto &pCond : pathCond)
  {
    auto cond = pCond.first;
    auto side = pCond.second;
    string fl = "";

    if (auto CI = dyn_cast<ICmpInst>(cond))
    {
      auto pred = CI->getPredicate();
      auto op0 = CI->getOperand(0);
      auto op1 = CI->getOperand(1);

      if (DEBUG_PRINT)
      {
        OP << *cond << "\n";
        OP << pred << " " << *op0 << " " << *op1 << "\n";
      }

      switch (pred)
      {
      case CmpInst::ICMP_NE:
        if (side == true)
          fl += "NE ";
        else
          fl += "EQ ";
        break;
      case CmpInst::ICMP_EQ:
        if (side == true)
          fl += "EQ ";
        else
          fl += "NE ";
        break;
      case CmpInst::ICMP_UGT:
        if (side == true)
          fl += "UGT ";
        else
          fl += "ULE ";
        break;
      case CmpInst::ICMP_UGE:
        if (side == true)
          fl += "UGE ";
        else
          fl += "ULT ";
        break;
      case CmpInst::ICMP_ULT:
        if (side == true)
          fl += "ULT ";
        else
          fl += "UGE ";
        break;
      case CmpInst::ICMP_ULE:
        if (side == true)
          fl += "ULE ";
        else
          fl += "UGT ";
        break;
      case CmpInst::ICMP_SGT:
        if (side == true)
          fl += "SGT ";
        else
          fl += "SLE ";
        break;
      case CmpInst::ICMP_SGE:
        if (side == true)
          fl += "SGE ";
        else
          fl += "SLT ";
        break;
      case CmpInst::ICMP_SLT:
        if (side == true)
          fl += "SLT ";
        else
          fl += "SGE ";
        break;
      case CmpInst::ICMP_SLE:
        if (side == true)
          fl += "SLE ";
        else
          fl += "SGT ";
        break;

      default:
        OP << "DEBUG: cover more predicate: " << pred << "\n";
        exit(1);
      }
      /*     
     ICMP_EQ    = 32,  ///< equal
     ICMP_NE    = 33,  ///< not equal
     ICMP_UGT   = 34,  ///< unsigned greater than
     ICMP_UGE   = 35,  ///< unsigned greater or equal
     ICMP_ULT   = 36,  ///< unsigned less than
     ICMP_ULE   = 37,  ///< unsigned less or equal
     ICMP_SGT   = 38,  ///< signed greater than
     ICMP_SGE   = 39,  ///< signed greater or equal
     ICMP_SLT   = 40,  ///< signed less than
     ICMP_SLE   = 41,  ///< signed less or equal
*/

      process_condOperand(op0, valsMap, fl);
      process_condOperand(op1, valsMap, fl);

      output_conds.push_back(fl);
    }
    else
    {
      OP << "DEBUG: path cond is not ICMP\n";
      OP << *cond << "\n";
    }
  }
  return output_conds;
}

void collect_callees(Function *F)
{
  if (DEBUG_PRINT)
    OP << "collecting callees for: " << F->getName() << "\n";
  set<Function *> currentSet;
  for (inst_iterator insnIt = inst_begin(F); insnIt != inst_end(F); ++insnIt)
  {
    Instruction *insn = &*insnIt;
    auto callInsn = dyn_cast<CallInst>(insn);
    if (callInsn == NULL)
      continue; //not a call insn
    auto callee = getCallee(callInsn);
    if (callee == NULL)
      continue; // encountered indirect call
    if (callee->getName().startswith("llvm."))
      continue;
    if (calleeFuncsMap.find(F) != calleeFuncsMap.end())
      currentSet = calleeFuncsMap[F];
    else
      currentSet.clear(); //make an empty set

    currentSet.insert(callee);
    calleeFuncsMap[F] = currentSet;

    //if needed assign ID to this call
    string op_sig = "call " + callee->getName().str();
    if (opcodeMap.find(op_sig) == opcodeMap.end())
    {
      auto new_index = (uint32_t)opcodeMap.size();
      opcodeMap[op_sig] = new_index;
      opcodeMapRev[new_index] = op_sig;
    }

    if (!callee->isDeclaration())
    { //if callee has body: look into it
      if (calleeFuncsMap.find(callee) == calleeFuncsMap.end())
        collect_callees(callee);
    }
  }
}

tuple<Instruction *, int> find_last_foi_use(const vector<BasicBlock *> &path, set<Value *> &foi_eqs)
{
  Instruction *defaultPtr = NULL;
  for (auto revBBIt = path.rbegin(); revBBIt != path.rend(); ++revBBIt)
  {
    BasicBlock *currBB = (*revBBIt);
    if (DEBUG_PRINT)
      debug_print_BB(currBB);
    for (auto revInsnIt = currBB->rbegin(); revInsnIt != currBB->rend(); ++revInsnIt)
    {
      auto callInsn = dyn_cast<CallInst>(&(*revInsnIt));
      if (callInsn)
      {
        auto callee = getCallee(callInsn);
        bool is_indirect = false;
        if (callee)
        {
          auto clName = callee->getName();
          if (clName.startswith("llvm.") || clName == "PTR_ERR" || clName == "IS_ERR")
            continue;
        }
        else if (auto iClee = getCalleeVal(callInsn))
        {
          if (DEBUG_PRINT)
            OP << *iClee << "\n";
          is_indirect = true;
        }
        else
        { //this skips inline asembly
          continue;
        }
        if (DEBUG_PRINT)
          OP << *callInsn << "\n"; //can be indirect too
        //it should start from 0
        int limit = callInsn->getNumOperands();
        if (is_indirect)
          limit -= 1;
        for (int i = 0; i < limit; ++i)
        {
          Value *arg = callInsn->getOperand(i);
          if (DEBUG_PRINT)
            OP << *arg << "\n";
          if (foi_eqs.find(arg) != foi_eqs.end())
          {
            return make_tuple(callInsn, i);
          }
        }
      }
    }
  }
  return make_tuple(defaultPtr, -1);
}

// here I do a lightweight path exploration
bool reaches(BasicBlock *src, BasicBlock *dst, vector<BasicBlock *> &reachPath)
{
  if (src == dst)
  {
    reachPath.push_back(src);
    return true;
  }
  if (find(reachPath.begin(), reachPath.end(), src) == reachPath.end())
  {
    reachPath.push_back(src);
  }
  auto TI = src->getTerminator();
  for (int i = 0; i < TI->getNumSuccessors(); ++i)
  {
    auto succ = TI->getSuccessor(i);
    if (succ == dst)
    {
      reachPath.push_back(succ);
      return true;
    }
    if (find(reachPath.begin(), reachPath.end(), succ) == reachPath.end())
    {
      reachPath.push_back(succ);
      if (reaches(succ, dst, reachPath))
        return true;
    }
  }

  return false;
}

bool is_under_condition(Instruction *insn, Instruction *foi_check, const vector<BasicBlock *> &path)
{
  BasicBlock *targetBB = insn->getParent();

  set<BasicBlock *> visited;
  vector<BasicBlock *> worklist;
  worklist.push_back(targetBB);

  while (!worklist.empty())
  {
    BasicBlock *currBB = worklist.back();
    worklist.pop_back();

    vector<BasicBlock *> reachPath;
    for (const auto &predBB : predecessors(currBB))
    {
      if (foi_check && predBB == foi_check->getParent())
        continue;
      auto TI = predBB->getTerminator();
      if (TI)
      {
        if (DEBUG_PRINT)
          OP << *TI << "\n";
        if (auto brInsn = dyn_cast<BranchInst>(TI))
        {
          if (brInsn->isConditional())
          {
            auto cond = brInsn->getCondition();
            if (DEBUG_PRINT)
              OP << *cond << "\n";
            Instruction *condI = dyn_cast<Instruction>(cond);
            if (condI == NULL)
              continue;
            if (DEBUG_PRINT)
              OP << *cond << "\n";

            if (!has_fallthrough(TI, path)) //it should not terminate differently
              continue;

            auto succ0 = TI->getSuccessor(0);
            auto res0 = reaches(succ0, targetBB, reachPath);
            reachPath.clear();
            auto succ1 = TI->getSuccessor(1);
            auto res1 = reaches(succ1, targetBB, reachPath);

            if (res0 ^ res1)
              return true;
          }
          //add to worklist predBB
          if (visited.find(predBB) == visited.end())
          {
            visited.insert(predBB);
            worklist.push_back(predBB);
          }
        }
      }
    }
  } //end of while

  return false;
}

bool is_unlikely(ICmpInst *CI)
{
  auto pred = CI->getPredicate();
  if (DEBUG_PRINT)
    OP << pred << "\n";
  if (isConstant(CI->getOperand(0)))
  {
    auto zz = dyn_cast<ConstantInt>(CI->getOperand(0));
    if (zz && zz->getValue() == 0 && pred == CmpInst::ICMP_NE)
    { //pred == NE is my assumption!
      return true;
    }
  }
  if (isConstant(CI->getOperand(1)))
  {
    auto zz = dyn_cast<ConstantInt>(CI->getOperand(1));
    if (zz && zz->getValue() == 0 && pred == CmpInst::ICMP_NE)
    {
      return true;
    }
  }
  return false;
}

bool has_critical_check(vector<BasicBlock *> path, Value *foi_check)
{
  auto foiBB = dyn_cast<Instruction>(foi_check)->getParent();
  for (vector<BasicBlock *>::reverse_iterator rit = path.rbegin(); rit != path.rend(); ++rit)
  {
    BasicBlock *currBB = *rit;
    if (currBB == foiBB)
      return false; //reached foi_check

    if (DEBUG_PRINT)
      debug_print_BB(currBB);

    auto TI = currBB->getTerminator();
    if (TI == NULL)
      return false; //malformed BB
    auto brI = dyn_cast<BranchInst>(TI);
    if (brI)
    {
      if (brI->isConditional())
        return true;
    }
  }
  return false;
}

bool is_calling_foi(Function &F)
{
  for (auto &BB : F)
    for (auto &I : BB)
    {
      if (auto clInsn = dyn_cast<CallInst>(&I))
      {
        if (auto clee = getCallee(clInsn))
        {
          if (clee->getName() == FOI)
          {
            return true;
          }
        }
      }
    }
  return false;
}

bool unlikely_BB(BasicBlock *BB)
{
  int step = 0;
  for (auto rit = BB->rbegin(); rit != BB->rend(); ++rit)
  {
    if (DEBUG_PRINT)
      OP << *rit << "\n";
    switch (step)
    {
    case 0:
      if (dyn_cast<BranchInst>(&*rit) == NULL)
        return false;
      break;
    case 1:
      if (dyn_cast<ICmpInst>(&*rit) == NULL)
        return false;
      break;
    case 2:
      if (dyn_cast<SExtInst>(&*rit) == NULL)
        return false;
      break;
    case 3:
      if (dyn_cast<ZExtInst>(&*rit) == NULL)
        return false;
      break;
    case 4:
    case 5:
    case 6:
      if ((*rit).getOpcode() != Instruction::BinaryOps::Xor)
        return false;
      break;
    case 7:
      if (dyn_cast<ICmpInst>(&*rit) == NULL)
        return false;
      break;

    default:
      break;
    }
    if (++step > 7)
      return true; //it satisfied all conditions
  }
  return false;
}
bool unlikely_path(vector<BasicBlock *> path)
{
  for (auto rit = path.rbegin(); rit != path.rend(); ++rit)
  {
    auto BB = *rit;
    if (DEBUG_PRINT)
      debug_print_BB(BB);
    if (unlikely_BB(BB))
      return true;
  }
  return false;
}

bool infeasible_path(const vector<BasicBlock *> &path, set<Value *> loose_foi_eqs)
{
  for (auto pit = path.begin(); pit != path.end(); ++pit)
  {
    BasicBlock *nextBB, *BB = *pit;
    auto TI = BB->getTerminator();
    auto BI = dyn_cast<BranchInst>(TI);
    if (BI && BI->isConditional())
    {
      nextBB = *(pit + 1);
      Value *cond = BI->getCondition();
      if (DEBUG_PRINT)
      {
        OP << *BI << "\n";
        debug_print_BB(nextBB);
        OP << *cond << "\n";
      }
      if (auto CI = dyn_cast<ICmpInst>(cond))
      {
        auto pred = CI->getPredicate();
        BasicBlock *interestingSide = NULL;
        if (DEBUG_PRINT)
          OP << pred << "\n";

        Value *constOperand, *nonConstOperand;
        if (isConstant(CI->getOperand(0)))
        {
          constOperand = CI->getOperand(0);
          nonConstOperand = CI->getOperand(1);
        }
        else if (isConstant(CI->getOperand(1)))
        {
          constOperand = CI->getOperand(1);
          nonConstOperand = CI->getOperand(0);
        }
        if (loose_foi_eqs.find(nonConstOperand) == loose_foi_eqs.end())
        {
          if (DEBUG_PRINT)
            OP << "This condition is not on foi_val\n";
          continue; // go look on other BBs
        }
        ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(constOperand);

        if (unlikely_BB(BB))
        {
          interestingSide = TI->getSuccessor(1); // wierd case of Unlikely!
        }
        else if (CPN)
        { // this is normal null condition check
          if (pred == CmpInst::ICMP_EQ)
          {
            interestingSide = TI->getSuccessor(1); //FOI success is on false side of condition
          }
          else if (pred == CmpInst::ICMP_NE)
          {
            interestingSide = TI->getSuccessor(0); //FOI success is on true side of condition
          }
        }
        //if the path taking interesting side
        //pit won't be the last BB in path, as it is not returning BB
        if (interestingSide && nextBB != interestingSide)
          return true; //not going through interesting side
      }
    }
  }

  return false;
}

bool is_val_func(Function &F)
{
  return F.isVarArg();
}

string print_type(Type *V)
{
  std::string type_str;
  llvm::raw_string_ostream rso(type_str);
  V->print(rso);
  return type_str;
}
string extractFuncSignature(FunctionType *FT)
{
  if (DEBUG_PRINT)
    OP << *FT << "\n";
  string sig;
  auto RT = FT->getReturnType();
  sig = print_type(RT) + "(";

  for (unsigned i = 0, N = FT->getNumParams(); i < N; ++i)
  {
    auto pt = FT->getParamType(i);
    sig += print_type(pt) + ",";
  }

  if (*(sig.end() - 1) == ',')
    sig.replace(sig.end() - 1, sig.end(), ")");
  else
    sig += ")";
  return sig;
}

bool is_call_checked(Value *CV)
{
  auto callEqs = findEquivalents(CV, true);
  for (auto &eq : callEqs)
  {
    if (dyn_cast<ICmpInst>(eq))
      return true;
  }
  return false;
}
//TODO: detect consumer functions:
//1- if last_use is call, extract callee and its arg list to know which one is foi_val
//2- extract exec paths of callee
//3- record the last use of foi in each of the extracted paths
//4- in patter matching, when the release is identified check if the last uses in sptep 3 are a release
//^^ this will detect uncommon release funcs, too.
void process_last_call(CallInst *last_call, int arg_index, set<string> runningSet)
{

  set<tuple<string, string>> last_use_set; //tuple of (fnName, side)
  //side: Err, Norm, +: means both
  Value *new_foi_value;
  string lastName;

  auto lastFunc = getCallee(last_call);
  if (lastFunc)
  {
    lastName = lastFunc->getName();
  }
  else if (auto lastV = getCalleeVal(last_call))
  { //is iCall
    //resolve lastV to candidate funcs
    auto sig = extractFuncSignature(lastV);
    if (DEBUG_PRINT)
      OP << sig << "\n";
    if (iCallMap.find(sig) == iCallMap.end())
      return;
    lastName = *iCallMap[sig].begin();
    lastFunc = NULL;
  }
  else
  {
    return; //probably inlineAsm
  }

  if (lastName == "list_add" || lastName == "atm_tc_enqueue")
  {
    OP << "HERE!";
  }
  if (calleeFoiLastUse.find(lastName) != calleeFoiLastUse.end())
  {
    if (DEBUG_PRINT)
      OP << "This function is already processed as last foi use: " << lastName << "\n";
    return;
  }
  OP << "processing last func: " + lastName + "\n";
  if (lastName.find("warn") != string::npos || lastName.find("print") != string::npos)
  {
    last_use_set.insert(make_tuple("NULL", "+")); //means leaking
    calleeFoiLastUse[lastName] = last_use_set;
    return;
  }
  if (
      releaseTerminals.find(lastName) != releaseTerminals.end() ||
      lastName.find("kfree") != string::npos || lastName == "iput" || lastName == "kref_put" || lastName.find("unref") != string::npos || lastName.find("list_add") != string::npos || lastName.find("write_once") != string::npos || lastName.find("queue_") != string::npos || lastName.find("refcount") != string::npos)
  {
    last_use_set.insert(make_tuple("TERM", "+"));
    calleeFoiLastUse[lastName] = last_use_set;
    return;
  }
  ////
  if (lastFunc == NULL || lastFunc->isDeclaration())
  { //can be null when there were iCall
    if (DEBUG_PRINT)
      OP << lastName << " is not defined in current module!\n";
    if (funcDefinitionMap.find(lastName) == funcDefinitionMap.end())
    {
      OP << lastName << "has not definition in our bc files!\n"; //like __memcpy
      last_use_set.insert(make_tuple("UNDF", "+"));
      calleeFoiLastUse[lastName] = last_use_set;
      return;
    }
    auto defIdx = funcDefinitionMap[lastName];
    string bcFile = bcFileMap[defIdx];
    LLVMContext *LLVMCtx = new LLVMContext();
    Module *newMod = load_module(bcFile, *LLVMCtx);
    alreadyLoadedModules[bcFile] = newMod;
    if (newMod)
    for (auto &F : *newMod)
    {
      auto fName = F.getName();
      if (fName.startswith("llvm.") || F.isDeclaration())
        continue;
      if (fName == lastName)
      {
        lastFunc = &F;
        break;
      }
    }
  }

  // Here I check to see if func is variable arg list: if so, skip it by returning no paths
  // such functions are problematic when doing equivalence analysis: gives values without parent
  if (is_val_func(*lastFunc))
  {
    last_use_set.insert(make_tuple("VALF", "+")); //stands for Variable Argument List Func
    calleeFoiLastUse[lastName] = last_use_set;
    return;
  }

  auto foi_it = lastFunc->args().begin() + arg_index;
  if (!foi_it)
  { //a sanity check for rare cases
    OP << "Couldn't get new_foi_val iterator!" << lastName << "\n";
    last_use_set.insert(make_tuple("NULL", "+")); //could not get foi_val so just returning ..
    calleeFoiLastUse[lastName] = last_use_set;
    return;
  }
  new_foi_value = dyn_cast<Value>(&*foi_it); //was foi_it, but no difference!
  if (!new_foi_value)
  {
    if (DEBUG_PRINT)
      OP << "Couldn't get new_foi_val\n";
    last_use_set.insert(make_tuple("NULL", "+")); //could not get foi_val so just returning ..
    calleeFoiLastUse[lastName] = last_use_set;
    return;
  }
  if (DEBUG_PRINT)
    OP << *new_foi_value << "\n";

  visitedUses.clear();
  auto allFoiEqs = findEquivalents(new_foi_value, true);
  set<Value *> otherArgs;

  for (auto &arg : lastFunc->args())
  {
    auto currArg = dyn_cast<Value>(&arg);
    if (allFoiEqs.find(currArg) != allFoiEqs.end())
      continue;
    auto firstU = currArg->users().begin();
    if (firstU != currArg->users().end())
    {
      auto firstUval = dyn_cast<Value>(*firstU);
      auto currArgFirstUse = findValueFlow(firstUval, true, currArg);
      if (currArgFirstUse)
        otherArgs.insert(currArgFirstUse);
    }
    otherArgs.insert(currArg);
    if (DEBUG_PRINT)
      OP << "other arg: " << *currArg << "\n";
  }

  //go for finding last use per-path
  auto extr_paths = extract_func_paths(*lastFunc);
  if (extr_paths.size() >= MAX_PATHS_NUM)
  { //Truncated path exploration! assume this func as non-consumer
    if (DEBUG_PRINT)
      OP << "Truncated funcs are assumed to be non-consumer!\n";
    last_use_set.insert(make_tuple("NULL", "+"));
    calleeFoiLastUse[lastName] = last_use_set;
    return;
  }

  for (auto &path : extr_paths)
  {
    auto side = "E";                        //as in ErrPath
    if (!identify_err_path(path, lastFunc)) //if it is errPath or not
      side = "N";                           //as in NormalPath
    visitedUses.clear();
    auto loose_foi_eqs = findEquivalents(new_foi_value, true, &path);
    if (DEBUG_PRINT)
      for (auto &eq : loose_foi_eqs)
        OP << *eq << "\n";

    //check for escaped new_foi_val
    for (auto &eq : loose_foi_eqs)
    {
      GlobalVariable *glbVar = dyn_cast<GlobalVariable>(eq);
      if (glbVar || otherArgs.find(eq) != otherArgs.end())
      { //if eq is global or one of args
        last_use_set.insert(make_tuple("ESCP", side));
        continue;
      }
    }
    //check for escape via return
    auto lastBB = path.back();
    auto retI = lastBB->getTerminator();
    if (retI->getNumOperands() == 1)
    { //just making sure
      auto retVal = retI->getOperand(0);
      if (loose_foi_eqs.find(retVal) != loose_foi_eqs.end() && lastFunc->getReturnType() == new_foi_value->getType())
      {
        last_use_set.insert(make_tuple("ESCP", side));
        continue;
      }
    }

    if (infeasible_path(path, loose_foi_eqs))
    {
      if (DEBUG_PRINT)
      {
        OP << "infeasible path, skipping it!\n";
        debug_print_path(path, true);
      }
      last_use_set.insert(make_tuple("IMPB", side));
      continue;
    }
    auto res = find_last_foi_use(path, loose_foi_eqs);
    auto last_use = get<0>(res);
    auto last_arg_idx = get<1>(res);

    if (!last_use)
    {
      if (DEBUG_PRINT)
        debug_print_path(path);
      last_use_set.insert(make_tuple("NULL", side));
    }
    else
    { //there is a last_use
      if (DEBUG_PRINT)
        OP << *last_use << "\n";
      auto lastC = dyn_cast<CallInst>(last_use);
      if (!is_call_checked(last_use))
      {
        if (strncmp(side, "N", 1) == 0) //if side is N
          side = "+";
      }
      auto lastCallee = getCallee(lastC);
      if (lastCallee)
      {
        auto lastClName = lastCallee->getName();
        if (runningSet.find(lastClName) == runningSet.end())
        {
          runningSet.insert(lastClName);
          process_last_call(lastC, last_arg_idx, runningSet);
        }
        last_use_set.insert(make_tuple(lastClName, side));
      }
      else if (auto lastCallVal = getCalleeVal(lastC))
      { // it's an indirtect call
        if (DEBUG_PRINT)
          OP << *last_use << "\n";
        auto sig = extractFuncSignature(lastCallVal);
        if (DEBUG_PRINT)
          OP << sig << "\n";
        if (iCallMap.find(sig) != iCallMap.end())
        {
          auto lastClName = *iCallMap[sig].begin();
          if (runningSet.find(lastClName) == runningSet.end())
          {
            runningSet.insert(lastClName);
            process_last_call(lastC, last_arg_idx, runningSet);
          }
          last_use_set.insert(make_tuple(lastClName, side));
        }
      }
    }
  }
  calleeFoiLastUse[lastName] = last_use_set;
}

void load_funcsDefMaps(void)
{
  string fDefFileName = WRK_DIR + "funcsDefinitionMap.txt";
  string bcFName = WRK_DIR + "bcFileMap.txt";
  string calleeFoiLUname = WRK_DIR + "calleesFoiLastUseMap.txt";
  string releaseTermsFile = WRK_DIR + "releaseTerminals.txt";
  string iCallSigFile = WRK_DIR + "iCallSigs.txt";
  string callersFile = WRK_DIR + "callersMap.txt";
  string initFOIsFile = WRK_DIR + "potentialFOIs.txt";

  string line;
  ifstream defFile(fDefFileName);
  ifstream bcFile(bcFName);

  if (!defFile.is_open() || !bcFile.is_open())
  {
    OP << "COULD NOT OPEN Func Definition Map Files!\n";
    exit(1);
  }

  while (getline(defFile, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, "\t");
    auto fName = tokens[0];
    auto bcIdx = tokens[1];
    funcDefinitionMap[fName] = stoi(bcIdx);
  }

  while (getline(bcFile, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, "\t");
    auto bcIdx = tokens[0];
    auto bcPath = tokens[1];
    bcFileMap[stoi(bcIdx)] = bcPath;
  }

  ifstream clLast(calleeFoiLUname);
  if (!clLast.is_open())
  {
    OP << "Could not open callees Last Use file!\n"
       << calleeFoiLUname << "\n";
    exit(1);
  }

  while (getline(clLast, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, ":");
    if (tokens.size() < 2)
      continue;

    auto lName = tokens[0];
    set<tuple<string, string>> clList;
    vector<string> tk2;
    Tokenize(tokens[1], tk2, " ");
    for (auto &tup : tk2)
    {
      vector<string> fn;
      Tokenize(tup, fn, "|");
      clList.insert(make_tuple(fn[0], fn[1]));
    }
    calleeFoiLastUse[lName] = clList;
  }

  ifstream termFile(releaseTermsFile);
  if (!termFile.is_open())
  {
    OP << "Could not open Release Terminals file!\n"
       << releaseTermsFile << "\n";
    exit(1);
  }

  while (getline(termFile, line))
  {
    releaseTerminals.insert(line);
  }

  ifstream iCallFile(iCallSigFile);
  if (!iCallFile.is_open())
  {
    OP << "Failed to open iCallSigs.txt\n"
       << iCallSigFile << "\n";
    exit(1);
  }

  while (getline(iCallFile, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, ":");
    if (tokens.size() < 2)
      continue;

    auto sig = tokens[0];
    set<string> fns;
    vector<string> tk2;
    Tokenize(tokens[1], tk2, " ");
    for (auto &f : tk2)
    {
      fns.insert(f);
    }
    iCallMap[sig] = fns;
  }

  ifstream callersMapFile(callersFile);
  if (!callersMapFile.is_open())
  {
    OP << "Failed to open callersMap.txt\n"
       << callersFile << "\n";
    exit(1);
  }

  while (getline(callersMapFile, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, ":");
    if (tokens.size() < 2)
      continue;
    auto fn = tokens[0];
    set<string> callers;
    vector<string> tk2;
    Tokenize(tokens[1], tk2, " ");
    for (auto &cl : tk2)
    {
      callers.insert(cl);
    }
    callersMap[fn] = callers;
  }

  ifstream initFFile(initFOIsFile);
  if (!initFFile.is_open())
  {
    OP << "Could not open Release init FOIs file!\n"
       << initFOIsFile << "\n";
    exit(1);
  }
  while (getline(initFFile, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, " ");
    initialFOIs.insert(tokens[0]);
  }

  defFile.close();
  bcFile.close();
  clLast.close();
  termFile.close();
  iCallFile.close();
  initFFile.close();
}

//determine if this callInsn is calling targetFuncN or not
bool is_escapeeCall(CallInst *CI, string targetFuncN)
{
  bool res = false;
  if (auto cl = getCallee(CI))
  {
    if (cl->getName() == targetFuncN)
      res = true;
  }
  else if (auto icl = getCalleeVal(CI))
  {
    auto sig = extractFuncSignature(icl);
    if (iCallMap.find(sig) != iCallMap.end())
      if (targetFuncN == *iCallMap[sig].begin())
        res = true;
  }

  return res;
}

//locate the module or load it containing to the funciton
Function *find_corresponding_func(string fName)
{
  Function *foundF;
  auto defIdx = funcDefinitionMap[fName];
  string bcFile = bcFileMap[defIdx];
  LLVMContext *LLVMCtx = new LLVMContext();

  if (alreadyLoadedModules.find(bcFile) == alreadyLoadedModules.end())
  {
    Module *Mod = load_module(bcFile, *LLVMCtx);
    alreadyLoadedModules[bcFile] = Mod;
  }

  auto Mod = alreadyLoadedModules[bcFile];
  if (Mod)
  for (auto &F : *Mod)
  {
    if (!F.isDeclaration() && F.getName() == fName)
    {
      foundF = &F;
      break;
    }
  }
  return foundF;
}

//handles the functions that the allocation pointer is escaping to
void process_escaped_to(set<string> callersNames, string escapeeFuncN, int argIndex)
{
  FOI = escapeeFuncN; //this is needed, as we need to know the location of such call in the path
  int tries = 0;
  for (auto &callerN : callersNames)
  {
    if (tries++ >= MAX_ESCAPEDTO_NUM)
      break; //skip if the function is being called from many places (like read_buf)

    //skip recursive funcs!
    if (escapeeFuncN == callerN)
      continue;
    auto callerF = find_corresponding_func(callerN);

    //extract foi_val wrt argIndex
    Value *foi_val = NULL;
    Instruction *intendedCall; //the instruction leading to allocation, used for success side determination
    for (auto &BB : *callerF)
    {
      if (foi_val)
        break;
      for (auto &I : BB)
      {
        if (auto CI = dyn_cast<CallInst>(&I))
        {
          if (is_escapeeCall(CI, escapeeFuncN))
          {
            intendedCall = dyn_cast<Instruction>(&I);
            if (argIndex == -1)
            { //escape via return
              foi_val = dyn_cast<Value>(&I);
            }
            else if (argIndex < I.getNumOperands())
            {
              foi_val = I.getOperand(argIndex);
            }
            if (DEBUG_PRINT)
              OP << *foi_val << "\n";
            break; //found new foi_val
          }
        }
      }
    }

    if (!foi_val || isConstant(foi_val))
    {
      // OP << "Abandoned escape case: " << escapeeFuncN << " indside " << callerN << "\n";
      continue;
    }

    //extract path in callerF going throu escapee Func
    auto paths_to_foi = locate_call_to_foi(*callerF, escapeeFuncN);

    if (paths_to_foi.size() >= MAX_PATHS_NUM)
    {
      OP << "Truncated funcs are being skipped!\n";
      continue;
    }

    if (DEBUG_PRINT)
      OP << "Number of paths in caller: " << paths_to_foi.size() << "\n";
    vector<std::tuple<vector<BasicBlock *>, string, bool, bool, bool, string, pair<string, int>>> labled_paths;
    for (auto &memb : paths_to_foi)
    {
      auto const path = get<0>(memb);  //memb.first;
      auto foi_path = get<1>(memb);    //memb.second;
      auto loop_foi = get<2>(memb);    //is foi in loop
      auto is_escaping = get<3>(memb); //comes as false, filled here if is errPath
      auto ret_path = get<4>(memb);    //where path ends

      auto foi_start = make_pair(escapeeFuncN, argIndex); //where in code is the source of foi val
      //check for success path
      if (!is_call_succesful(intendedCall, &path))
      {
        continue;
      }
      bool isErrPath = identify_err_path(path, callerF);
      if (isErrPath)
      { //just consider errPaths of the caller
        is_escaping = isValEscaping(foi_val, &path, callerF);
        if (is_escaping)
          continue; //skip errPaths that are escaping to prevent FP on paths that we know are escaping
        auto new_element = make_tuple(path, foi_path, isErrPath, loop_foi, is_escaping, ret_path, foi_start);
        labled_paths.push_back(new_element);
      }
    }

    process_paths(labled_paths, foi_val, NULL, callerF, true);
  }
  //now log the collected paths for this escapee
  dump_flattenPaths(errFlattenPaths_to_foi, insnPathToCSMap, pathConditionMap, true, true);
  dump_flattenPaths(normalFlattenPaths_to_foi, insnPathToCSMap, pathConditionMap, false, true);
  dump_loopAndConditionalPaths(loopFlattenPaths_to_foi, conditionally_released_paths,
                               escapingFlattenPaths_to_foi, true);

  errFlattenPaths_to_foi.clear();
  normalFlattenPaths_to_foi.clear();
  loopFlattenPaths_to_foi.clear();
  escapingFlattenPaths_to_foi.clear();
  conditionally_released_paths.clear();
  insnPathToCSMap.clear();
  pathConditionMap.clear();
  errPathLastCallCheckSide.clear();
  escapedPathsFoiStarts.clear();
}

void process_escaping_values(void)
{
  set<Function *> processedEscapingFuncsSet;
  int eCount = 1;
  OP << "Found " << escapingValuesSet.size() << " escaped values\n";

  while (!escapingValuesSet.empty())
  { //escapingValuesSet serves as EA worklist
    if (processedEscapingFuncsSet.size() >= 1000)
      break; //cap on escaping funcs

    auto head = escapingValuesSet.begin();
    auto F = head->first;
    auto argIndex = head->second;
    escapingValuesSet.erase(head);

    if (initialFOIs.find(F->getName()) != initialFOIs.end())
      continue; //skip initial FOIs
    if (processedEscapingFuncsSet.find(F) == processedEscapingFuncsSet.end())
      processedEscapingFuncsSet.insert(F);
    else
      continue;
    OP << eCount++ << "- escaped val: " << F->getName() << " " << argIndex << "\n";
    auto callers = callersMap[F->getName().str()];
    process_escaped_to(callers, F->getName(), argIndex);
  }
}

void process_paths(const vector<std::tuple<vector<BasicBlock *>, string, bool, bool, bool, string, pair<string, int>>> &inputPaths,
                   Value *foi_value, Instruction *foi_check, const Function *F, bool areEscapedPaths = false)
{

  for (auto &memb : inputPaths)
  {
    auto const path = get<0>(memb);
    // auto pathCond = get<1>(memb);
    auto foi_path = get<1>(memb);
    bool isErrPath = get<2>(memb);
    bool loop_foi = get<3>(memb);
    bool is_escaping = get<4>(memb);
    auto ret_path = get<5>(memb);
    auto foi_start = get<6>(memb); //where the foi val can be located in code
    Instruction *last_foi_use = NULL;
    int last_foi_call_arg_index = -1;
    bool conditional_release = false;

    //look for a cond-br after foi-check: to reduce FP
    if (foi_check && !has_critical_check(path, foi_check))
      continue;

    if (DEBUG_PRINT)
      OP << "foi path recieved: " << foi_path << "\n";
    vector<vector<uint32_t>> flattenPath;

    set<Value *> loose_foi_eqs;
    if (isErrPath)
    { // look bakward for the last call using foi_val
      visitedUses.clear();
      loose_foi_eqs = findEquivalents(foi_value, true, &path);
      if (DEBUG_PRINT)
        for (auto &eq : loose_foi_eqs)
          OP << *eq << "\n";
      auto res = find_last_foi_use(path, loose_foi_eqs);
      last_foi_use = get<0>(res);
      last_foi_call_arg_index = get<1>(res);
    }

    if (last_foi_use)
    {
      if (DEBUG_PRINT)
        OP << *last_foi_use << "\n";
      conditional_release = is_under_condition(last_foi_use, foi_check, path);
    }

    for (auto it = path.begin(), nextIt = it + 1;
         it != path.end(); ++it, ++nextIt)
    {
      BasicBlock *BB = *it;
      auto returnedPaths = flattenBB(BB);
      //each returned path has to be appended to the current flattened!
      if (flattenPath.size() == 0)
      {
        for (auto &retPath : returnedPaths)
        {
          flattenPath.push_back(retPath);
        }
      }
      else
      {
        for (auto &alreadyPath : flattenPath)
        {
          for (auto &retPath : returnedPaths)
          {
            alreadyPath.insert(alreadyPath.end(), retPath.begin(), retPath.end());
          }
        }
      }
    } // end of for loop over path's BBs

    for (auto &flP : flattenPath)
    {
      if (DEBUG_PRINT)
        debug_print_flatPath(flP);
      auto flattenPair = make_pair(flP, insnPathIndex);
      insnPathToCSMap[insnPathIndex] = foi_path + "\n" + ret_path;
      if (isErrPath)
      {
        errFlattenPaths_to_foi.push_back(flattenPair);
        if (last_foi_use != NULL)
        {
          errPathsLastFoiUseMap[insnPathIndex] = last_foi_use;
          auto lastC = dyn_cast<CallInst>(last_foi_use);
          if (lastC)
          {
            if (DEBUG_PRINT)
              OP << "\n"
                 << *last_foi_use << "\n";
            assert(last_foi_call_arg_index != -1); //the arg index should've been set properly
            set<string> runningSet;

            process_last_call(lastC, last_foi_call_arg_index, runningSet);

            auto calleeV = getCalleeVal(lastC);
            if (calleeV && !calleeV->getReturnType()->isVoidTy())
            { //skip void returning func for side check
              auto side = "F";
              if (is_call_succesful(lastC, &path))
              {
                side = "S";
              }
              if (!is_call_checked(last_foi_use))
              { //there were no check
                if (strncmp(side, "S", 1) == 0)
                  side = "+";
              }

              errPathLastCallCheckSide[insnPathIndex] = side;
            }
          }
        }
        if (conditional_release)
          conditionally_released_paths.push_back(insnPathIndex);
        if (is_escaping)
          escapingFlattenPaths_to_foi.push_back(insnPathIndex);
      }
      else
        normalFlattenPaths_to_foi.push_back(flattenPair);

      if (loop_foi)
        loopFlattenPaths_to_foi.push_back(insnPathIndex);

      if (areEscapedPaths)
        escapedPathsFoiStarts[insnPathIndex] = foi_start;

      insnPathIndex++;
    }
  }
}

void sequenceMine(void)
{
  // std::map<std::string, std::set<std::string>> callSiteMap;
  // callSiteMap = readin_call_sites();
  // if (DEBUG_PRINT)
  //   OP << "callSite read!\n";
  // std::set<std::string> callSites = callSiteMap[FOI];
  vector<string> bc_files;

  load_funcsDefMaps();
  bc_files = readin_bc_list();

  set<string> processed_bc;
  set<string> processed_funcs;
  int bc_num = bc_files.size();
  int bc_count = 1;
  for (string bc_file : bc_files)
  {
    OP << bc_file << "\n";

    //process bc_file
    if (processed_bc.find(bc_file) != processed_bc.end())
    { //already processed
      continue;
    }
    processed_bc.insert(bc_file);
    if (DEBUG_PRINT)
      OP << bc_file << "\n";
    ifstream f(bc_file.c_str()); //checking if the file exist
    if (f.good() != true)
    {
      OP << "Failed to locate .bc file!!\nSkipping it.\n";
      continue;
    }
    f.close();

    OP << "[" << bc_count++ << "/" << bc_num << "]"
       << " Working on module:\n"
       << bc_file << "\n";
    set<Function *> foi_callers;
    LLVMContext *LLVMCtx = new LLVMContext();
    Module *currentMod = load_module(bc_file, *LLVMCtx);
    alreadyLoadedModules[bc_file] = currentMod;
    if(currentMod)
    for (auto &F : *currentMod)
    {
      auto fName = F.getName();
      if (fName.startswith("llvm.") || F.isDeclaration())
        continue;
      if (fName == FOI)
      { //to make sure we don't go into foi's body
        if (DEBUG_PRINT)
          OP << "DEBUG:: SKIPPING FOI body!!\n";
        continue;
      }
      if (is_calling_foi(F))
        foi_callers.insert(&F);
    }

    function_paths.clear(); //free up the map

    // now look for calls to FOI
    for (auto &F : foi_callers)
    {
      errPathTailSet.clear(); //reset this for each function, this can be a map to leave all the time, but no need!
      equivalenceCausalMap.clear();
      escapingBB = NULL;

      auto fName = F->getName();
      if (fName.startswith("llvm.") || F->isDeclaration() || processed_funcs.find(fName) != processed_funcs.end())
        continue;

      processed_funcs.insert(fName);

      if (DEBUG_PRINT)
        OP << "paths to foi in function: " << fName << "\n";

      auto paths_to_foi = locate_call_to_foi(*F, FOI);
      if (paths_to_foi.size() >= MAX_PATHS_NUM)
      {
        OP << "Truncated funcs are being skipped!\n";
        continue;
      }
      if (DEBUG_PRINT)
        OP << "#paths_to_foi: " << paths_to_foi.size() << "\n";
      vector<std::tuple<vector<BasicBlock *>, string, bool, bool, bool, string, pair<string, int>>> labled_paths, success_paths;
      BasicBlock *foi_BB, *foi_succ1, *foi_succ2, *foi_success;
      string foi_loc;
      Value *foi_value;
      Instruction *foi_check = NULL;

      if (!paths_to_foi.empty())
      {
        if (DEBUG_PRINT)
          OP << "look for foi_bb\n";
        auto const firstPath = get<0>(paths_to_foi.front());
        for (auto &BB : firstPath)
        { // find foi_BB and null check
          if (BB_has_call_to_foi(BB, FOI, &foi_loc, foi_value))
          {
            foi_BB = BB;

            if (DEBUG_PRINT)
            {
              OP << *foi_value << "\n";
              OP << "look for foi null check\n";
            }
            visitedUses.clear();
            auto foi_eqs = findEquivalents(foi_value, true, &firstPath); //shouldn't this be true? loosen gep?
            foi_check = findNullCheckInsn(foi_value, foi_eqs);           //look for null check on FOI
            if (DEBUG_PRINT && foi_check)
            {
              OP << *foi_check << "\n";
              for (auto &eq : foi_eqs)
                OP << *eq << "\n";
            }
            break;
          }
        }
        auto foi_insn = dyn_cast<Instruction>(foi_value);

        if (DEBUG_PRINT)
          OP << "process errPaths and escape analysis\n";
        for (auto &memb : paths_to_foi)
        {
          auto const path = get<0>(memb);  //memb.first;
          auto foi_path = get<1>(memb);    //memb.second;
          auto loop_foi = get<2>(memb);    //is foi in loop
          auto is_escaping = get<3>(memb); //comes as false, filled here if is errPath
          auto ret_path = get<4>(memb);    //where path ends
          bool isErrPath = identify_err_path(path, F);
          if (isErrPath)
            is_escaping = isValEscaping(foi_value, &path, F);
          auto foi_start = make_pair(FOI, -1);
          auto new_element = make_tuple(path, foi_path, isErrPath, loop_foi, is_escaping, ret_path, foi_start);
          labled_paths.push_back(new_element);
        }

        if (foi_check != NULL)
        { //meaning there is a check on FOI result
          auto TI = foi_check->getParent()->getTerminator();
          if (TI->getNumSuccessors() < 2)
          {
            bool isSelect = false, isRet = false;
            visitedUses.clear();
            auto chEqs = findEquivalents((Value *)foi_check);
            for (auto &chEq : chEqs)
            {
              if (isSelect == true || isRet == true)
                break;
              auto chUsers = (&(*chEq))->users();
              for (const auto &U : chUsers)
              {
                auto selInsn = dyn_cast<SelectInst>(&(*U));
                if (selInsn)
                {
                  isSelect = true;
                  break;
                }
                auto retInsn = dyn_cast<ReturnInst>(&(*U));
                if (retInsn)
                {
                  isRet = true;
                  break;
                }
              }
            }
            if (isSelect == true || isRet == true)
            { // treat it as if the null check was not there
              success_paths = labled_paths;
            }
            else
            {
              OP << "DEBUG: Unexpected!! FOI check should have exactly two successor or be used by Select/Ret Insn!\n";
              // exit(1);
              continue; // it may happen that FOI check is using BUG_ON, for now just ignoring
            }
          }
          else
          {
            auto BI = dyn_cast<BranchInst>(TI);
            if (BI && BI->isConditional())
            {
              Value *cond = BI->getCondition();
              if (DEBUG_PRINT)
                OP << *cond << "\n";
              if (auto CI = dyn_cast<ICmpInst>(cond))
              {
                auto pred = CI->getPredicate();
                if (DEBUG_PRINT)
                  OP << pred << "\n";
                if (unlikely_BB(TI->getParent()))
                {
                  foi_success = TI->getSuccessor(1); // wierd case of Unlikely!
                }

                else
                { // this is normal null condition check
                  if (pred == CmpInst::ICMP_EQ)
                  {
                    foi_success = TI->getSuccessor(1); //FOI success is on false side of condition
                  }
                  else if (pred == CmpInst::ICMP_NE)
                  {
                    foi_success = TI->getSuccessor(0); //FOI success is on true side of condition
                  }
                  else
                  {
                    OP << "UNHANDLED predicate!\n";
                    OP << pred << "\n";
                    exit(1);
                  }
                }
              }
              else
              {
                OP << "UNEXPEXTED: the condition is not icmp!\n";
                OP << *cond << "\n";
                // exit(1);
                continue; //go for next path
              }
            }
            else
            { //Sanity check
              OP << "UNEXPECTED: the terminator Insn should be conditional br!\n";
              OP << *TI << "\n";
              exit(0);
            }

            //now we have the success side for FOI
            for (auto memb : labled_paths)
            {
              auto path = get<0>(memb);
              if (find(path.begin(), path.end(), foi_success) != path.end())
              { //if path is going through foi success
                success_paths.push_back(memb);
              }
            }
          }
        }
        else
        { //there were no check on FOI, so all paths are considered success path
          success_paths = labled_paths;
        }

        if (DEBUG_PRINT)
          OP << "process success path\n";
        process_paths(success_paths, foi_value, foi_check, F); //do all of last use detection and flatteningn
      }
    }
    if (DEBUG_PRINT)
    {
      OP << "GOT all PATHS to FOI Flatten for:\n"
         << bc_file << "\n";
      OP << opcodeMap.size() << "\n";
      OP << opcodeMapRev.size() << "\n";
    }
    dump_flattenPaths(errFlattenPaths_to_foi, insnPathToCSMap, pathConditionMap, true);
    dump_flattenPaths(normalFlattenPaths_to_foi, insnPathToCSMap, pathConditionMap, false);
    dump_loopAndConditionalPaths(loopFlattenPaths_to_foi, conditionally_released_paths,
                                 escapingFlattenPaths_to_foi);
    dump_calleesFoiLastUse();

    errFlattenPaths_to_foi.clear();
    normalFlattenPaths_to_foi.clear();
    loopFlattenPaths_to_foi.clear();
    escapingFlattenPaths_to_foi.clear();
    conditionally_released_paths.clear();
    insnPathToCSMap.clear();
    pathConditionMap.clear();
    errPathLastCallCheckSide.clear();

    if (debug_run)
    {
      process_escaping_values();
      dump_flattenPaths(errFlattenPaths_to_foi, insnPathToCSMap, pathConditionMap, true, true);
      dump_flattenPaths(normalFlattenPaths_to_foi, insnPathToCSMap, pathConditionMap, false, true);
      dump_loopAndConditionalPaths(loopFlattenPaths_to_foi, conditionally_released_paths,
                                   escapingFlattenPaths_to_foi);
      dump_calleesFoiLastUse();

      std::ofstream OP_map_outFile;
      OP_map_outFile.open(FOI_DIR + "OP_Map_index.txt", std::ios::out);
      if (!OP_map_outFile.is_open())
      {
        OP << "Failed to open file:\n"
           << FOI_DIR + "OP_Map_index.txt\n";
        exit(1);
      }
      for (auto &mapPair : opcodeMapRev)
      {
        OP_map_outFile << mapPair.first << " " << mapPair.second << "\n";
      }
      OP_map_outFile.close();

      OP << "it's enough!\n";
      exit(0);
    }
  } // end of callSite string loop

  // process_escaping_values();

  dump_calleesFoiLastUse();

  std::ofstream OP_map_outFile;
  OP_map_outFile.open(FOI_DIR + "OP_Map_index.txt", std::ios::out);
  if (!OP_map_outFile.is_open())
  {
    OP << "Failed to open file:\n"
       << FOI_DIR + "OP_Map_index.txt\n";
    exit(1);
  }
  for (auto &mapPair : opcodeMapRev)
  {
    OP_map_outFile << mapPair.first << " " << mapPair.second << "\n";
  }
  OP_map_outFile.close();

  OP << "# of items: " << opcodeMap.size() << "\n";
  OP << "*********\n";
}

void init_output_files(void)
{
  std::ifstream foi_file;
  std::string line;

  char curr_path[4096];
  if (!getcwd(curr_path, 4096))
  {
    OP << "failed to get current dir\n";
    exit(1);
  }

  WRK_DIR.assign(curr_path);
  WRK_DIR += "/run/";

  foi_file.open(WRK_DIR + "foi.txt", std::ios::in);
  if (!foi_file.is_open())
  {
    OP << "Failed to open foi.txt\n"
       << WRK_DIR + "foi.txt\nUsing default FOI: kmalloc\n";
    FOI = "kmalloc";
  }
  else
  {
    std::getline(foi_file, line);
    std::istringstream iss(line);
    iss >> FOI;
    foi_file.close();
  }
  OP << "FOI is: " << FOI << "\n";

  FOI_DIR = WRK_DIR + FOI + "/";

  int dir_err = mkdir((FOI_DIR).c_str(), S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
  while (-1 == dir_err)
  {
    if (errno != EEXIST)
    {
      OP << "Error creating directory!\n"
         << (FOI_DIR) << "\n";
      exit(1);
    }
    OP << "Directory exists: " << (FOI_DIR) << "\nRemoving it!\n";
    system(("rm -rf " + FOI_DIR).c_str());
    dir_err = mkdir((FOI_DIR).c_str(), S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
  }
  OP << "Directory created: " << (FOI_DIR) << "\n";
}

map<Value *, set<Value *>> EqMap;
set<GetElementPtrInst *> skipGEPs;
map<string, pair<unsigned, unsigned>> visited; //funcName, timesVisited, timesChecked

//finds reachable BBs and respective distances from startingBB
set<BasicBlock *> findReachableBBs(BasicBlock *startingBB, map<BasicBlock *, uint32_t> *distanceMap)
{
  set<BasicBlock *> reachables;
  vector<pair<BasicBlock *, uint32_t>> workList;
  workList.push_back(make_pair(startingBB, 0));
  reachables.insert(startingBB);
  if (distanceMap)
    (*distanceMap)[startingBB] = 0;

  while (!workList.empty())
  {
    auto currentPair = workList.back();
    auto currentBB = currentPair.first;
    auto dist = currentPair.second;
    workList.pop_back();

    auto TI = currentBB->getTerminator();
    if (TI)
    {
      for (unsigned i = 0, NSucc = TI->getNumSuccessors(); i < NSucc; ++i)
      {
        auto succ = TI->getSuccessor(i);
        auto ret = reachables.insert(succ);
        if (ret.second == true)
        {
          workList.push_back(make_pair(succ, dist + 1));
          if (distanceMap)
            (*distanceMap)[succ] = dist + 1;
        }
      }
    }
  }
  return reachables;
}

bool pointerReturning(Function *F)
{
  if (F->getReturnType()->isPointerTy())
  {
    return true;
  }
  return false;
}

set<Value *> findEqGEP(GetElementPtrInst *inputGEP)
{
  if (EqMap.find(inputGEP) != EqMap.end())
  { // already found
    auto retSet = EqMap[inputGEP];
    return retSet;
  }

  set<Value *> EqGEPSet;
  set<Value *> baseEquals;
  set<Value *> idxEquals;

  EqGEPSet.insert(inputGEP); //equivalent to itself

  bool singleIndexed = false;
  if (inputGEP->getNumIndices() == 1)
  {
    if (DEBUG_PRINT)
      OP << "GEP with just 1 index!\n";
    singleIndexed = true;
  }

  auto ret = skipGEPs.insert(inputGEP);
  auto inputGEPit = ret.first;

  auto structBase = inputGEP->getOperand(0);
  auto baseIdx = inputGEP->getOperand(1);
  if (!singleIndexed)
  {
    auto idx = inputGEP->getOperand(2);
    if (EqMap.find(idx) != EqMap.end())
    {
      idxEquals = EqMap[idx];
    }
    else
    {
      visitedUses.clear();
      idxEquals = findEquivalents(idx);
    }
  }
  else
  {
    if (EqMap.find(baseIdx) != EqMap.end())
    {
      idxEquals = EqMap[baseIdx];
    }
    else
    {
      visitedUses.clear();
      idxEquals = findEquivalents(baseIdx);
    }
  }

  if (EqMap.find(structBase) != EqMap.end())
  {
    baseEquals = EqMap[structBase];
  }
  else
  {
    visitedUses.clear();
    baseEquals = findEquivalents(structBase);
  }
  if (DEBUG_PRINT)
  {
    OP << "EQ of base: " << *structBase << "\n";
    for (auto &v : baseEquals)
    {
      OP << *v << "\n";
    }
  }

  auto reachables = findReachableBBs(inputGEP->getParent()); //set of all BBs after this BB
  for (auto &baseEq : baseEquals)
  { //look for other uses of the base in other gep insn, and find equivalent gep
    auto bEqUsers = baseEq->users();
    for (const auto &bEqU : bEqUsers)
    {
      auto useVal = &(*bEqU);
      if (DEBUG_PRINT)
        OP << *useVal << "\n";
      if (!dyn_cast<Instruction>(useVal))
      {
        continue;
      }
      if (reachables.find(dyn_cast<Instruction>(useVal)->getParent()) == reachables.end())
      { // this use is not important
        continue;
      }
      auto eqGEP = dyn_cast<GetElementPtrInst>(useVal);
      if (eqGEP && eqGEP != inputGEP)
      {
        if (eqGEP->getNumIndices() != inputGEP->getNumIndices())
        {
          continue;
        }
        if (singleIndexed)
        {
          auto eqGEPidx = eqGEP->getOperand(1);
          if (idxEquals.find(eqGEPidx) != idxEquals.end())
          {
            EqGEPSet.insert(eqGEP);
          }
        }
        else
        { //double indexed GEP
          auto eqGEPidx = eqGEP->getOperand(2);
          if (idxEquals.find(eqGEPidx) != idxEquals.end())
          {
            EqGEPSet.insert(eqGEP);
          }
        }
      }
    }
  }
  skipGEPs.erase(inputGEPit); //keep track of processing GEP
  EqMap[inputGEP] = EqGEPSet;
  return EqGEPSet;
}

bool dontFollowFuncs(string fn)
{
  if (fn.find("llvm") != string::npos || fn.find("warn") != string::npos || fn.find("print") != string::npos ||
      releaseTerminals.find(fn) != releaseTerminals.end() || fn.find("irq") != string::npos ||
      fn.find("kfree") != string::npos || fn == "iput" || fn == "kref_put" || fn.find("unref") != string::npos || fn.find("list_add") != string::npos ||
      fn.find("write_once") != string::npos || fn.find("memcpy") != string::npos)
  {

    return true;
  }
  return false;
}

//options:
// useFollow: is this value a use? if yes, the direction of explore is different from non-use vals
Value *findValueFlow(Value *val, bool useFollow = true, Value *orgVal = NULL)
{
#ifndef DEBUG_PRINT
  // DEBUG_PRINT = false;
#endif

  auto insn = dyn_cast<Instruction>(val);
  if (!insn)
  {
    if (DEBUG_PRINT)
      OP << "Val is not an insn.\n";
    return val;
  }
  if (DEBUG_PRINT)
    OP << *insn << "\n";
  // debug_dump_insn_operands(insn);
  auto SI = dyn_cast<StoreInst>(val);
  if (SI)
  {
    if (useFollow == true)
      return SI->getPointerOperand();
    else
    {
      return SI->getOperand(0);
    }
  }

  auto LI = dyn_cast<LoadInst>(val);
  if (LI)
  { // record the dst of load
    if (useFollow == true)
    {
      return LI;
    }
    else
    {
      return LI->getOperand(0);
    }
  }
  auto BI = dyn_cast<BitCastInst>(val);
  if (BI)
  { // record the result
    if (useFollow == true)
    {
      return BI;
    }
    else
    {
      return BI->getOperand(0);
    }
  }
  auto PI = dyn_cast<PtrToIntInst>(val);
  if (PI)
  {
    if (useFollow == true)
    {
      return PI;
    }
    else
    {
      return PI->getOperand(0);
    }
  }
  auto ZeI = dyn_cast<ZExtInst>(val);
  if (ZeI)
  {
    if (useFollow == true)
    {
      return ZeI;
    }
    else
    {
      return ZeI->getOperand(0);
    }
  }
  auto SeI = dyn_cast<SExtInst>(val);
  if (SeI)
  {
    if (useFollow == true)
    {
      return SeI;
    }
    else
    {
      return SeI->getOperand(0);
    }
  }

  auto phiN = dyn_cast<PHINode>(val);
  if (phiN)
  {
    if (useFollow == true)
      return phiN;
    else
    {
      if (DEBUG_PRINT)
        OP << "ATTENTION: reached Phi Node, and here we may miss some dependencies!\n";
      return phiN->getOperand(0);
    }
  }

  auto CI = dyn_cast<CallInst>(val);
  if (CI)
  {
    callDepth++;
    if (DEBUG_PRINT)
      OP << *CI << "\n";
    auto caller = CI->getParent()->getParent();
    auto callerN = caller->getName().str();
    auto callee = getCallee(CI);
    if (callee)
    {
      string clName = callee->getName().str();
      if (DEBUG_PRINT)
        OP << callerN << " --> " << clName << "\n";

      if (useFollow == false && orgVal != NULL && !dontFollowFuncs(clName) && callDepth < 5)
      {
        if (DEBUG_PRINT)
          debug_dump_insn_operands((Instruction *)CI);
        int orgValIdx = -1;
        for (int i = 0; i < CI->getNumOperands() - 1; ++i)
        { //the last operand in callInsn is callee func
          if (orgVal == CI->getOperand(i))
          {
            orgValIdx = i;
            break;
          }
        }

        if (callee->isDeclaration())
        { //need to load func in another module
          if (funcDefinitionMap.find(clName) != funcDefinitionMap.end())
          {
            auto defIdx = funcDefinitionMap[clName];
            string bcFile = bcFileMap[defIdx];
            Module *newMod;
            if (alreadyLoadedModules.find(bcFile) == alreadyLoadedModules.end())
            {
              LLVMContext *LLVMCtx = new LLVMContext();
              newMod = load_module(bcFile, *LLVMCtx);
              alreadyLoadedModules[bcFile] = newMod;
            }
            else
            {
              newMod = alreadyLoadedModules[bcFile];
            }
            if (newMod)
              for (auto &F : *newMod)
              {
                auto fName = F.getName();
                if (fName.startswith("llvm.") || F.isDeclaration())
                  continue;
                if (fName == clName)
                {
                  callee = &F;
                  break;
                }
              }
          }
          else
          {
            if (DEBUG_PRINT)
              OP << "callee has no definition in our bc files! " << clName << "\n";
          }
        }

        if (!is_val_func(*callee) && orgValIdx != -1)
        {
          Value *inCalleeVal = NULL;
          map<Value *, int> otherArgsIdx;

          int idx = -1;
          for (auto &arg : callee->args())
          {
            auto currArg = dyn_cast<Value>(&arg);
            idx++;
            if (idx == orgValIdx)
              inCalleeVal = currArg;
            else
              otherArgsIdx[currArg] = idx;
          }
          if (DEBUG_PRINT)
            OP << *inCalleeVal << "\n";

          visitedUses.clear();
          auto inCalleeEqs = findEquivalents(inCalleeVal, true, NULL, true);
          for (auto &eq : inCalleeEqs)
          {
            if (DEBUG_PRINT)
              OP << *eq << "\n";
            if (otherArgsIdx.find(eq) != otherArgsIdx.end())
            {
              if (DEBUG_PRINT)
                OP << *eq << "\n";
              callDepth--;
              return CI->getOperand(otherArgsIdx[eq]); //one of args where equal to the orgVal
            }
          }
        }
      }

      if (callee->arg_size() == 1)
      { //takes strickly one parameter
        //AND: that parameter is a global or arg of caller:
        auto calleeParam = CI->getOperand(0);
        Function *caller = CI->getParent()->getParent();
        GlobalVariable *glbVar = dyn_cast<GlobalVariable>(calleeParam);
        bool isCallerArg = false;

        if (!glbVar)
        { //check if it is a caller-arg
          auto srcVals = findValueSources(calleeParam, true);
          for (auto &eq : srcVals)
          {
            if (DEBUG_PRINT)
              OP << *eq << "\n";
            for (auto &argI : caller->args())
            {
              Value *arg = &argI;
              if (DEBUG_PRINT)
                OP << *arg << "\n";
              if (eq == arg)
              {
                isCallerArg = true;
                break;
              }
            }
            if (isCallerArg)
              break;
          }
        }

        if (glbVar || isCallerArg)
        { //now I can assume it is escaping
          if (useFollow == true && calleeParam == orgVal)
            return CI;
          if (useFollow == false)
          { //looking for source
            if (DEBUG_PRINT)
              OP << "propagate via 1-arg func: " << clName << "\n";
            callDepth--;
            return calleeParam;
          }
        }
      }
    }
    callDepth--;
  }

  auto GEP = dyn_cast<GetElementPtrInst>(val);
  if (GEP)
  {
    if (GEP->getNumIndices() != 2)
    {
      if (DEBUG_PRINT)
        OP << "GEP with 1 index!\n";
      if (useFollow)
        return GEP;
      return GEP->getOperand(0);
    }
    auto structBase = GEP->getOperand(0);
    auto baseIdx = GEP->getOperand(1);
    auto idx = GEP->getOperand(2);

    auto baseConst = dyn_cast<ConstantInt>(baseIdx);
    if (baseConst)
    {
      if (baseConst->getValue() != 0)
      {
        OP << "non-zero base for GEP!!\n";
        OP << "TODO: take care of it: " << *GEP << "\n";
        return NULL;
      }
    }
    else
    {
      OP << "baseIdx is not constInt: " << *baseIdx << "\n";
      OP << "TODO: take care of it: " << *GEP << "\n";
      return NULL;
    }

    if (useFollow)
    {
      return GEP;
    }
    return structBase;
  }
#ifndef DEBUG_PRINT
// DEBUG_PRINT = true;
#endif

  if (DEBUG_PRINT)
    OP << "SHOULD cover more insn?! here:\n"
       << insn->getOpcodeName() << "\n";
  return NULL;
}

bool val_preceeds(Value *start, Value *end)
{
  if (DEBUG_PRINT)
    OP << *start << "\n"
       << *end << "\n";

  auto stInsn = dyn_cast<Instruction>(start);
  auto enInsn = dyn_cast<Instruction>(end);
  if (!stInsn || !enInsn)
    return false;

  auto startBB = stInsn->getParent();
  auto startReachables = findReachableBBs(startBB);
  auto endBB = enInsn->getParent();
  auto endReachables = findReachableBBs(endBB);

  if (startBB == endBB)
  { // both Vals in same BB
    for (Instruction &Insn : *startBB)
    {
      if ((Value *)&Insn == start)
        return true;
      if ((Value *)&Insn == end)
        return false;
    }
  }

  if (endReachables.find(startBB) == endReachables.end() && //end cannot reach the start
      startReachables.find(endBB) != startReachables.end())
  { //start reaches the end
    return true;
  }

  return false;
}

//just go the direction of finding sources of a value
set<Value *> findValueSources(Value *target, bool loosen_gep)
{
  if (DEBUG_PRINT)
    OP << "find SRC of:\n"
       << *target << "\n";
  set<Value *> SrcSet;

  SrcSet.insert(target); //traget is equal to itself

  auto targetI = dyn_cast<Instruction>(target);
  if (!targetI)
  { // not an insn like global
    return SrcSet;
  }
  vector<Value *> work_list;
  auto targetBB = dyn_cast<Instruction>(target)->getParent();
  auto targetReachables = findReachableBBs(targetBB);

  work_list.push_back(target); //to cover targets like load insn

  while (!work_list.empty())
  {
    auto insnVal = work_list.back();
    work_list.pop_back();

    if (DEBUG_PRINT)
      OP << "work on " << *insnVal << "\n";

    auto GEP = dyn_cast<GetElementPtrInst>(insnVal);
    if (GEP)
    {
      if (DEBUG_PRINT)
        OP << "working on GEP\n";
      if (loosen_gep)
      {
        Value *baseStruct = GEP->getOperand(0);
        if (DEBUG_PRINT)
          OP << *baseStruct << "\n";
        auto ret = SrcSet.insert(baseStruct);
        if (ret.second == true)
        { //insert was successful
          work_list.push_back(baseStruct);
        }
      }
      else
      { //normal handling of GEP
        auto eqGEPs = findEqGEP(GEP);
        for (auto &eq : eqGEPs)
        {
          auto ret = SrcSet.insert(eq);
          if (ret.second == true)
          { //insert was successful
            work_list.push_back(eq);
          }
        }
      }
    }
    else
    { // not GEP

      auto FV = findValueFlow(insnVal, false); //flase: is not use-follow
      if (FV)
      {
        if (DEBUG_PRINT)
          OP << *FV << "\n";
        auto ret = SrcSet.insert(FV);
        if (ret.second == true)
        { //insert was successful
          work_list.push_back(FV);
        }
      }
    }

    auto Users = insnVal->users();
    for (const auto &UV : Users)
    {
      auto useVal = &(*UV);
      if (DEBUG_PRINT)
        OP << *useVal << " user of " << *insnVal << "\n";

      Instruction *useInsn = dyn_cast<Instruction>(useVal);
      if (!useInsn)
      {
        continue;
      }

      if (useInsn->getParent()->getParent() != targetBB->getParent())
        continue;
      if (val_preceeds(useVal, target) && visitedUses.find(useVal) == visitedUses.end())
      {
        auto UF = findValueFlow(useVal, false, insnVal); //look for sources of useVal
        if (UF)
        {
          if (DEBUG_PRINT)
            OP << *UF << "\n";
          auto ret = SrcSet.insert(UF);
          if (ret.second == true)
          { //insert was successful
            work_list.push_back(UF);
          }
        }
      }
    }
  }

  return SrcSet;
}

bool is_call_succesful(Instruction *CI, const vector<BasicBlock *> *path)
{
  Value *callVal = (Value *)CI;
  BasicBlock *successSide = NULL;

  if (DEBUG_PRINT)
    OP << *CI << "\n";
  auto callee = getCalleeVal((CallInst *)CI);
  if (callee && callee->getReturnType()->isVoidTy())
    return true; //if callee is void returning, there won't be any failure check on it

  visitedUses.clear();                         //necessary
  auto cvEqs = findEquivalents(callVal, true); //, path);
  auto zeroCheck = findZeroCheckInsn(callVal, cvEqs);

  if (!zeroCheck)
    return true; //the call return val is not checked: we assume it succeeded

  if (DEBUG_PRINT)
    OP << *zeroCheck << "\n";

  auto TI = zeroCheck->getParent()->getTerminator();
  if (!TI)
    return true;

  if (DEBUG_PRINT)
    OP << *TI << "\n";

  if (TI->getNumSuccessors() < 2)
    return true; //ignore unconditional br

  auto compI = dyn_cast<ICmpInst>(zeroCheck);
  if (!compI)
    return true; //impossible!

  auto pred = compI->getPredicate();
  if (pred == CmpInst::ICMP_EQ)
  {
    successSide = TI->getSuccessor(0); //success is on true side of condition
  }
  else if (pred == CmpInst::ICMP_NE)
  {
    successSide = TI->getSuccessor(1); //success is on false side of condition
  }
  else if (pred == CmpInst::ICMP_SLT)
  {
    successSide = TI->getSuccessor(1); //success is on false side of condition
  }
  else if (pred == CmpInst::ICMP_SGT)
  {
    successSide = TI->getSuccessor(0); //success is on true side of condition; NEVER encountered!
  }
  //check for the side on the path
  if (successSide && find(path->begin(), path->end(), successSide) == path->end())
    return false;
  return true;
}

//find any equivalent values to target
//loosen_gep (default false): if should treat GEP loosly or not (default is false)
//path (default NULL): the path that we are interested to find equivalents on; useful for escape analysis and last foi use
//isFuncArg: special treatment for funcArg equivalents finding
set<Value *> findEquivalents(Value *target, bool loosen_gep, const vector<BasicBlock *> *path, bool isFuncArg)
{
#ifndef DEBUG_PRINT
  DEBUG_PRINT = false;
#endif
  if (DEBUG_PRINT)
    OP << "find EQ of:\n"
       << *target << "\n";
  set<Value *> EqSet;
  set<BasicBlock *> pathSet;

  EqSet.insert(target); //traget is equal to itself
  if (path)
  { //this is path sensitive
    for (auto &bb : *path)
      pathSet.insert(bb);
  }

  if (!target || isConstant(target))
    return EqSet;
  auto targetI = dyn_cast<Instruction>(target);
  if (!targetI)
  { // not an insn like global or func arg
    //  should be able to continue!
    auto tUsers = target->users();
    auto firstU = tUsers.begin();
    if (firstU == tUsers.end()) //if there were no use!
      return EqSet;

    auto firstUval = dyn_cast<Value>(*firstU);
    target = findValueFlow(firstUval, true, target); //track the use-follow from target
    if (!target)
    {
      return EqSet;
    }
    EqSet.insert(target); //the first use is eq to the arg (initial target)
    if (DEBUG_PRINT)
      OP << "working on first use: " << *target << "\n";
  }
  vector<Value *> work_list;
  auto targetBB = dyn_cast<Instruction>(target)->getParent();
  auto targetReachables = findReachableBBs(targetBB);

  work_list.push_back(target); //to cover targets like load insn

  while (!work_list.empty())
  {
    auto insnVal = work_list.back();
    work_list.pop_back();

    if (path != NULL)
    { //this is a path specific equivalency search
      if (DEBUG_PRINT)
        OP << *insnVal << "\n";
      auto insn = dyn_cast<Instruction>(insnVal);
      if (insn)
      {
        auto currBB = insn->getParent();
        if (pathSet.find(currBB) == pathSet.end())
        {
          EqSet.erase(insnVal); //was already added to the set
          continue;
        }
      }
    }
    if (DEBUG_PRINT)
      OP << "work on " << *insnVal << "\n";

    auto GEP = dyn_cast<GetElementPtrInst>(insnVal);
    if (GEP)
    { //needs special treatment for GEP:
      if (skipGEPs.find(GEP) != skipGEPs.end())
      {
        continue;
      }
      if (DEBUG_PRINT)
        OP << "working on GEP\n";
      if (loosen_gep)
      {
        Value *baseStruct = GEP->getOperand(0);
        if (DEBUG_PRINT)
          OP << *baseStruct << "\n";
        auto ret = EqSet.insert(baseStruct);
        if (ret.second == true)
        { //insert was successful
          equivalenceCausalMap[baseStruct] = GEP;
          work_list.push_back(baseStruct);
        }
      }
      else
      { //normal handling of GEP
        auto eqGEPs = findEqGEP(GEP);
        for (auto &eq : eqGEPs)
        {
          auto ret = EqSet.insert(eq);
          if (ret.second == true)
          { //insert was successful
            equivalenceCausalMap[eq] = GEP;
            work_list.push_back(eq);
          }
        }
      }
    }
    else
    { // not GEP

      auto FV = findValueFlow(insnVal, false);
      if (FV)
      {
        if (DEBUG_PRINT)
          OP << *FV << "\n";
        auto ret = EqSet.insert(FV);
        if (ret.second == true)
        { //insert was successful
          equivalenceCausalMap[FV] = dyn_cast<Instruction>(insnVal);
          work_list.push_back(FV);
        }
      }
    }

    auto Users = insnVal->users();
    bool stored_intoVal = false;
    for (const auto &UV : Users)
    {
      auto useVal = &(*UV);
      if (DEBUG_PRINT)
        OP << *useVal << " user of " << *insnVal << "\n";

      if (visitedUses.find(useVal) != visitedUses.end())
        continue;
      visitedUses.insert(useVal);

      Instruction *useInsn = dyn_cast<Instruction>(useVal);
      if (!useInsn)
      {
        continue;
      }
      auto SI = dyn_cast<StoreInst>(useVal); //used for filtering shadowed stores

      if (path != NULL)
      { //this is a path specific equivalency search
        if (DEBUG_PRINT)
          OP << *useInsn << "\n";
        auto currBB = useInsn->getParent();
        if (pathSet.find(currBB) == pathSet.end())
        {
          continue;
        }
      }

      if (useInsn->getParent()->getParent() != targetBB->getParent())
        continue;
      if (!SI || !stored_intoVal)
      {
        auto UF = findValueFlow(useVal, false, insnVal); //look for sources of useVal
        if (UF)
        {
          if (DEBUG_PRINT)
            OP << *UF << "\n";
          auto ret = EqSet.insert(UF);
          if (ret.second == true)
          { //insert was successful
            equivalenceCausalMap[UF] = useInsn;
            work_list.push_back(UF);
          }
        }
      }
      if (SI)
      {
        if (SI->getPointerOperand() == insnVal)
          stored_intoVal = true;
      }
      //////////////

      auto UF = findValueFlow(useVal, true, insnVal);
      if (UF)
      {
        if (DEBUG_PRINT)
          OP << *UF << "\n";
        auto ret = EqSet.insert(UF);
        if (ret.second == true)
        { //insert was successful
          equivalenceCausalMap[UF] = useInsn;
          work_list.push_back(UF);
        }
      }
    }
  }
#ifndef DEBUG_PRINT
  // DEBUG_PRINT = true;
#endif
  EqMap[target] = EqSet; //update the global map of equivalences
  return EqSet;
}

//checks if the V is a pointer to poniter type
bool isPointerToPointer(const Value *V)
{
  if (DEBUG_PRINT)
    OP << *V << "\n";
  const Type *T = V->getType();
  return T->isPointerTy() && T->getContainedType(0)->isPointerTy();
}

// look for nullCheck and dereferences
bool findNullCheckOrDeref(string name, set<Value *> eqSet, bool *isDerefed, vector<Instruction *> *derefInsns)
{
  bool isNullChecked = false;
  *isDerefed = false;
  for (auto &eqVal : eqSet)
  {
    if (DEBUG_PRINT)
    {
      OP << *eqVal << "\n";
    }
    auto users = ((Value *)eqVal)->users();
    if (isNullChecked == true)
    { //one null check is enough in the caller!
      break;
    }
    for (const auto &UI : users)
    { // UI: usrs iterator
      Value *useVal = &(*UI);
      if (DEBUG_PRINT)
        OP << *useVal << "\n";
      auto cmpInsn = dyn_cast<ICmpInst>(useVal);
      if (cmpInsn)
      {
        Value *compareTo;
        if (cmpInsn->getOperand(0) == eqVal)
        {
          compareTo = cmpInsn->getOperand(1);
        }
        else if (cmpInsn->getOperand(1) == eqVal)
        {
          compareTo = cmpInsn->getOperand(0);
        }
        else
        {
          OP << "Imposible happened!! compare insn is not comparing call insn!\n";
          exit(1);
        }
        ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(compareTo);
        if (CPN)
        {
          if (DEBUG_PRINT)
            OP << name << "\n";
          if (visited.find(name) == visited.end())
          {
            OP << "IMPOSIBLE Happened! checked while not visited before?!\n";
            exit(1);
          }
          else
          {
            visited[name].second += 1;
            isNullChecked = true;
          }
        }
      }
      auto loadInsn = dyn_cast<LoadInst>(useVal);
      if (loadInsn)
      {
        Value *ptrVal = loadInsn->getPointerOperand();
        if (!isPointerToPointer(ptrVal))
        {
          if (eqVal == ptrVal)
          {
            *isDerefed = true;
            derefInsns->push_back(loadInsn);
          }
        }
      }
      auto storeInsn = dyn_cast<StoreInst>(useVal);
      if (storeInsn)
      { // compare to the store dst (not pointer to pointer)
        Value *ptrVal = storeInsn->getPointerOperand();
        if (!isPointerToPointer(ptrVal))
        {
          if (eqVal == ptrVal)
          {
            *isDerefed = true;
            derefInsns->push_back(storeInsn);
          }
        }
      }
      auto gepInsn = dyn_cast<GetElementPtrInst>(useVal);
      if (gepInsn)
      {
        Value *basePtr = gepInsn->getOperand(0);
        if (eqVal == basePtr)
        { // being used as base struct pointer
          *isDerefed = true;
          derefInsns->push_back(gepInsn);
        }
      }
    }
  } // end of nullCheck find
  return isNullChecked;
}

bool isGetter(string caller, string currGetter, Module *newM)
{
  for (auto &F : *newM)
  {
    if (F.getName() != caller || F.isDeclaration())
      continue;

    for (auto &BB : F)
    {
      for (auto &I : BB)
      {
        if (auto CI = dyn_cast<CallInst>(&I))
        {
          if (auto callee = getCallee(CI))
          {
            if (callee->getName() == currGetter)
            {
              auto cEq = findEquivalents(CI, true);
              for (auto &eq : cEq)
              {
                auto eqUsers = eq->users();
                for (auto eqU : eqUsers)
                  if (auto retI = dyn_cast<ReturnInst>(eqU))
                  {
                    return true;
                  }
              }
            }
          }
        }
      }
    }
  }
  return false;
}

pair<Instruction *, int> look_for_init(CallInst *callInsn, set<Value *> equals)
{
  Value *initInsn = NULL;

  uint32_t cutoff = MAX_VAL;
  // pair<Instruction *, uint32_t> closestLoad, closestStore;
  auto closestLoad = make_pair((Instruction *)NULL, MAX_VAL);
  auto closestStore = make_pair((Instruction *)NULL, MAX_VAL);

  uint32_t currentDistance = MAX_VAL; //some intitial large unsigned
  map<BasicBlock *, uint32_t> distanceMap;
  auto foiReachableBBs = findReachableBBs(callInsn->getParent(), &distanceMap);
  //look into equals one by one and find the closest deref to callInsn
  for (auto &eq : equals)
  {
    Value *eqVal = &(*eq);
    auto eqUsers = eqVal->users();
    for (const auto &eqU : eqUsers)
    {
      Value *useVal = &(*eqU);
      if (val_preceeds(useVal, (Value *)callInsn))
        continue; //not interested in uses before the call
      if (DEBUG_PRINT)
        OP << *useVal << "\n";
      if (auto ldInsn = dyn_cast<LoadInst>(useVal))
      { //if it is load
        auto ldBB = ldInsn->getParent();
        auto ptrVal = ldInsn->getPointerOperand();
        if (!isPointerToPointer(ptrVal) && ptrVal == eqVal && distanceMap[ldBB] < closestLoad.second)
        {
          closestLoad = make_pair(dyn_cast<Instruction>(ldInsn), distanceMap[ldBB]);
        }
      }
      else if (auto stInsn = dyn_cast<StoreInst>(useVal))
      { // if it is store
        auto stBB = stInsn->getParent();
        auto ptrVal = stInsn->getPointerOperand();
        if (!isPointerToPointer(ptrVal) && ptrVal == eqVal && distanceMap[stBB] < closestStore.second)
        {
          closestStore = make_pair(dyn_cast<Instruction>(stInsn), distanceMap[stBB]);
        }
      }
      else if (auto callInsn = dyn_cast<CallInst>(useVal))
      { // if is call to memcpy
        if (auto callee = getCallee(callInsn))
        {
          if (callee->getName() == "__memcpy")
          {
            if (callInsn->getOperand(0) == eqVal)
            { // is dest of memcpy
              auto callBB = callInsn->getParent();
              if (distanceMap[callBB] < closestStore.second)
              {
                closestStore = make_pair(dyn_cast<Instruction>(callInsn), distanceMap[callBB]);
              }
            }
          }
          else
          {
            auto callBB = callInsn->getParent();
            if (cutoff > distanceMap[callBB])
              cutoff = distanceMap[callBB];
          }
        }
      }
    }
  }

  //now check if it was initialized or not
  if (closestLoad.second > closestStore.second && closestStore.second < cutoff)
    return make_pair(closestStore.first, 1);
  else if (closestLoad.second < closestStore.second && closestLoad.second < cutoff)
    return make_pair(closestLoad.first, 0);

  return make_pair((Instruction *)NULL, -1);
}

bool is_null_checking(Instruction *I, Value *V)
{
  auto cmpInsn = dyn_cast<ICmpInst>(I);
  if (cmpInsn)
  {
    // debug_dump_insn_operands(dyn_cast<Instruction>(cmpInsn));
    Value *compareTo;
    if (cmpInsn->getOperand(0) == V)
    {
      compareTo = cmpInsn->getOperand(1);
    }
    else if (cmpInsn->getOperand(1) == V)
    {
      compareTo = cmpInsn->getOperand(0);
    }
    else
    {
      OP << "Imposible happened!! compare insn is not comparing call insn!\n";
      exit(1);
    }
    ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(compareTo);
    if (CPN)
    {
      return true;
    }
  }
  return false;
}

bool is_initializing(Instruction *I, Value *V)
{
  if (auto stInsn = dyn_cast<StoreInst>(I))
  { // if it is store
    auto ptrVal = stInsn->getPointerOperand();
    if (!isPointerToPointer(ptrVal) && ptrVal == V)
    {
      return true;
    }
  }
  if (auto callInsn = dyn_cast<CallInst>(I))
  { // if is call to memcpy
    if (auto callee = getCallee(callInsn))
    {
      if (callee->getName() == "__memcpy")
      {
        if (callInsn->getOperand(0) == V) // is dest of memcpy
          return true;
      }
    }
  }

  return false;
}

bool is_readingFrom(Instruction *I, Value *V)
{
  if (auto ldInsn = dyn_cast<LoadInst>(I))
  { //if it is load
    auto ptrVal = ldInsn->getPointerOperand();
    if (!isPointerToPointer(ptrVal) && ptrVal == V)
    {
      return true;
    }
  }
  return false;
}
//this function acts like findEquivalents, but considers the sequence of insns as well
void track_uses(Instruction *callInsn, string calleeName, map<string, int> &nullCheckedFuncs,
                map<string, vector<Instruction *>> &initializedCall, map<string, vector<Instruction *>> &readFromCall,
                map<string, vector<Instruction *>> &isErrFuncs)
{
  struct qElem
  {
    BasicBlock *BB;
    set<Value *> eqVals;
  };
  set<BasicBlock *> visitedBBs;
  bool nullCheck = false;
  queue<qElem> myQueue;
  qElem initElem;
  initElem.BB = callInsn->getParent();
  initElem.eqVals.insert((Value *)callInsn);

  myQueue.push(initElem);

  while (!myQueue.empty())
  {
    auto currElem = myQueue.front();
    auto currBB = currElem.BB;
    auto currEqs = currElem.eqVals;

    myQueue.pop();
    for (auto &I : *currBB)
    {
      if (DEBUG_PRINT)
        OP << I << "\n";
      Value *voi = NULL;
      for (unsigned i = 0, opNum = I.getNumOperands(); i < opNum; ++i)
      {
        Value *currOp = I.getOperand(i);
        if (currEqs.find(currOp) != currEqs.end())
        { //this I is using an Eq
          voi = currOp;
          break;
        }
      }
      if (!voi)
        continue;

      if (auto CI = dyn_cast<CallInst>(&I))
      {
        if (auto callee = getCallee(CI))
        {
          if (callee->getName() == "IS_ERR")
          {
            if (DEBUG_PRINT)
              OP << *CI << "\n";
            isErrFuncs[calleeName].push_back(&I);
          }
        };
      }
      if (!nullCheck && is_null_checking(&I, voi))
      {
        if (DEBUG_PRINT)
          OP << I << "\n";
        nullCheck = true;
        nullCheckedFuncs[calleeName] += 1;
      }
      else if (is_initializing(&I, voi))
      {
        if (DEBUG_PRINT)
          OP << I << "\n";
        initializedCall[calleeName].push_back(&I);
        return;
      }
      else if (is_readingFrom(&I, voi))
      {
        if (DEBUG_PRINT)
          OP << I << "\n";
        readFromCall[calleeName].push_back(&I);
        return;
      }
      else if (auto vf = findValueFlow((Value *)&I, true))
      { //finds new eqs based on current I
        if (DEBUG_PRINT)
          OP << *vf << "\n";
        auto ret = currEqs.insert(vf);
        while (ret.second == true)
        { //trace all equivalents hierarchy
          vf = findValueFlow(vf, false);
          if (!vf)
            break;
          if (DEBUG_PRINT)
            OP << *vf << "\n";
          ret = currEqs.insert(vf);
        }
      }
    }
    //prepare new qElem and add to myQ
    if (DEBUG_PRINT)
      OP << "------------\n";
    auto TI = currBB->getTerminator();
    for (unsigned i = 0, NSucc = TI->getNumSuccessors(); i < NSucc; ++i)
    {
      auto succBB = TI->getSuccessor(i);
      if (visitedBBs.find(succBB) != visitedBBs.end())
        continue;
      visitedBBs.insert(succBB);
      set<Value *> copiedEqs(currEqs);
      qElem newElem;
      newElem.BB = succBB;
      newElem.eqVals = copiedEqs;
      myQueue.push(newElem);
    }
  }

  return;
}

void collectGetterFuncs(void)
{
  set<string> getterFuncsSet;
  string bc_list = WRK_DIR + "bc.list";

  ifstream bc_files;
  bc_files.open(bc_list, ios::in);
  if (!bc_files.is_open())
  {
    OP << "Failed to open file:\n"
       << bc_list << "\n";
    exit(1);
  }
  string line;

  unsigned i = 1;
  while (getline(bc_files, line))
  { // for each .bc file
    OP << i++ << "- Processing bitcode:\n"
       << line << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    auto M = load_module(line, *LLVMCtx);
    alreadyLoadedModules[line] = M;
    if(M)
    for (auto &F : *M)
    {
      set<Value *> arg_list;
      bool isFgetter = false;
      bool isFptrRet = pointerReturning(&F);
      for (Argument &arg : F.args())
      {
        arg_list.insert((Value *)(&arg));
      }
      for (auto &BB : F)
      { //look for getter
        for (auto &I : BB)
        {
          auto retInsn = dyn_cast<ReturnInst>(&I);
          if (retInsn && isFptrRet && !isFgetter)
          {
            auto retVal = retInsn->getReturnValue();
            auto retSrcs = findValueSources(retVal, true);
            for (auto arg : arg_list)
            {
              if (arg->getType()->isPointerTy())
              { // sanity check: work on pointer args
                if (retSrcs.find(arg) != retSrcs.end())
                {
                  isFgetter = true;
                  break;
                }
              }
            }
          }
        }
      }
      if (isFptrRet && isFgetter)
        getterFuncsSet.insert(F.getName());
    }

  } //initial getters are collected

  vector<string> getterWorkingList;
  for (auto g : getterFuncsSet)
  {
    getterWorkingList.push_back(g);
  }

  while (!getterWorkingList.empty())
  {
    auto currG = getterWorkingList.back();
    getterWorkingList.pop_back();

    if (DEBUG_PRINT)
    {
      if (currG != "dev_get_drvdata")
        continue;
    }

    auto callers = callersMap[currG];
    for (auto &cl : callers)
    {

      if (DEBUG_PRINT)
      {
        if (cl != "get_gadget_data")
          continue;
      }
      if (getterFuncsSet.find(cl) != getterFuncsSet.end())
        continue;

      auto bcIdx = funcDefinitionMap[cl];
      auto bc_name = bcFileMap[bcIdx];
      Module *newM;
      if (alreadyLoadedModules.find(bc_name) == alreadyLoadedModules.end())
      {
        LLVMContext *LLVMCtx = new LLVMContext();
        newM = load_module(bc_name, *LLVMCtx);
        alreadyLoadedModules[bc_name] = newM;
      }
      else
        newM = alreadyLoadedModules[bc_name];

      if (isGetter(cl, currG, newM))
      {
        getterFuncsSet.insert(cl); //this is not previously found
        getterWorkingList.push_back(cl);
      }
    }
  }

  ofstream getterFuncFile;
  getterFuncFile.open(WRK_DIR + "getterFuncs.txt", ios::out);
  for (auto &gt : getterFuncsSet)
  {
    getterFuncFile << gt << "\n";
  }
  getterFuncFile.close();
}

//find potential FOIs:
// 3 conditions to be met:
// 1) pointer-returning
// 2) number of null-checks in callers should be above a threshold (like 50%)
// 3) the returned pointer is initialized then used (via store insn)
void findPotentialFOIs(void)
{
  load_funcsDefMaps();                               //to load callersMap
  map<string, int> visitedPtrFuncs, nullChekedFuncs; //set of ptr returning functions with their calls site info
  map<string, vector<Instruction *>> initializedCall, readFromCall, isErrFuncs;
  set<string> potentialFOIsSet;
  set<string> getterFuncsSet;
  string bc_list = WRK_DIR + "bc.list";

  ofstream potentialFOIsFile;
  potentialFOIsFile.open(WRK_DIR + "potentialFOIs.txt", ios::out);
  ofstream initLocationsFile;
  initLocationsFile.open(WRK_DIR + "initLocations.txt", ios::out);
  ofstream readLocationsFile;
  readLocationsFile.open(WRK_DIR + "readLocations.txt", ios::out);

  ofstream isErrLocationsFile;
  isErrLocationsFile.open(WRK_DIR + "isErrLocations.txt", ios::out);

  ifstream bc_files;
  bc_files.open(bc_list, ios::in);
  if (!bc_files.is_open())
  {
    OP << "Failed to open foi.txt\n"
       << bc_list << "\n";
    exit(1);
  }
  string line;

  unsigned i = 1;
  while (getline(bc_files, line))
  { // for each .bc file
    OP << i++ << "- Processing bitcode:\n"
       << line << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    auto M = load_module(line, *LLVMCtx);
    alreadyLoadedModules[line] = M;

    ifstream gettersFile;
    gettersFile.open(WRK_DIR + "getterFuncs.txt");
    if (!gettersFile.is_open())
    {
      OP << "Failed to open foi.txt\n"
         << WRK_DIR + "getterFuncs.txt\n";
      exit(1);
    }
    while (getline(gettersFile, line))
    {
      getterFuncsSet.insert(line);
    }
    OP << "TOTAL Getter Funcs found: " << getterFuncsSet.size() << "\n";

    for (auto elem : alreadyLoadedModules)
    {
      Module *M = elem.second;
      for (auto &F : *M)
      {
        if (F.isDeclaration() || F.getName().startswith("llvm"))
          continue;
        set<Value *> arg_list;
        bool isFgetter = false;
        if (getterFuncsSet.find(F.getName()) != getterFuncsSet.end())
          isFgetter = true;
        bool isFptrRet = pointerReturning(&F);
        for (Argument &arg : F.args())
        {
          arg_list.insert((Value *)(&arg));
        }

        for (auto &BB : F)
        { //look for callees to count null-checks
          for (auto &I : BB)
          {
            auto callInsn = dyn_cast<CallInst>(&I);
            if (callInsn)
            {
              auto callee = getCallee(callInsn);
              if (callee && pointerReturning(callee))
              {
                if (callee->getName().startswith("llvm"))
                  continue;
                string name = callee->getName().str();
                //////////////
                if (visitedPtrFuncs.find(name) == visitedPtrFuncs.end())
                {
                  visitedPtrFuncs[name] = 1;
                  nullChekedFuncs[name] = 0;
                }
                else
                {
                  visitedPtrFuncs[name] += 1;
                }
                ///// here this function covers null-check find, init/read insn as well
                track_uses(callInsn, name, nullChekedFuncs, initializedCall, readFromCall, isErrFuncs);
              }
            }
          }
        }

        //finalize current F
        if (isFptrRet && !isFgetter)
        {
          potentialFOIsSet.insert(F.getName());
          OP << F.getName() << "\n";
        }
      }
    } //end of loop on bc_files

    potentialFOIsFile << "function-name; times Visited; times Checked; times init; times read\n";
    for (auto foi : potentialFOIsSet)
    {
      if (visitedPtrFuncs.find(foi) == visitedPtrFuncs.end())
        continue;
      auto visNum = visitedPtrFuncs[foi];
      auto ncNum = nullChekedFuncs[foi];
      auto initVec = initializedCall[foi];
      auto readVec = readFromCall[foi];
      auto isErrVec = isErrFuncs[foi];
      potentialFOIsFile << foi << " " << visNum << " " << ncNum << " " << initVec.size() << " " << readVec.size() << "\n";

      if (initVec.size())
      {
        initLocationsFile << foi << "\n";
        for (auto &initInsn : initVec)
        {
          if (DILocation *Loc = initInsn->getDebugLoc())
          { //record the line info
            string initSrcPath = Loc->getFilename().str() +
                                 +":" + std::to_string(Loc->getLine());
            initLocationsFile << "\t" << initSrcPath << "\n";
          }
        }
      }
      if (readVec.size())
      {
        readLocationsFile << foi << "\n";
        for (auto &readInsn : readVec)
        {
          if (DILocation *Loc = readInsn->getDebugLoc())
          { //record the line info
            string readSrcPath = Loc->getFilename().str() +
                                 +":" + std::to_string(Loc->getLine());
            readLocationsFile << "\t" << readSrcPath << "\n";
          }
        }
      }

      if (isErrVec.size())
      {
        isErrLocationsFile << foi << "\n";
        for (auto &errInsn : isErrVec)
        {
          if (DILocation *Loc = errInsn->getDebugLoc())
          { //record the line info
            string readSrcPath = Loc->getFilename().str() +
                                 +":" + std::to_string(Loc->getLine());
            isErrLocationsFile << "\t" << readSrcPath << "\n";
          }
        }
      }
    }

    isErrLocationsFile.close();

    potentialFOIsFile.close();
    initLocationsFile.close();
    readLocationsFile.close();
    bc_files.close();
  }
}
//looks for any functions with a pinter return type, which is at least once checked against NULL
void findPointerReturningFuncs(void)
{
  string bc_list = WRK_DIR + "bc.list";

  ofstream ptRtFuncs;
  ptRtFuncs.open(WRK_DIR + "PointerReturningFuncs.txt", ios::out);

  ofstream checkLackFuncs;
  checkLackFuncs.open(WRK_DIR + "CheckLackingFuncs.txt", ios::out);

  ifstream bc_files;
  bc_files.open(bc_list, ios::in);
  if (!bc_files.is_open())
  {
    OP << "Failed to open foi.txt\n"
       << bc_list << "\n";
    exit(1);
  }
  string line;

  std::ofstream callSiteFile;
  callSiteFile.open(WRK_DIR + "totalCallSite.txt", std::ios::out);

  unsigned i = 1;
  while (getline(bc_files, line))
  { // for each .bc file
    OP << i++ << "- Processing bitcode:\n"
       << line << "\n";

    EqMap.clear();
    skipGEPs.clear();
    ptRtFuncs.flush();
    map<Function *, set<pair<Function *, Value *>>> callersMap; // a map from fn to (caller, callInsn)
    LLVMContext *LLVMCtx = new LLVMContext();
    auto M = load_module(line, *LLVMCtx);
    alreadyLoadedModules[line] = M;

    //fill in the callers map, and callSites
    if(M)
    for (auto &F : *M)
    {
      for (auto &BB : F)
      {
        for (auto &I : BB)
        {
          auto callInsn = dyn_cast<CallInst>(&I);
          Value *callV = &I;
          if (callInsn)
          {
            auto callee = getCallee(callInsn);
            if (callee)
            {

              auto clName = callee->getName();
              if (clName.startswith("llvm"))
                continue;
              if (DILocation *Loc = callInsn->getDebugLoc())
              { //record the line info
                string callerSrcPath = Loc->getFilename().str() +
                                       +":" + std::to_string(Loc->getLine());
                callSiteFile << clName.str() << "\t" << callerSrcPath << "\n";
              }

              if (callersMap.find(callee) == callersMap.end())
              {
                set<pair<Function *, Value *>> tmpSet;

                tmpSet.insert(make_pair(&F, callV));
                callersMap[callee] = tmpSet;
              }
              else
              {
                auto tmpSet = callersMap[callee];
                tmpSet.insert(make_pair(&F, callV));
                callersMap[callee] = tmpSet;
              }
            }
          }
        }
      }
    }

    for (auto &F : *M)
    {
      set<Value *> arg_list;
      for (Argument &arg : F.args())
      {
        arg_list.insert((Value *)(&arg));
      }
      for (auto &BB : F)
      {
        for (auto &I : BB)
        {
          auto callInsn = dyn_cast<CallInst>(&I);
          if (callInsn)
          {
            auto callee = getCallee(callInsn);
            if (callee && pointerReturning(callee))
            {
              if (callee->getName().startswith("llvm"))
                continue;
              string name = callee->getName().str();
              if (visited.find(name) == visited.end())
              {
                visited[name] = make_pair(1, 0);
              }
              else
              {
                visited[name].first += 1;
              }
              visitedUses.clear();
              auto equals = findEquivalents((Value *)callInsn);
              if (DEBUG_PRINT)
              {
                OP << "EQ of: " << *callInsn << "\n";
                for (auto &v : equals)
                {
                  OP << *v << "\n";
                }
              }

              bool nullChecked = false;
              bool isEscaping = false;
              bool isDerefed = false;
              vector<Instruction *> derefInsns;
              for (auto &eqVal : equals)
              {
                if (DEBUG_PRINT)
                {
                  OP << *eqVal << "\n";
                }
                if (arg_list.find(eqVal) != arg_list.end())
                { //is assigned to a func parameter
                  ;
                }

                auto users = ((Value *)eqVal)->users();

                for (const auto &UI : users)
                { // UI: usrs iterator
                  Value *useVal = &(*UI);
                  if (DEBUG_PRINT)
                    OP << *useVal << "\n";
                  auto cmpInsn = dyn_cast<ICmpInst>(useVal);
                  if (cmpInsn && nullChecked == false)
                  { //still looking for null check
                    Value *compareTo;
                    if (cmpInsn->getOperand(0) == eqVal)
                    {
                      compareTo = cmpInsn->getOperand(1);
                    }
                    else if (cmpInsn->getOperand(1) == eqVal)
                    {
                      compareTo = cmpInsn->getOperand(0);
                    }
                    else
                    {
                      OP << "Imposible happened!! compare insn is not comparing call insn!\n";
                      exit(1);
                    }
                    ConstantPointerNull *CPN = dyn_cast<ConstantPointerNull>(compareTo);
                    if (CPN)
                    {
                      if (DEBUG_PRINT)
                        OP << name << "\n";
                      if (visited.find(name) == visited.end())
                      {
                        OP << "IMPOSIBLE Happened! checked while not visited before?!\n";
                        exit(1);
                      }
                      else
                      {
                        visited[name].second += 1;
                        nullChecked = true;
                      }
                    }
                  }
                  auto retInsn = dyn_cast<ReturnInst>(useVal);
                  if (retInsn)
                  { // is being returned; and by defenition it is a pointer
                    isEscaping = true;
                  }
                  auto loadInsn = dyn_cast<LoadInst>(useVal);
                  if (loadInsn)
                  {
                    Value *ptrVal = loadInsn->getPointerOperand();
                    if (!isPointerToPointer(ptrVal))
                    {
                      if (eqVal == ptrVal)
                      {
                        isDerefed = true;
                        derefInsns.push_back(loadInsn);
                      }
                    }
                  }
                  auto storeInsn = dyn_cast<StoreInst>(useVal);
                  if (storeInsn)
                  { // compare to the store dst (not pointer to pointer)
                    Value *ptrVal = storeInsn->getPointerOperand();
                    if (!isPointerToPointer(ptrVal))
                    {
                      if (eqVal == ptrVal)
                      {
                        isDerefed = true;
                        derefInsns.push_back(storeInsn);
                      }
                    }
                  }
                  auto gepInsn = dyn_cast<GetElementPtrInst>(useVal);
                  if (gepInsn)
                  {
                    Value *basePtr = gepInsn->getOperand(0);
                    if (eqVal == basePtr)
                    { // being used as base struct pointer
                      isDerefed = true;
                      derefInsns.push_back(gepInsn);
                    }
                  }
                }
              } // end of nullCheck find

              if (nullChecked == false)
              {
                if (DEBUG_PRINT)
                  OP << "Not checked in current func.\n";
                if (DILocation *Loc = callInsn->getDebugLoc())
                { //record the line info
                  string callerSrcPath = Loc->getFilename().str() +
                                         +":" + std::to_string(Loc->getLine());
                  checkLackFuncs << "\n"
                                 << name << "\tnot checked at " << callerSrcPath << "\n";
                }
                //check for dereferences
                if (isDerefed)
                {
                  if (DEBUG_PRINT)
                    OP << "Potential NULL Deref!!\n";
                  for (auto &dInsn : derefInsns)
                  {
                    if (DILocation *Loc = dInsn->getDebugLoc())
                    {
                      string derefSrcPath = Loc->getFilename().str() +
                                            +":" + std::to_string(Loc->getLine());
                      checkLackFuncs << name << "\tDerefed at: " << derefSrcPath << "\n";
                    }
                  }
                }
                if (isEscaping)
                {
                  auto grandCallers = callersMap[&F];
                  for (auto &gCallerPair : grandCallers)
                  {
                    auto gCaller = gCallerPair.first;
                    auto gCallerV = gCallerPair.second;
                    // assuming each caller definately calls the FOI:
                    visited[name].first += 1;

                    visitedUses.clear(); //is needed before any eq find!
                    auto callerEq = findEquivalents(gCallerV);
                    bool isDerefedInCaller = false;
                    vector<Instruction *> callerDerefInsns;
                    bool callerChecked = findNullCheckOrDeref(name, callerEq, &isDerefedInCaller, &callerDerefInsns);
                    if (!callerChecked)
                    {
                      if (DEBUG_PRINT)
                        OP << "Not checked in the caller func too!\n";
                      if (isDerefedInCaller)
                      {
                        if (DEBUG_PRINT)
                          OP << "Potential NULL Deref in caller!!\n";
                        for (auto &dInsn : callerDerefInsns)
                        {
                          if (DILocation *Loc = dInsn->getDebugLoc())
                          {
                            string derefSrcPath = Loc->getFilename().str() +
                                                  +":" + std::to_string(Loc->getLine());
                            checkLackFuncs << "\tDerefed in caller at: " << derefSrcPath << "\n";
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    LLVMDisposeModule((LLVMModuleRef)M);
  }
  callSiteFile.close();

  ptRtFuncs << "function-name; times Visited; times Checked\n";
  for (auto &fn : visited)
  {
    ptRtFuncs << fn.first << ": " << fn.second.first << " " << fn.second.second << "\n";
  }
  ptRtFuncs.close();
  checkLackFuncs.close();
}
///////////////
//collect call graph over the whole kernel
void collect_funcs_definition_map(void)
{
  string bc_list = WRK_DIR + "bc.list";

  ofstream funcsDefinitionMap;
  funcsDefinitionMap.open(WRK_DIR + "funcsDefinitionMap.txt", ios::out);
  ofstream bcFileMap;
  bcFileMap.open(WRK_DIR + "bcFileMap.txt", ios::out);

  ifstream bc_files;
  bc_files.open(bc_list, ios::in);
  if (!bc_files.is_open())
  {
    OP << "Failed to open bc_file\n"
       << bc_list << "\n";
    exit(1);
  }
  string line;

  unsigned i = 0;
  while (getline(bc_files, line))
  { // for each .bc file
    OP << i << "- Processing bitcode:\n"
       << line << "\n";
    bcFileMap << i << "\t" << line << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    auto M = load_module(line, *LLVMCtx);
    alreadyLoadedModules[line] = M;

    //just record which funcs are defined in this bc file
    if (M)
    for (auto &F : *M)
    {
      auto funcName = F.getName();
      if (funcName.startswith("llvm") || F.isDeclaration())
        continue;
      funcsDefinitionMap << funcName.str() << "\t" << i << "\n";
    }
    i++;
    LLVMDisposeModule((LLVMModuleRef)M);
  }
  funcsDefinitionMap.close();
  bcFileMap.close();
  bc_files.close();
}
////////////////
//collect call graph over the whole kernel
void collect_call_graph(void)
{
  string bc_list = WRK_DIR + "bc.list";
  string line;

  //load iCallSigs
  ifstream iCallFile(WRK_DIR + "iCallSigs.txt");
  if (!iCallFile.is_open())
  {
    OP << "Failed to open iCallSigs.txt";
    exit(1);
  }

  while (getline(iCallFile, line))
  {
    vector<string> tokens;
    Tokenize(line, tokens, ":");
    if (tokens.size() < 2)
      continue;

    auto sig = tokens[0];
    set<string> fns;
    vector<string> tk2;
    Tokenize(tokens[1], tk2, " ");
    for (auto &f : tk2)
    {
      fns.insert(f);
    }
    iCallMap[sig] = fns;
  }
  iCallFile.close();
  ///

  ofstream callersMapFile(WRK_DIR + "callersMap.txt");

  ofstream callGraphMap;
  callGraphMap.open(WRK_DIR + "callGraphMap.txt", ios::out);

  ifstream bc_files;
  bc_files.open(bc_list, ios::in);
  if (!bc_files.is_open())
  {
    OP << "Failed to open foi.txt\n"
       << bc_list << "\n";
    exit(1);
  }
  int untracked = 0;
  unsigned i = 1;
  while (getline(bc_files, line))
  { // for each .bc file
    OP << i++ << "- Processing bitcode:\n"
       << line << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    auto M = load_module(line, *LLVMCtx);
    alreadyLoadedModules[line] = M;

    //fill in the callers map, and callSites
    if(M)
    for (auto &F : *M)
    {
      auto callerName = F.getName();
      callGraphMap << "\n[" << callerName.str() << "]\n\t";
      for (auto &BB : F)
      {
        for (auto &I : BB)
        {
          auto callInsn = dyn_cast<CallInst>(&I);
          // Value *callV = &I;
          if (callInsn)
          {
            string clName;
            if (auto callee = getCallee(callInsn))
            {
              auto cN = callee->getName();
              if (cN.startswith("llvm"))
                continue;
              clName = cN.str();
              callGraphMap << clName << " ";
            }
            else if (auto iCall = getCalleeVal(callInsn))
            {
              auto sig = extractFuncSignature(iCall);
              if (iCallMap.find(sig) == iCallMap.end())
              { // such iCall was not recorded!
                if (DEBUG_PRINT)
                  OP << "Unknown iCall:\n"
                     << callerName << "\n"
                     << *callInsn << "\n"
                     << sig << "\n";
                untracked++;
                continue;
              }
              clName = *iCallMap[sig].begin();
              callGraphMap << clName << " ";
            }
            else
            { //inline asm
              continue;
            }

            callersMap[clName].insert(callerName);
          }
        }
      }
    }
    LLVMDisposeModule((LLVMModuleRef)M);
  }

  for (auto &elem : callersMap)
  {
    auto cleeN = elem.first;
    auto clrsN = elem.second;

    callersMapFile << cleeN << ": ";
    for (auto &n : clrsN)
    {
      callersMapFile << n << " ";
    }
    callersMapFile << "\n";
  }
  callersMapFile.close();
  callGraphMap.close();
  bc_files.close();
}

////////////////
//stricly determine if start reaches end?
bool val_reaches(Value *start, Value *end)
{
  auto stInsn = dyn_cast<Instruction>(start);
  auto enInsn = dyn_cast<Instruction>(end);
  if (!stInsn || !enInsn)
    return false;

  auto startBB = stInsn->getParent();
  auto startReachables = findReachableBBs(startBB);
  auto endBB = enInsn->getParent();
  auto endReachables = findReachableBBs(endBB);

  if (startBB == endBB)
  { // both Vals in same BB
    for (Instruction &Insn : *startBB)
    {
      if ((Value *)&Insn == start)
        return true;
      if ((Value *)&Insn == end)
        return false;
    }
  }

  if (startReachables.find(endBB) != startReachables.end())
  { //start reaches the end
    return true;
  }

  return false;
}

void collect_icalls(void)
{
  string bc_list = WRK_DIR + "bc.list";

  ofstream iCallMapFile;
  iCallMapFile.open(WRK_DIR + "iCallSigs.txt", ios::out);

  ifstream bc_files;
  bc_files.open(bc_list, ios::in);
  if (!bc_files.is_open())
  {
    OP << "Failed to open bc.list\n"
       << bc_list << "\n";
    exit(1);
  }
  string line;

  unsigned i = 1;
  while (getline(bc_files, line))
  { // for each .bc file
    OP << i++ << "- Processing bitcode:\n"
       << line << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    auto M = load_module(line, *LLVMCtx);
    alreadyLoadedModules[line] = M;

    //fill in
    for (auto &F : *M)
    {
      if (F.hasAddressTaken() || (F.hasExternalLinkage() && !F.empty()))
      {
        if (DEBUG_PRINT)
          OP << F.getName() << "\n";
        auto sig = extractFuncSignature(F.getFunctionType());
        iCallMap[sig].insert(F.getName());
      }
    }
  }

  for (auto &elem : iCallMap)
  {
    auto s = elem.first;
    auto fns = elem.second;
    iCallMapFile << s << ": ";
    for (auto &f : fns)
    {
      iCallMapFile << f << " ";
    }
    iCallMapFile << "\n";
  }
  iCallMapFile.close();
}

//++++++++++++++++++++++++++++++++++++++++++
void CallGraphMain(void)
{
  init_output_files();
  collect_icalls();
  collect_call_graph();
}

void FOIcollect(void)
{
  init_output_files();
  collectGetterFuncs();
  findPotentialFOIs();
}

void SequenceMine(void)
{
  /*pass to extract paths for a specific FOI*/
  init_output_files();
  sequenceMine();
}
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/CallSite.h>
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"


#include <fstream>
#include "Common.h"

#define LINUX_SOURCE_DIR1 "/home/kjlu/projects/kernel-analysis/compile-kernel/code/srcs/linux-stable-4.20.0"
#define LINUX_SOURCE_ANDROID "/home/kjlu/projects/kernels/compile-linux/code/srcs/linux-android-4.9"
#define LINUX_SOURCE_FREEBSD "/home/kjlu/projects/kernel-analysis/compile-kernel/code/srcs/freebsd-12"
#define LINUX_SOURCE_DIR_4_19_1 "/home/pakki001/research/linux"
#define LINUX_SOURCE_DIR_4_19_2 "/home/aditya/linux-src"
#define LINUX_SOURCE_DIR_4_20_0 "/home/qiushi/Desktop/Sec-Check/kernel-analysis/compile-kernel/code/srcs/linux-stable-4.20.0"
#define LINUX_SOURCE_DIR_NVD "/export/scratch/navid/MOSE/mose-git/kernel-analysis/compile-kernel/code/srcs/linux-stable-4.19.0"

DILocation *getSourceLocation(Instruction *I);
// string getFileName(DILocation *Loc, DISubprogram *SP) {
// 	string FN;
// 	if (Loc)
// 		FN= Loc->getFilename().str();
// 	else if (SP)
// 		FN= SP->getFilename().str();
// 	else
// 		return "";

// 	char *user = getlogin();
// 	const char *filename = FN.c_str();
// 	filename = strchr(filename, '/') + 1;
// 	filename = strchr(filename, '/');
// 	int idx = filename - FN.c_str();
// 	if (strstr(user, "kjlu")) {
// 		//if (FN.find("linux-stable") != std::string::npos)
// 		//FN.replace(0, idx, LINUX_SOURCE_FREEBSD);
// 		FN.replace(0, idx, LINUX_SOURCE_DIR1);
// 		//else
// 		//	FN.replace(0, 54, LINUX_SOURCE_DIR1);
// 	} else if (strstr(user, "pakki001")) {
// 		FN.replace(0, idx, LINUX_SOURCE_DIR_4_19_1);
// 	} else if (strstr(user, "aditya")) {
// 		FN.replace(0, idx, LINUX_SOURCE_DIR_4_19_2);
// 	} else if (strstr(user, "qiushi")) {
// 		FN.replace(0, idx, LINUX_SOURCE_DIR_4_20_0);
// 	} else if (strstr(user, "emamd")) {
// 		FN.replace(0, idx, LINUX_SOURCE_DIR_NVD);		
// 	} else {
// 		OP << "== Warning: please specify the path of linux source.\n";
// 	}
// 	return FN;
// }

/// Check if the value is a constant.
bool isConstant(Value *V) {
  // Invalid input.
  if (!V) 
    return false;

  // The value is a constant.
  Constant *Ct = dyn_cast<Constant>(V);
  if (Ct) 
    return true;

  return false;
}

/// Get the source code line
string getSourceLine(string fn_str, unsigned lineno) {
	std::ifstream sourcefile(fn_str);
	string line;
	sourcefile.seekg(ios::beg);
	
	for(int n = 0; n < lineno - 1; ++n){
		sourcefile.ignore(std::numeric_limits<streamsize>::max(), '\n');
	}
	getline(sourcefile, line);

	return line;
}

// string getSourceFuncName(Instruction *I) {

// 	DILocation *Loc = getSourceLocation(I);
// 	if (!Loc)
// 		return "";
// 	unsigned lineno = Loc->getLine();
// 	std::string fn_str = getFileName(Loc, NULL);
// 	string line = getSourceLine(fn_str, lineno);
	
// 	while(line[0] == ' ' || line[0] == '\t')
// 		line.erase(line.begin());
// 	line = line.substr(0, line.find('('));
// 	return line;
// }


/// Get called function name of V.
StringRef getCalledFuncName(Instruction *I) {

  Value *V;
	if (CallInst *CI = dyn_cast<CallInst>(I))
		V = CI->getCalledValue();
	else if (InvokeInst *II = dyn_cast<InvokeInst>(I))
		V = II->getCalledValue();
	assert(V);

  InlineAsm *IA = dyn_cast<InlineAsm>(V);
  if (IA)
    return StringRef(IA->getAsmString());

  User *UV = dyn_cast<User>(V);
  if (UV) {
    if (UV->getNumOperands() > 0) {
			Value *VUV = UV->getOperand(0);
			return VUV->getName();
		}
  }

	return V->getName();
}

DILocation *getSourceLocation(Instruction *I) {
  if (!I)
    return NULL;

  MDNode *N = I->getMetadata("dbg");
  if (!N)
    return NULL;

  DILocation *Loc = dyn_cast<DILocation>(N);
  if (!Loc || Loc->getLine() < 1)
		return NULL;

	return Loc;
}

/// Print out source code information to facilitate manual analyses.
// void printSourceCodeInfo(Value *V) {
// 	Instruction *I = dyn_cast<Instruction>(V);
// 	if (!I)
// 		return;

// 	DILocation *Loc = getSourceLocation(I);
// 	if (!Loc)
// 		return;

// 	unsigned LineNo = Loc->getLine();
// 	std::string FN = getFileName(Loc, NULL);
// 	string line = getSourceLine(FN, LineNo);
// 	FN = Loc->getFilename().str();
// 	const char *filename = FN.c_str();
// 	filename = strchr(filename, '/') + 1;
// 	filename = strchr(filename, '/') + 1;
// 	int idx = filename - FN.c_str();

// 	while(line[0] == ' ' || line[0] == '\t')
// 		line.erase(line.begin());
// 	OP << " ["
// 		<< "\033[34m" << "Code" << "\033[0m" << "] "
// 		<< FN.replace(0, idx, "") 
// 		<< " +" << LineNo << ": "
// 		<< "\033[35m" << line << "\033[0m" <<'\n';
// }

void printSourceCodeInfo(Function *F) {
	
	DISubprogram *SP = F->getSubprogram();
	
	if (SP) {
		std::string FN = getFileName(NULL, SP);
		string line = getSourceLine(FN, SP->getLine());
		while(line[0] == ' ' || line[0] == '\t')
			line.erase(line.begin());

		OP << " ["
			<< "\033[34m" << "Code" << "\033[0m" << "] "
			<< SP->getFilename()
			<< " +" << SP->getLine() << ": "
			<< "\033[35m" << line << "\033[0m" <<'\n';
	}
}

/// Get source code information of this value
void getSourceCodeInfo(Value *V, string &file,
                               unsigned &line) {
  file = "";
  line = 0;

  auto I = dyn_cast<Instruction>(V);
  if (!I)
    return;

  MDNode *N = I->getMetadata("dbg");
  if (!N)
    return;

  DILocation *Loc = dyn_cast<DILocation>(N);
  if (!Loc || Loc->getLine() < 1)
    return;

  file = Loc->getFilename().str();
  line = Loc->getLine();
}

Argument *getArgByNo(Function *F, int8_t ArgNo) {

  if (ArgNo >= F->arg_size())
    return NULL;

  int8_t idx = 0;
  Function::arg_iterator ai = F->arg_begin();
  while (idx != ArgNo) {
    ++ai;
    ++idx;
  }
  return ai;
}

//#define HASH_SOURCE_INFO
// size_t funcHash(Function *F, bool withName) {

// 	hash<string> str_hash;
// 	string output;

// #ifdef HASH_SOURCE_INFO
// 	DISubprogram *SP = F->getSubprogram();

// 	if (SP) {
// 		output = SP->getFilename();
// 		output = output + to_string(uint_hash(SP->getLine()));
// 	}
// 	else {
// #endif
// 		string sig;
// 		raw_string_ostream rso(sig);
// 		Type *FTy = F->getFunctionType();
// 		FTy->print(rso);
// 		output = rso.str();

// 		if (withName)
// 			output += F->getName();
// #ifdef HASH_SOURCE_INFO
// 	}
// #endif
// 	string::iterator end_pos = remove(output.begin(), 
// 			output.end(), ' ');
// 	output.erase(end_pos, output.end());

// 	return str_hash(output);
// }
/*
size_t callHash(CallInst *CI) {

	CallSite CS(CI);
	Function *CF = CI->getCalledFunction();

	if (CF)
		return funcHash(CF, false);
	else {
		hash<string> str_hash;
		string sig;
		raw_string_ostream rso(sig);
		Type *FTy = CS.getFunctionType();
		FTy->print(rso);
		
		string strip_str = rso.str();
		string::iterator end_pos = remove(strip_str.begin(), 
				strip_str.end(), ' ');
		strip_str.erase(end_pos, strip_str.end());
		return str_hash(strip_str);
	}
}

size_t typeHash(Type *Ty) {
	hash<string> str_hash;
	string sig;

	raw_string_ostream rso(sig);
	Ty->print(rso);
	string ty_str = rso.str();
	string::iterator end_pos = remove(ty_str.begin(), ty_str.end(), ' ');
	ty_str.erase(end_pos, ty_str.end());
	
	return str_hash(ty_str);
}

size_t typeIdxHash(Type *Ty, unsigned Idx) {
	hash<string> str_hash;
	string sig;

	raw_string_ostream rso(sig);
	string ty_str;
	if (StructType *STy = dyn_cast<StructType>(Ty)) {
		ty_str = STy->getName();
	}
	else {
		Ty->print(rso);
		ty_str = rso.str();
	}
	ty_str += to_string(Idx);
	string::iterator end_pos = remove(ty_str.begin(), ty_str.end(), ' ');
	ty_str.erase(end_pos, ty_str.end());
	
	return str_hash(ty_str);
}
*/
// bool getBaseStructIdx(Value *V, Type * &STy, unsigned &Idx, 
// 		const DataLayout *DL) {

// 	if (GetElementPtrInst *GEP 
// 			= dyn_cast<GetElementPtrInst>(V)) {
// 		Type *PTy = GEP->getPointerOperand()->getType();
// 		Type *Ty = PTy->getPointerElementType();
// 		if ((Ty->isStructTy() || Ty->isArrayTy()) && GEP->hasAllConstantIndices()) {
// 			STy = Ty;
// 			User::op_iterator ie = GEP->idx_end();
// 			ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
// 			Idx = ConstI->getZExtValue();
// 			/*
// 			APInt Offset(DL->getPointerTypeSizeInBits(GEP->getType()), 0);
// 			if(!GEP->accumulateConstantOffset(*DL, Offset))
// 				return false;
// 			Idx = Offset.getLimitedValue();
// 			for (User::op_iterator i = GEP->idx_begin(), ie = GEP->idx_end();
// 					i != ie; ++i) {
// 				ConstantInt *ConstI = dyn_cast<ConstantInt>(i->get());
// 				if (i != ie - 1)
// 					Idx = Idx * ConstI->getZExtValue();
// 				else
// 					Idx += ConstI->getZExtValue();
// 			}
// 			*/
// 			return true;
// 		}
// 		else
// 			return false;
// 	}
// 	else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(V)) {
// 		return getBaseStructIdx(UI->getOperand(0), STy, Idx, DL);
// 	}
// #if 0
// 	//FIXME: 
// 	else if (
// 			isa<GlobalVariable>(V) 
// 			) {

// 		STy = V->getType();
// 		Idx = 0;
// 		return true;
// 	}
// #endif


// 	return false;
// }

// #ifndef UNISAN_COMMON_H
// #define UNISAN_COMMON_H

#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/DebugInfoMetadata.h>

#include <unistd.h>
#include <bitset>
#include <chrono>
#include <map>

using namespace llvm;
using namespace std;

#define LOG(lv, stmt)							\
	do {											\
		if (VerboseLevel >= lv)						\
		errs() << stmt;							\
	} while(0)


#define OP llvm::errs()

#define WARN(stmt) LOG(1, "\n[WARN] " << stmt);

#define ERR(stmt)													\
	do {																\
		errs() << "ERROR (" << __FUNCTION__ << "@" << __LINE__ << ")";	\
		errs() << ": " << stmt;											\
		exit(-1);														\
	} while(0)


extern cl::opt<unsigned> VerboseLevel;


// #endif

//
// Common functions
//

// string getFileName(DILocation *Loc, 
// 		DISubprogram *SP=NULL);

bool isConstant(Value *V);

string getSourceLine(string fn_str, unsigned lineno);

string getSourceFuncName(Instruction *I);

StringRef getCalledFuncName(Instruction *I);

DILocation *getSourceLocation(Instruction *I);

void printSourceCodeInfo(Value *V);
void printSourceCodeInfo(Function *F);

void getSourceCodeInfo(Value *V, string &file,
                               unsigned &line);

Argument *getArgByNo(Function *F, int8_t ArgNo);

bool getBaseStructIdx(Value *V, Type * &STy, unsigned &Idx, 
		const DataLayout *DL);

// size_t funcHash(Function *F, bool withName=true);
size_t callHash(CallInst *CI);
size_t typeHash(Type *Ty);
size_t typeIdxHash(Type *Ty, unsigned Idx);

// class SanityCheck {
// public:
//   SanityCheck(Value *sk, Value *br) : SCheck(sk), SCBranch(br) {
//     auto I = dyn_cast<Instruction>(SCheck);
//     if (!I)
//       return;

//     MDNode *N = I->getMetadata("dbg");
//     if (!N)
//       return;

//     DILocation *Loc = dyn_cast<DILocation>(N);
//     if (!Loc || Loc->getLine() < 1)
//       return;

//     SCheckFileName = Loc->getFilename().str();
//     SCheckLineNo = Loc->getLine();
//   }

//   ~SanityCheck() {
//   }

//   Value *getSCheck() { return SCheck; }

//   Value *getSCBranch() { return SCBranch; }

//   string getSCheckFileName() { return SCheckFileName; }

//   unsigned getSCheckLineNo() { return SCheckLineNo; }

// 	friend bool operator< (const SanityCheck &SC1, const SanityCheck &SC2) {
// 		return (SC1.SCheck < SC2.SCheck);
// 	}

// private:
//   Value *SCheck;          /* Security check of this critical variable */
//   Value *SCBranch;        /* Branch associated to the check */
//   string SCheckFileName; /* Source file name of security check */
//   unsigned SCheckLineNo;  /* Line number of security check */
// };
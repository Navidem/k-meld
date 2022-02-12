#ifndef _CRITICAL_FUNC_H
#define _CRITICAL_FUNC_H

#include <llvm/Analysis/BasicAliasAnalysis.h>

#include "Kmeld.h"

#endif

void CallGraphMain(void);
void FOIcollect(void);
void SequenceMine(void);

void debug_print_BB(llvm::BasicBlock *BB, bool verbose);
std::set<llvm::Value *> findValueSources(llvm::Value *target, bool loosen_gep);
llvm::Value *findValueFlow(llvm::Value *, bool, llvm::Value *);
bool is_call_succesful(llvm::Instruction *CI, const std::vector<llvm::BasicBlock *> *path);
std::string extractFuncSignature(llvm::FunctionType *FT);
void process_paths(const std::vector<std::tuple<std::vector<llvm::BasicBlock *>, std::string,
                    bool, bool, bool, std::string, std::pair<std::string, int>>> &inputPaths,
                   llvm::Value *foi_value, llvm::Instruction *foi_check, const llvm::Function *F, bool escapePaths);
bool reaches(llvm::BasicBlock *, llvm::BasicBlock *, std::vector<llvm::BasicBlock *> &);

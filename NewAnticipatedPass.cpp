#include "llvm/Transforms/Utils/AnticipatedExpressions.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <list>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>
using namespace llvm;

class Expression{
    public:
    
    // For Other
    std::vector<Value*>ops;
    std::vector<Value*>call_ops;
    int id;
    // Instruction* I;
    int numOp;
    std::string opname;
    unsigned int opcode;
    bool isHoisted, hasNSW, hasNUW;
    Instruction *hoist_inst;
    
    // Call
    int sizeOfArguments;
    Function *fun;
    StringRef nameOfFunction;
    Type *ret;

    // For Cast
    Type *castType;
    Value *cast_op;
    
    // For ICMP
    CmpInst::Predicate pred;
    Expression(Instruction *I){
        
        this->opcode = I->getOpcode();
        this->opname = I->getOpcodeName(opcode);
        //this->I = I;
        this->isHoisted = false;
        this->hasNSW = false;
        this->hasNUW = false;
        this->hoist_inst = NULL;
        this->numOp = I->getNumOperands();
        this->ops.resize(I->getNumOperands());
        for(int i=0; i<I->getNumOperands(); i++){
            this->ops[i] = I->getOperand(i);
        }
        

        if(isa<CallInst>(I)){
            this->id=0;
            CallInst *call = dyn_cast<CallInst>(I);
            this->sizeOfArguments = call->arg_size();
            this->fun = call->getCalledFunction();
            this->nameOfFunction = this->fun->getName();
            this->ret = call->getType();

            // this->call_ops.resize(this->sizeOfArguments);
            for(int i=0; i<this->sizeOfArguments; i++){
                this->call_ops.push_back(call->getArgOperand(i));
            }
            
        }
        else if(isa<CastInst>(I)){
            this->id = 1;
            CastInst *cast = dyn_cast<CastInst>(I);
            this->castType = cast->getDestTy();
            this->cast_op = cast->getOperand(0);
        }
        else if(isa<ICmpInst>(I)){
            this->id = 2;
            ICmpInst *icmp = dyn_cast<ICmpInst>(I);
            this->pred = icmp->getPredicate();
        }
        else {
            this->id = 3;
            // this->hasNSW = I->hasNoSignedWrap();
            // this->hasNUW = I->hasNoUnsignedWrap();
        }
    }         
};

bool areEqual(Expression *expr, Expression *ele){

    //0 is for call, 1 for cast, 2 for others
    if(expr->id == 0 && ele->id == 0){
        // errs() << "\n Enteringgg Call\n ";
        bool opCheck = true;
        if(expr->sizeOfArguments != ele->sizeOfArguments)
            return false;
        for(int i=0; i<expr->sizeOfArguments; i++){
            
            if(expr->call_ops[i]!=ele->call_ops[i]){
                opCheck = false;
            }
        }
        return expr->sizeOfArguments == ele->sizeOfArguments && expr->nameOfFunction == ele->nameOfFunction && opCheck && expr->ret && ele->ret;
    }
    
    else if(expr->id == 1 && ele->id == 1) {
        return ele->castType == expr->castType && expr->cast_op == ele->cast_op;
    }
    else if(expr->id == 2 && ele->id == 2){
        return expr->ops[0] == ele->ops[0] && expr->ops[1] == ele->ops[1] && expr->opcode == ele->opcode && expr->pred == ele->pred;
    }
    else if(expr->id == 3 && ele->id == 3){
        bool f = true;
        for(int i=0; i<expr->numOp; i++){
            if(expr->ops[i] != ele->ops[i]){
                f = false;
            }
        }
        return f && expr->opcode == ele->opcode;
    }
    
    else 
        return false;
    
}

bool isFeasibleInstruction(Instruction &I)
{
    if(!isa<StoreInst>(I) && !isa<AllocaInst>(I) && !isa<LoadInst>(I) && !isa<PHINode>(I) && !isa<BranchInst>(I) && !isa<ReturnInst>(I))
        return true;
    return false;
    
}
        
// This computes universal set of expressions
std::set<Expression *> computeExpression(Function &F, DenseMap<Expression *, unsigned> &exToBit, DenseMap<unsigned, Expression *> &BitToex, DenseMap<unsigned, std::set<BasicBlock *>> &exToBlock, unsigned k){
    std::set<Expression *> expressions;
    for(BasicBlock &BB: F){
        for(Instruction &I: BB){
            if(isFeasibleInstruction(I)){
                Expression *expr = new Expression(&I);
                bool f = true;
                for(auto *ele: expressions){
                    if(areEqual(expr, ele)){
                        f = false;
                        break;
                    }
                }
                if(f){
                    expressions.insert(expr);
                    exToBit[expr] = k; // Assigned each expressions unique integer
                    BitToex[k] = expr;
                    exToBlock[k].insert(&BB);
                    k++;
                }
                
            }
        }
    }
    return expressions;
}


void codeHoisting(Function &F, DenseMap<unsigned,std::set<BasicBlock*>> &exToBlock, DenseMap<Expression *, unsigned> &exToBit, DenseMap<unsigned, Expression *> &BitToex, std::map<BasicBlock *, BitVector> &OUTBitmap, std::map<BasicBlock *, BitVector> &INBitmap, bool &changed){
    std::list<BasicBlock *>DFSBlocks;
    for(BasicBlock *BB: depth_first(&F.getEntryBlock())){
        DFSBlocks.push_back(BB);
    }
    bool isHoisted = false;
    for(auto *BB: DFSBlocks){
        BitVector OUT = OUTBitmap[BB];
        BitVector IN = INBitmap[BB];
        if(OUT.none())
            continue;
        
        // errs() << "\n Checking if OUT bit is set \n";
        for(unsigned int i=0; i<OUT.size(); i++){
            if(OUT[i] == 1){
                
                // Get Expression
                Expression *hoist_expr = BitToex[i];
                BinaryOperator *bo = nullptr;
                
                // Traverse downwards and remove this expression
                std::list<BasicBlock *>DownBlocks;
                for(BasicBlock *item: depth_first(BB))
                    DownBlocks.push_back(item);
                for(BasicBlock *succ: DownBlocks)
                {
                    BasicBlock::iterator it = succ->begin();
                    while(it != succ->end()){
                        Instruction *newI;
                        if(Instruction *I = dyn_cast<Instruction>(it)){
                            
                            Expression *expr = new Expression(I);
                            it++;
                            if(areEqual(expr, hoist_expr)){
                                isHoisted = true;
                                if(hoist_expr->isHoisted){
                                        newI = hoist_expr->hoist_inst; 
                                }
                                else
                                {
                                    if(hoist_expr->id == 3){  
                                        hoist_expr->isHoisted = true;
                                        newI = bo->CreateWithCopiedFlags(static_cast<llvm::Instruction::BinaryOps>(hoist_expr->opcode), hoist_expr->ops[0], 
                                                hoist_expr->ops[1], I,"yp", BB->getTerminator());
                                        hoist_expr->hoist_inst = newI;
                                    }
                                    else if(hoist_expr->id == 0){
                                        //CallInst *call = dyn_cast<CallInst>(I);
                                        if(hoist_expr->isHoisted){
                                            newI = hoist_expr->hoist_inst; 
                                        }
                                        else{
                                            hoist_expr->isHoisted = true;
                                            newI = llvm::CallInst::Create(hoist_expr->fun,hoist_expr->call_ops,"yp", BB->getTerminator());
                                            hoist_expr->hoist_inst = newI;
                                        }
                        
                                        // errs() << "\n Hoisted Instruction\n";
                                        // newI->print(errs());
                                        // errs() << "\n------\n";     
                                    }
                                    else if(hoist_expr->id == 1){
                                    
                                        CastInst *cast = dyn_cast<CastInst>(I);
                                        hoist_expr->isHoisted = true;
                                        newI = llvm::CastInst::Create(static_cast<llvm::Instruction::CastOps>(cast->getOpcode()),hoist_expr->cast_op,hoist_expr->castType,"yp", BB->getTerminator());
                                        hoist_expr->hoist_inst = newI;
                                        // errs() << "\n Hoisted Instruction\n";
                                        // newI->print(errs());
                                        // errs() << "\n------\n";
                                    }
                                }
                                
                                I->replaceAllUsesWith(newI);    
                                I->eraseFromParent();  // Delete the instructions
                            }   
                                
                        }
                        
                    }
                }
            }
            
        }
    }
    if(isHoisted)
        changed = true;
}
        
// Compute BIT
std::map<BasicBlock *, BitVector> computeBIT(Function &F, std::map<BasicBlock *, std::set<Expression *>> ds, DenseMap<Expression *, unsigned> exToBit, std::set<Expression *> expressions,unsigned int size){
    std::map<BasicBlock *, BitVector> BlockBitMap;
    for (auto &BB : F) {
        BitVector helper(size, false);
        if (ds.count(&BB) == 0) {
            BlockBitMap[&BB] = helper;
            continue;
        }
        for (auto &use : ds[&BB]) {
            for(auto *ele: expressions){
                if(areEqual(use, ele)){
                    unsigned bit = exToBit[ele];
                    helper.set(bit);
                }
            }
        }
        BlockBitMap[&BB] = helper;
    }
    return BlockBitMap;
}

// Compute USE
std::map<BasicBlock *, std::set<Expression *>> computeUSE(Function &F){
    std::map<BasicBlock *,std::set<Expression *>> useMap;
    for (BasicBlock &BB : F) {
        std::set<Instruction *> definedInstructions;
        std::set<Expression *> usedExpressions;

        for (Instruction &I : BB) {
            if (isFeasibleInstruction(I)) {
                Expression *expr = new Expression(&I);
                bool canNotBeInserted = false;
                for(unsigned int i=0; i<I.getNumOperands(); i++){
                    if (auto *defInst = dyn_cast<Instruction>(expr->ops[i])) {
                        if (defInst->getParent() == &BB || definedInstructions.count(defInst)) {
                            canNotBeInserted = true;
                            continue;
                        }
                    }
                }

                // usedExpressions.insert(std::make_pair(op1, std::make_pair(op2, I.getOpcodeName(I.getOpcode()))));
                if(!canNotBeInserted)
                    usedExpressions.insert(expr);
            }
            definedInstructions.insert(&I);
        }
        useMap[&BB] = usedExpressions;  
    }
    return useMap;
}

// Compute DEF
std::map<BasicBlock *, std::set<Expression *>> computeDEF(Function &F){
    std::map<BasicBlock *, std::set<Expression *>> defMap;
    for(BasicBlock &BB: F){
        //std::set<Instruction *> definedInstructions;
        std::set<Expression *> DefExpressions;
        for(Instruction &I: BB){
            if(isFeasibleInstruction(I)){
                for(auto *use: I.users()){
                    Instruction *Inst = dyn_cast<Instruction>(use);
                    if (Inst && isFeasibleInstruction(*Inst)){
                        Expression *expr = new Expression(Inst);
                        DefExpressions.insert(expr);
                    }
                }
            }
        }
        defMap[&BB] = DefExpressions;
    }
    return defMap;
}

void initialiseIN_OUT(Function &F, std::map<BasicBlock *, BitVector> &IN,std::map<BasicBlock *, BitVector> &OUT,unsigned size){
    for(auto &BB: F){
        IN[&BB] = BitVector(size, true);
        OUT[&BB] = BitVector(size, false);
    }
}

/* PRINT FUNCTIONS FOR DEBUGGING */

// void printInstructions(Function &F){
//     for(BasicBlock &BB: F){
//         for(Instruction &I:BB){
//             if(isFeasibleInstruction(I)){
//                 errs() << "\n";
//                 I.print(errs());
//                 errs() << I.getOpcode() << " \n";
//             }
//         }
//     }
// }

// void printMap(std::map<BasicBlock *, std::set<Expression*>> ds, std::string s, Function &F){
//     errs() << "\n" << s << " \n";
//     for (auto &BB : F) {
//         errs() << "Basic Block " << BB.getName() << ":\n";

//         if (ds.count(&BB) == 0) {
//             errs() << "No USE sets.\n";
//             continue;
//         }

//         for (auto &use : ds[&BB]) {
//             // Value *B = use->op1;
//             // Value *C = use->op2;
//             // std::string opname = use->opname;
//             // if(B == D)  errs() << "True";
//             // errs() << "\t" << *B << " " << opname << " " << *C << "\n";
//             //errs() << *(use->I) << "\n";
//         }
//     }
//     errs() << "\n";
// }

// // Print Mapping Map
// void printMapping(DenseMap<Expression *, unsigned> exToBit){
//     for(const auto &pair: exToBit){
//         errs() << "Instruction:  " << *(pair.first->I) << " ------- " << "Bit: " << pair.second << "\n" ;
//     }
//     errs() << "\n";
// }


// void printexToBlock(DenseMap<unsigned, std::set<BasicBlock *>> exToBlock){
//     for(const auto &pair: exToBlock){
//         for(auto ele: pair.second){
//             errs() << "BasicBlock:" << ele << " -----  " << "Instruction: " << *(ele->begin()) << "\n";
//         }
//         errs() << "\n";
//     }
//     errs() << "\n";
// }

// // void printBitMap(Function &F, std::map<BasicBlock *, BitVector> bmap){
// //     for(auto &BB: F){
// //         BitVector temp = bmap[&BB];
// //         for (auto i = 0; i < temp.size(); i++) {
// //             errs() << temp[i];
// //         }
// //         errs() << "\n";
// //     }
// // }

// void printBitMap(Function &F, std::map<BasicBlock *, BitVector> bmap, DenseMap<unsigned, Expression*> BitToex){
    
//     for(auto &BB: F){
//         BitVector temp = bmap[&BB];
//         for (auto i = 0; i < temp.size(); i++) {
//             errs() << temp[i];
//             if(temp[i] == 1){
//                 auto *ele = BitToex[i];
//                 errs() << *(ele->I) << " ";
//             }
//         }
//         errs() << "\n";
//     }
// }


// void printOGmap(Function &F, std::map<BasicBlock *, std::set<Expression *>> ds){
//     for(auto &BB: F){
//         auto temp = ds[&BB];
//         for(auto *expr: temp){
//             // errs() << "\nOP1: " << *expr->op1;
//             // errs() << "\nOP2: " << *expr->op2;
//             errs() <<"\n I: " << *expr->I;
//             for(unsigned int i=0; i<expr->I->getNumOperands(); i++)
//                     errs() << "\n OP" << i << " " << *expr->ops[i];
//             errs() << "\nOPName: " << expr->opname << "\n";
//         }
//     }
//     errs() << "\n";
// }



PreservedAnalyses AnticipatedExpressionsPass::run(Function &F,FunctionAnalysisManager &AM) {
    // Expression to bit
    bool changed = true;
    while (changed) {
        DenseMap<Expression *, unsigned> exToBit;
        DenseMap<unsigned, Expression *> BitToex;
        DenseMap<unsigned, std::set<BasicBlock *>> exToBlock;
        unsigned expressPos = 0;

        changed = false;
        // Compute Expression
        std::set<Expression *> expressions = computeExpression(
            F, exToBit, BitToex, exToBlock, expressPos);
        unsigned int size = expressions.size();
        std::map<BasicBlock *, BitVector> UseBitMap, DefBitMap,
            INBitMap, OUTBitMap;

        // Compute USE and DEF
        // std::map<BasicBlock *, std::set<std::pair<Value *,
        // std::pair<Value *, std::string>>>> useMap, defMap;
        std::map<BasicBlock *, std::set<Expression *>> useMap, defMap;
        useMap = computeUSE(F);
        defMap = computeDEF(F);
        UseBitMap = computeBIT(F, useMap, exToBit, expressions, size);
        DefBitMap = computeBIT(F, defMap, exToBit, expressions, size);

        // Initialise IN and OUT sets
        initialiseIN_OUT(F, INBitMap, OUTBitMap, size);

        // Compute IN and OUT sets

        bool modified = true;
        while (modified) {
            modified = false;
            for (auto &BB : reverse(F)) {
                BitVector INBit = INBitMap[&BB];
                BitVector OUTBit = OUTBitMap[&BB];
                BitVector UseBit = UseBitMap[&BB];
                BitVector DefBit = DefBitMap[&BB];
                BitVector tempBit(size, false);
                if (!successors(&BB).empty()) {
                    OUTBit = INBitMap[*succ_begin(&BB)];
                    for (BasicBlock *succ : successors(&BB)) {
                        BitVector INBit = INBitMap[succ];
                        OUTBit &= INBit;
                    }
                }

                OUTBitMap[&BB] = OUTBit;
                DefBit.flip();
                OUTBit &= DefBit;
                OUTBit |= UseBit;
                if (!(OUTBit == INBit)) {
                    modified = true;
                }
                INBitMap[&BB] = OUTBit;
            }
        }
        codeHoisting(F, exToBlock, exToBit, BitToex, OUTBitMap,
                        INBitMap, changed);
        if (changed) {
            
            changed = true;
        }
        // **** Print Functions used for Debugging **** //
        /*printInstructions(F);
        printMap(useMap, "USE SET", F);
        printMap(defMap, "DEF SET", F);
        printMapping(exToBit);
        errs() << "IN\n";
        printBitMap(F, INBitMap);
        errs() << "OUT\n";
        printBitMap(F, OUTBitMap);
        errs() << "USE\n";
        printBitMap(F, UseBitMap);
        errs() << "DEF\n";
        printBitMap(F, DefBitMap);
        errs() << "\nIN BIT MAP\n";
        printBitMap(F, INBitMap, BitToex);
        errs() << "\nOUT BIT MAP\n";
        printBitMap(F, OUTBitMap, BitToex);
        errs() << "\nUSE BIT MAP\n";
        printBitMap(F, UseBitMap, BitToex);
        errs() << "\nDEF BIT MAP\n";
        printBitMap(F, DefBitMap, BitToex);
        errs() << "\nUSE MAP\n";
        printOGmap(F, useMap);
        errs() << "\nDEF MAP\n";
        printOGmap(F, defMap);
        printexToBlock(exToBlock);
        printexToBit(exToBit);*/
    }

    return PreservedAnalyses::all();
}

        

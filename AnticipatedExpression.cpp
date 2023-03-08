#include "llvm/Pass.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <set>
#include <string>
#include <utility>
using namespace llvm;

// namespace{
//     struct AnticipatedExpressions: public FunctionPass{
//         static char ID;
//         AnticipatedExpressions(): FunctionPass(ID){}

//         bool runOnFunction(Function &F) override{
//             std::map<BasicBlock*, std::set<Value*>> IN,OUT, USE, DEF;
//             for(auto &BB: F){
//                 IN[&BB] = std::set<Value*>();
//                 OUT[&BB] = std::set<Value*>();
//                 for(auto &I: BB){
//                     if(auto *inst = dyn_cast<Instruction>(&I)){
//                         IN[&BB].insert(inst);
//                     }
//                 }
//             }

//             // Compute USE and DEF for each block
//             for(auto &BB: F){
//                 USE[&BB] = computeUSE(BB);
//                 DEF[&BB] = computeDEF(BB);
//             }

//             // Finding IN and OUT sets
//             bool changed = true;
//             while (changed) {
//                 changed = false;
//                 for (auto &BB : F) {
//                     std::set<Value*> in_set = IN[&BB];
//                     std::set<Value*> out_set = OUT[&BB];
//                     for (BasicBlock *succ : successors(&BB)) {
//                         std::set<Value*> succ_in = IN[succ];
//                         std::set_intersection(succ_in.begin(), succ_in.end(),
//                                                 out_set.begin(), in_set.end(),
//                                                 std::inserter(out_set, out_set.begin()));
//                     }
//                     std::set_difference(out_set.begin(), out_set.end(),
//                                         DEF[&BB].begin(), DEF[&BB].end(),
//                                         std::inserter(in_set, in_set.begin()));
//                     std::set_union(in_set.begin(), in_set.end(),
//                                     USE[&BB].begin(), USE[&BB].end(),
//                                     std::inserter(in_set,in_set.begin()));
//                     std::set<Value*> old_in_set = IN[&BB];

//                     errs() << "IN: \n";
//                     for (Value *V : old_in_set) {
//                         V->print(errs());
//                         errs() << "\n";
//                     }
//                     errs() << "\n";

//                     errs() << "OUT :\n";
//                     for (Value *V : out_set) {
//                         V->print(errs());
//                         errs() << "\n";
//                     }
//                     errs() << "\n";
            
//                     if (old_in_set != in_set) {
//                         changed = true;
//                     }
//                     IN[&BB] = in_set;
//                     OUT[&BB] = out_set;
//                 }
//             }
            
//             return true;
//         }
//         std::set<Value*> computeUSE(BasicBlock &BB){
//             std::set<Value*> temp_set;
//             std::set<Value*> use_set;
//                 for (auto &I : BB) {
//                     if (auto bin_op = dyn_cast<BinaryOperator>(&I)) {

//                         Value *lop = bin_op->getOperand(0);
//                         Value *rop = bin_op->getOperand(1);
//                         if (temp_set.count(lop) == 0) {
//                             use_set.insert(lop);
//                         }
//                         if (temp_set.count(rop) == 0) {
//                             use_set.insert(rop);
//                         }
//                     }
//                     temp_set.insert(&I);
//                 }
//             return use_set;
//         }

//         std::set<Value*> computeDEF(BasicBlock &BB){
//             std::set<Value*> temp_set;
//             std::set<Value*> def_set;
            
//                 for (auto &I : BB) {
//                     if (auto bin_op = dyn_cast<BinaryOperator>(&I)) {
//                     Value *lop = bin_op->getOperand(0);
//                     Value *rop = bin_op->getOperand(1);
//                     if ((temp_set.count(lop) != 0) || (temp_set.count(rop) != 0)){
//                         def_set.insert(&I);
//                     }
//                     }
//                     temp_set.insert(&I);
//                 }
            
//             // for (Value *V : def_set) {
//             //     V->print(errs());
//             //     errs() << "\n";
//             // }
//             // errs() << "\n";
//             return def_set;
//         }
//     };
// }

// char AnticipatedExpressions::ID = 0;
// static RegisterPass<AnticipatedExpressions> X("antiexp", "Anticipated Expressions Pass");
// //Perform code hoisting
// // for (auto &I : BB) {
// //   if (auto bin_op = dyn_cast<BinaryOperator>(&I)) {
// //     Value *lhs = bin_op->getOperand(0);
// //     Value *rhs = bin_op->getOperand(1);
// //     if (in_map[&BB].count(lhs) && in_map[&BB].count(rhs)) {
// //       bool can_hoist = true;
// //       for (BasicBlock *Succ : successors(&BB)) {
// //         if (out_map[Succ].count(lhs) || out_map[Succ].count(rhs) ||
// //             def_map[Succ].count(lhs) || def_map[Succ].count(rhs)) {
// //           can_hoist = false;
// //           break;
// //         }
// //       }
// //       if (can_hoist) {
// //         I.moveBefore(&(BB.front()));
// //       }
// //     }
// //   }
// // }

namespace{
    struct AnticipatedExpressions: public FunctionPass{
        static char ID;
        AnticipatedExpressions(): FunctionPass(ID){}
        class Expression{
            public:
            Value* op1,*op2;
            Instruction* I;
            std::string opname;
            unsigned int opcode;

            Expression(){
                op1 = NULL;
                op2 = NULL;
                opcode = -1;
                opname = "";
                I = NULL;
            } 
        };

        bool isFeasibleInstruction(Instruction &I)
        {
            if(I.isBinaryOp() && !isa<StoreInst>(I) && !isa<AllocaInst>(I) && !isa<LoadInst>(I))
                return true;
            return false;
        }
        std::set<Expression *> computeExpressionBB(BasicBlock &BB){
            std::set<Expression *> expressions;
                for(Instruction &I: BB){
                    if(isFeasibleInstruction(I)){
                        Expression *expr = new Expression;
                        expr->op1 = I.getOperand(0);
                        expr->op2 = I.getOperand(1);
                        expr->opcode = I.getOpcode();
                        expr->opname = I.getOpcodeName(I.getOpcode());
                        expr->I = &I;
                        expressions.insert(expr);
                    }
            }
            return expressions;
        }

        std::set<Expression *> computeExpression(Function &F, DenseMap<Expression *, unsigned> &exToBit, unsigned k){
            std::set<Expression *> expressions;
            for(BasicBlock &BB: F){
                for(Instruction &I: BB){
                    if(isFeasibleInstruction(I)){
                        Expression *expr = new Expression;
                        expr->op1 = I.getOperand(0);
                        expr->op2 = I.getOperand(1);
                        expr->opcode = I.getOpcode();
                        expr->opname = I.getOpcodeName(I.getOpcode());
                        expr->I = &I;
                        expressions.insert(expr);
                        exToBit[expr] = k; // Assigned each expressiona unique integer
                        k++;
                    }
                }
            }
            return expressions;
        }

        bool runOnFunction(Function& F){
            // Expression to bit
            DenseMap<Expression *, unsigned> exToBit;
            unsigned expressPos = 0;

            // Compute Expression
            std::set<Expression *> expressions = computeExpression(F, exToBit, expressPos);
            unsigned int size = expressions.size();
            std::map<BasicBlock *, BitVector> UseBitMap, DefBitMap, INBitMap, OUTBitMap;

            // Compute USE and DEF
            //std::map<BasicBlock *, std::set<std::pair<Value *, std::pair<Value *, std::string>>>> useMap, defMap;
            std::map<BasicBlock *, std::set<Expression *>> useMap, defMap;
            useMap = computeUSE(F);
            defMap = computeDEF(F);
            UseBitMap = computeBIT(F,useMap, exToBit, size);
            DefBitMap = computeBIT(F, defMap, exToBit, size);

            // Initialise IN and OUT sets
            initialiseIN_OUT(F, INBitMap, OUTBitMap, size);

            //Compute IN and OUT sets
            
            bool modified = true;
            while(modified){
                modified = false;
                for(auto &BB: F){

                }
            }
            printMap(useMap, "USE", F);
            printMap(defMap, "DEF", F);
            printMapping(exToBit);
            return true;
        }

        
        // Compute BIT
        std::map<BasicBlock *, BitVector> computeBIT(Function &F, std::map<BasicBlock *, std::set<Expression *>> ds, DenseMap<Expression *, unsigned> exToBit, unsigned int size){
            std::map<BasicBlock *, BitVector> BlockBitMap;
            for (auto &BB : F) {
                BitVector helper(size, false);
                if (ds.count(&BB) == 0) {
                    BlockBitMap[&BB] = helper;
                    continue;
                }
                for (auto &use : ds[&BB]) {
                    unsigned bit = exToBit[use];
                    helper.set(bit);
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
                        Expression *expr = new Expression;
                        expr->op1 = I.getOperand(0);
                        expr->op2 = I.getOperand(1);
                        expr->opcode = I.getOpcode();
                        expr->opname = I.getOpcodeName(I.getOpcode());
                        expr->I = &I;

                        if (auto *defInst1 = dyn_cast<Instruction>(expr->op1)) {
                            if (defInst1->getParent() == &BB || definedInstructions.count(defInst1)) {
                                continue;
                            }
                        }

                        if (auto *defInst2 = dyn_cast<Instruction>(expr->op2)) {
                            if (defInst2->getParent() == &BB || definedInstructions.count(defInst2)) {
                                continue;
                            }
                        }

                        // usedExpressions.insert(std::make_pair(op1, std::make_pair(op2, I.getOpcodeName(I.getOpcode()))));
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
                            if (Inst){
                                Expression *expr = new Expression;
                                expr->op1 = I.getOperand(0);
                                expr->op2 = I.getOperand(1);
                                expr->opcode = I.getOpcode();
                                expr->opname = I.getOpcodeName(I.getOpcode());
                                expr->I = &I;
                                DefExpressions.insert(expr);
                            }
                        }
                    }
                }
                defMap[&BB] = DefExpressions;
            }
            return defMap;
        }

        void initialiseIN_OUT(Function &F, std::map<BasicBlock *, BitVector> &IN, std::map<BasicBlock *, BitVector> &OUT, unsigned size){
            for(auto &BB: F){
                IN[&BB] = computeExpressionBB(Function &F, DenseMap<Expression *, unsigned int> &exToBit, unsigned int k)
            }
        }
        // // Compute IN
        // void computeIN_OUT(Function &F){
        //     std::map<BasicBlock *, std::set<Expression*>> IN, OUT;

        //     // Initialize IN sets to universal set of Expressions
        //     for(BasicBlock &BB: F){
        //         IN[&BB] = computeExpressionBB(BB);
        //     }
            
        // }

        void printMap(std::map<BasicBlock *, std::set<Expression*>> ds, std::string s, Function &F){
            errs() << s << " \n";
            for (auto &BB : F) {
                errs() << "Basic Block " << BB.getName() << ":\n";

                if (ds.count(&BB) == 0) {
                    errs() << "No USE sets.\n";
                    continue;
                }

                for (auto &use : ds[&BB]) {
                    Value *B = use->op1;
                    Value *C = use->op2;
                    std::string opname = use->opname;
                    // if(B == D)  errs() << "True";
                    errs() << "\t" << *B << " " << opname << " " << *C << "\n";
                }
            }
            errs() << "\n";
        }

        // Print Mapping Map
        void printMapping(DenseMap<Expression *, unsigned> exToBit){
            for(const auto &pair: exToBit){
                errs() << " " << pair.second ;
            }
            errs() << "\n";
        }

    };
} //namespace

char AnticipatedExpressions::ID = 0;
static RegisterPass<AnticipatedExpressions> X("antiexp", "Anticipated Expressions Pass");

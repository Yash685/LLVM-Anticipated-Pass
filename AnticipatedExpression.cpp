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
            bool operator== (const Expression &ele) const{
                return (this->op1 == ele.op1) && (this->op2 == ele.op2) && (this->opname == ele.opname);
            }
        };

        bool isFeasibleInstruction(Instruction &I)
        {
            if(I.isBinaryOp(I.getOpcode()) && !isa<StoreInst>(I) && !isa<AllocaInst>(I) && !isa<LoadInst>(I))
                return true;
            return false;
        }
        
        // This computes universal set of expressions
        std::set<Expression *> computeExpression(Function &F, DenseMap<Expression *, unsigned> &exToBit, DenseMap<unsigned, Expression *> &BitToex, DenseMap<unsigned, std::set<BasicBlock *>> &exToBlock, unsigned k){
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
                        
                        bool f = true;
                        for(auto *ele: expressions){
                            if((*expr) == *(ele)){
                                f = false;
                                exToBlock[exToBit[expr]].insert(&BB);
                                break;
                            }
                        }
                        if(f){
                            expressions.insert(expr);
                            exToBit[expr] = k; // Assigned each expressiona unique integer
                            BitToex[k] = expr;
                            exToBlock[k].insert(&BB);
                            k++;
                        }
                    }
                }
            }
            return expressions;
        }

        bool runOnFunction(Function& F){
            // Expression to bit
            DenseMap<Expression *, unsigned> exToBit;
            DenseMap<unsigned, Expression *> BitToex;
            DenseMap<unsigned, std::set<BasicBlock *>> exToBlock;
            unsigned expressPos = 0;

            // Compute Expression
            std::set<Expression *> expressions = computeExpression(F, exToBit, BitToex, exToBlock, expressPos);
            unsigned int size = expressions.size();
            std::map<BasicBlock *, BitVector> UseBitMap, DefBitMap, INBitMap, OUTBitMap;

            // Compute USE and DEF
            //std::map<BasicBlock *, std::set<std::pair<Value *, std::pair<Value *, std::string>>>> useMap, defMap;
            std::map<BasicBlock *, std::set<Expression *>> useMap, defMap;
            useMap = computeUSE(F);
            defMap = computeDEF(F);
            UseBitMap = computeBIT(F, useMap, exToBit, expressions,size);
            DefBitMap = computeBIT(F, defMap, exToBit, expressions, size);

            // Initialise IN and OUT sets
            initialiseIN_OUT(F, INBitMap, OUTBitMap, size);

            //Compute IN and OUT sets
            
            bool modified = true;
            while(modified){
                modified = false;
                for(auto &BB: reverse(F)){
                    BitVector INBit = INBitMap[&BB];
                    BitVector OUTBit = OUTBitMap[&BB];
                    BitVector UseBit = UseBitMap[&BB];
                    BitVector DefBit = DefBitMap[&BB];
                    BitVector tempBit(size, false);
                    if(!successors(&BB).empty()){
                        OUTBit = INBitMap[*succ_begin(&BB)];
                        for(BasicBlock *succ: successors(&BB)){
                            BitVector INBit = INBitMap[succ];
                            OUTBit &= INBit;
                        }
                    }
                    
                    OUTBitMap[&BB] = OUTBit;
                    DefBit.flip();
                    OUTBit &= DefBit;
                    OUTBit|=UseBit;
                    if(!(OUTBit == INBit) ){
                        modified = true;
                    }
                    INBitMap[&BB] = OUTBit;
                }
            }
            printMap(useMap, "USE", F);
            printMap(defMap, "DEF", F);
            printMapping(exToBit);
            // errs() << "IN\n";
            // printBitMap(F, INBitMap);
            // errs() << "OUT\n";
            // printBitMap(F, OUTBitMap);
            // errs() << "USE\n";
            // printBitMap(F, UseBitMap);
            // errs() << "DEF\n";
            // printBitMap(F, DefBitMap);
            errs() << "IN\n";
            printBitMap(F, INBitMap, BitToex);
            errs() << "OUT\n";
            printBitMap(F, OUTBitMap, BitToex);
            errs() << "USE\n";
            printBitMap(F, UseBitMap, BitToex);
            errs() << "DEF\n";
            printBitMap(F, DefBitMap, BitToex);
            errs() << "USE MAP\n";
            printOGmap(F, useMap);
            errs() << "\nDEF MAP\n";
            printOGmap(F, defMap);
            printexToBlock(exToBlock);
            return true;
        }

        bool isSameInst(Instruction &I, Instruction &J){
            if(I.getOperand(0) == J.getOperand(0) && I.getOperand(1) == J.getOperand(1) && I.getOpcode() == J.getOpcode())
                return true;
            return false;
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
                        if((*use) == *(ele)){   
                            unsigned bit = exToBit[ele];
                            helper.set(bit);
                            break;
                        }
                    }
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
                       // expr->I = &I;

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
                            if (Inst && isFeasibleInstruction(*Inst)){
                                Expression *expr = new Expression;
                                expr->op1 = Inst->getOperand(0);
                                expr->op2 = Inst->getOperand(1);
                                expr->opcode = Inst->getOpcode();
                                expr->opname = Inst->getOpcodeName(Inst->getOpcode());
                                expr->I = Inst;
                                //expr->I = Inst;
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
                    // errs() << "\t" << *B << " " << opname << " " << *C << "\n";
                    errs() << *(use->I) << "\n";
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

        
        void printexToBlock(DenseMap<unsigned, std::set<BasicBlock *>> exToBlock){
            for(const auto &pair: exToBlock){
                for(auto ele: pair.second){
                    errs() << ele << " ";
                }
                errs() << "\n";
            }
            errs() << "\n";
        }

        // void printBitMap(Function &F, std::map<BasicBlock *, BitVector> bmap){
        //     for(auto &BB: F){
        //         BitVector temp = bmap[&BB];
        //         for (auto i = 0; i < temp.size(); i++) {
        //             errs() << temp[i];
        //         }
        //         errs() << "\n";
        //     }
        // }

        void printBitMap(Function &F, std::map<BasicBlock *, BitVector> bmap, DenseMap<unsigned, Expression*> BitToex){
            for(auto &BB: F){
                BitVector temp = bmap[&BB];
                for (auto i = 0; i < temp.size(); i++) {
                    errs() << temp[i];
                    if(temp[i] == 1){
                        auto ele = BitToex[i];
                        errs() << *(ele->I);
                    }
                }
                errs() << "\n";
            }
        }

        
        void printOGmap(Function &F, std::map<BasicBlock *, std::set<Expression *>> ds){
            for(auto &BB: F){
                auto temp = ds[&BB];
                for(auto expr: temp){
                    errs() << "\nOP1: " << *expr->op1;
                    errs() << "\nOP2: " << *expr->op2;
                    errs() << "\nOPName: " << expr->opname;
                }
            }
            errs() << "\n";
        }

    };
} //namespace

char AnticipatedExpressions::ID = 0;
static RegisterPass<AnticipatedExpressions> X("antiexp", "Anticipated Expressions Pass");

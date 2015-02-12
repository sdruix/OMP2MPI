#ifndef INLINE_PHASE_HPP
#define INLINE_PHASE_HPP

#include <tl-compilerphase.hpp>
#include <hlt/hlt-inline.hpp>
#include <hlt/hlt-common.hpp>
#include <tl-ast.hpp>
#include <tl-scopelink.hpp>
#include <tl-langconstruct.hpp>
#include <tl-symbol.hpp>
#include "tl-pragmasupport.hpp"
#include <cxx-utils.h>
#include <uniquestr.h>
#include <tl-source.hpp>
#include <tl-datareference.hpp>

#include "tl-omp.hpp"
#include <unordered_map>
#include "hlt/hlt-outline.hpp"

//#include "printTraverse.hpp"
using namespace TL;
using namespace TL::HLT;
using namespace std;


class TransPhase : public PragmaCustomCompilerPhase {
    struct infoVar {
        Source name;
        Source operation;
        Source type; 
        ObjectList<string> size;
        Source iterVar;
        int iterVarInOperation;
    };
public:
    TransPhase();
    virtual void run(DTO &dto);
private:
    void finalize();
    string addCommaIfNeeded(string arrayToCheck);
    Source findPrincipalIterator(AST_t varUse, string name);
    AST_t getForContextofConstruct(AST_t ast2check, ScopeLink scopeL, int exprLine, int searching_construct);
    string cleanWhiteSpaces(string toClean);
    void pragma_postorder(PragmaCustomConstruct construct);
    bool checkFor(PragmaCustomConstruct construct);
    int get_size_of_array(string name, string declaration);
    vector<infoVar> fill_vars_info(std::unordered_map <std::string,AST_t> params, TL::HLT::Outline outlineAux, PragmaCustomConstruct construct, Source initVar, Scope functionScope, Scope globalScope, int iNOUT);
    Source modifyReductionOperation(infoVar reducedVar, AST_t constructAST, PragmaCustomConstruct construct);
    AST_t _translation_unit;
    ScopeLink _scope_link;
    vector<infoVar> _reducedVars;
    vector<infoVar> _ioVars;
    vector<infoVar> _inVars;
    int _initialized;
    AST_t _initAST;
    int _num_transformed_blocks;
    int _finalized;
    int _reducedVarsIndexStart;
    int _construct_num_loop;
    int _construct_inside_bucle;
    AST_t _construct_loop;
    ObjectList<string> _privateVars;
    string _lastFunctionName;
    
    struct lastAst {
        AST_t _wherePutFinal;
        AST_t _lastModifiedAST;
        string _lastFunctionNameList;
        
    };
    vector<lastAst> _lastTransformInfo;
    //*******************
    struct use{
        int row;
        AST_t ast;
        ScopeLink sl;
        int inside_loop;
        int for_num;
        AST_t for_ast;
        AST_t for_internal_ast_last;
        AST_t for_internal_ast_first;
    };
    struct var_use{       
        use row_last_write_cpu;
        use row_last_read_cpu;
        use row_first_write_cpu;
        use row_first_read_cpu;
    }; 
    struct for_info {
        AST_t ast;
        int lineS;
        int lineF;
    };
    typedef unordered_map <string, var_use> Mymap; 
    unordered_map <string, var_use> _smart_use_table;
    std::unordered_map <std::string,AST_t> _ioParams;
    std::unordered_map <std::string,AST_t> _inParams;
    
    //****************************
    DTO _dto;
    std::vector<std::string> p_l_s;
    int _inside_loop,_for_num, _for_min_line, _pragma_lines, _notOutlined;
    AST_t _for_ast, _for_internal_ast_last, _for_internal_ast_first, _file_tree;
    void assignMasterWork(lastAst ast2Work);
    use fill_use(int line, AST_t actAst);
    int get_real_line(AST_t asT, ScopeLink scopeL, AST_t actLineAST, int update, int searching_construct);
    AST_t get_first_ast(AST_t ast, ScopeLink scopeL);
    AST_t get_last_ast(AST_t ast, ScopeLink scopeL);
    int is_inside_bucle(AST_t ast2check, ScopeLink scopeL, int exprLine, int searching_construct);
    int isReducedVar(string name);
    int isPrivateVar(string name);
    int isIOVar(string name);
    int isINVar(string name);
    int is_inside_master(AST_t ast2check, ScopeLink scopeL, int exprLine, int searching_construct);
    ObjectList<Source> splitMathExpression(Scope sC,std::string secondO);
    AST_t fill_smart_use_table(AST_t asT, ScopeLink scopeL, Scope sC, int outline_num_line, ObjectList<Symbol> prmters , int hmppOrig, int offset, AST_t prevAST);
    class TraverseASTFunctor4LocateUse : public TraverseASTFunctor {
    private:
        ScopeLink _slLU;
        bool _f_defined;
        bool _a_defined;
        
    public:
        
        TraverseASTFunctor4LocateUse(ScopeLink sl) : _slLU(sl) {};
        virtual ASTTraversalResult do_(const TL::AST_t &a) const
        {
            
            bool retBool = false;
            
            if (Expression::predicate(a)) {
                Expression expr(a, _slLU);
                if(expr.is_assignment()){
                    retBool = true;
                }
                if(expr.is_function_call()){
                    retBool = true;
                }
                
                if(expr.is_operation_assignment()){
                    retBool = true;
                }
                
                return ast_traversal_result_helper(retBool,false);
            } else {
                std::istringstream f(a.prettyprint());
                std::string line;    
                int lines=0;
                while (std::getline(f, line)) {
                    lines++;
                }
                
                if(lines==1){
                    retBool = true;
                    return ast_traversal_result_helper(retBool,false);
                } else {
                    PragmaCustomConstruct test(a,_slLU);
                    if(test.is_construct()){
                        retBool = true;
                        return ast_traversal_result_helper(retBool,false);
                    } 
                }
            }
            return ast_traversal_result_helper(false, true);
        };
    };
    class TraverseASTFunctor4Malloc : public TraverseASTFunctor {
    private:
        ScopeLink _slM;
    public:
        
        TraverseASTFunctor4Malloc(ScopeLink sl) : _slM(sl) {};
        virtual ASTTraversalResult do_(const TL::AST_t &a) const
        {
            
            if (Expression::predicate(a)) {
                Expression expr(a, _slM);
                bool retBool = false;
                bool is_assigment =expr.is_assignment();
                if(is_assigment){
                    retBool = true;
                }
                return ast_traversal_result_helper(retBool,false);
            }
            return ast_traversal_result_helper(false, true);
        };
    };
    class TraverseASTFunctor4All : public TraverseASTFunctor {
    private:
        ScopeLink _slM;
        
    public:
        TraverseASTFunctor4All(ScopeLink sl) : _slM(sl) {};
        virtual ASTTraversalResult do_(const TL::AST_t &a) const
        {
            //                    cout<<a.prettyprint()<<endl;
            return ast_traversal_result_helper(true, true);
        };
    };
    class TraverseASTFunctor4LocateFor : public TraverseASTFunctor {
    private:
        ScopeLink _slLF;
    public:
        
        TraverseASTFunctor4LocateFor(ScopeLink sl) : _slLF(sl) {};
        virtual ASTTraversalResult do_(const TL::AST_t &a) const
        {
            bool retBool = false;
            //std::cout<<"********************+"<<a.prettyprint()<<std::endl;
            if(ForStatement::predicate(a)) {
                
                retBool =true;
                return ast_traversal_result_helper(retBool,false);
            }
            if(WhileStatement::predicate(a)) {
                retBool =true;
                return ast_traversal_result_helper(retBool,false);
            }
            if(DoWhileStatement::predicate(a)) {
                retBool =true;
                return ast_traversal_result_helper(retBool,false);
            }
            return ast_traversal_result_helper(false, true);
        };
    };
    class TraverseASTFunctor4LocateOMP : public TraverseASTFunctor {
    private:
        ScopeLink _sl;
    public:
        
        TraverseASTFunctor4LocateOMP(ScopeLink sl) : _sl(sl) {};
        virtual ASTTraversalResult do_(const TL::AST_t &a) const
        {
            
            bool retBool = false;
            //                std::cout<<"a6: "<<a.prettyprint()<<"\n";  
            //                 std::cin.get();
            if (!Expression::predicate(a)) {
                std::istringstream f(a.prettyprint());
                std::string line;    
                int lines=0;
                while (std::getline(f, line)) {
                    lines++;
                }
                if(lines>1){
                    PragmaCustomConstruct test(a,_sl);
                    if(test.is_construct()){
                        //                                std::cout<<"a69: "<<a.prettyprint()<<"\n";  
                        //                                std::cin.get();
                        retBool = true;
                        return ast_traversal_result_helper(retBool,false);
                    } 
                }
            }
            return ast_traversal_result_helper(false, true);
        };
    };
    class TraverseASTFunctor4LocateIf : public TraverseASTFunctor {
    private:
        ScopeLink _sl;
    public:
        
        TraverseASTFunctor4LocateIf(ScopeLink sl) : _sl(sl) {};
        virtual ASTTraversalResult do_(const TL::AST_t &a) const
        {
            
            bool retBool = false;

            if (IfStatement::predicate(a)) {
                retBool = true;
                return ast_traversal_result_helper(retBool,false);
                    
            }
            return ast_traversal_result_helper(false, true);
        };
    };
};



#endif // OMP_TO_MPI_PHASE


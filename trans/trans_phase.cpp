#include "trans_phase.hpp"
#include "FunctionDefinitionPred.hpp"
#include "FunctionCallsPred.hpp"
#include <stdlib.h>
#include "hlt/hlt-common.hpp"
#include "../../omp_to_hmpp/inline/inline_phase.hpp"
#include "tl-omp.hpp"
#include <iostream>
#include <fstream>
#include <limits>
#include "regex.h"


#include <bits/basic_string.h>

using namespace TL;
using namespace TL::HLT;
using namespace std;

TransPhase::TransPhase() : PragmaCustomCompilerPhase("omp") {
    
    register_construct("parallel");
    register_construct("for");
    register_construct("schedule");
    register_construct("atomic");
    register_construct("master");
    register_construct("barrier");
    register_construct("critical");
    register_directive("check");
    register_directive("schedule");
    register_directive("for check");
    register_directive("for private");
    register_directive("for threadprivate");
    on_directive_post["parallel"].connect(functor(&TransPhase::pragma_postorder, *this));
    _ATAG = "ATAG";
    _RTAG = "RTAG";
    _WTAG = "WTAG";
    _FTAG = "FTAG";
    _SWTAG = "SWTAG";
    _FRTAG = "FRTAG";
    _FWTAG = "FWTAG";
    _withMemoryLimitation = 0;
    _oldMPIStyle = 1;
    _secureWrite = 0;
    _workWithCopiesOnSlave = 0;
    _smartUploadDownload = 0;
    _fullArrayReads = 1;
    _fullArrayWrites =1;
    _divideWork = 1;
    _expandFullArrayReads = 1;
    
}

void TransPhase::run(DTO& dto) {
    _dto=dto;
    vector<string> keys;
    keys =dto.get_keys();
    
    _translation_unit = dto["translation_unit"];
    _scope_link = dto["scope_link"];  
    defineVars();
    
    if(_divideWork)
        divideTask();
    PragmaCustomCompilerPhase::run(dto);
    finalize();
    
    
    
}
void TransPhase::defineVars() {
    _statVar = "stat";
    int num = 0;
    while(isExistingVariable(_statVar,_translation_unit,_scope_link)){
        _statVar = "stat"+num;
        num++;
    }
    _sizeVar = "size";
    num = 0;
    while(isExistingVariable(_sizeVar,_translation_unit,_scope_link)){
        _sizeVar = "size"+num;
        num++;
    }
    _myidVar = "myid";
    num = 0;
    while(isExistingVariable(_myidVar,_translation_unit,_scope_link)){
        _myidVar = "myid"+num;
        num++;
    }
    _timeStartVar = "timeStart";
    num = 0;
    while(isExistingVariable(_timeStartVar,_translation_unit,_scope_link)){
        _timeStartVar = "timeStart"+num;
        num++;
    }
    _timeFinishVar = "timeFinish";
    num = 0;
    while(isExistingVariable(_timeFinishVar,_translation_unit,_scope_link)){
        _timeFinishVar = "timeFinish"+num;
        num++;
    }
    _argcVar = "argcVar";
    num = 0;
    while(isExistingVariable(_argcVar,_translation_unit,_scope_link)){
        _argcVar = "argcVar"+num;
        num++;
    }
    _argvVar = "argvVar";
    num = 0;
    while(isExistingVariable(_argvVar,_translation_unit,_scope_link)){
        _argvVar = "argvVar"+num;
        num++;
    }
    _partSizeVar = "partSize";
    num = 0;
    while(isExistingVariable(_partSizeVar,_translation_unit,_scope_link)){
        _partSizeVar = "partSize"+num;
        num++;
    }
    _offsetVar = "offset";
    num = 0;
    while(isExistingVariable(_offsetVar,_translation_unit,_scope_link)){
        _offsetVar = "offset"+num;
        num++;
    }
    _followINVar = "followIN";
    num = 0;
    while(isExistingVariable(_followINVar,_translation_unit,_scope_link)){
        _followINVar = "followIN"+num;
        num++;
    }
    _sourceVar = "source";
    num = 0;
    while(isExistingVariable(_sourceVar,_translation_unit,_scope_link)){
        _sourceVar = "source"+num;
        num++;
    }
    _killedVar = "killed";
    num = 0;
    while(isExistingVariable(_killedVar,_translation_unit,_scope_link)){
        _killedVar = "killed"+num;
        num++;
    }
    _toVar = "to";
    num = 0;
    while(isExistingVariable(_toVar,_translation_unit,_scope_link)){
        _toVar = "to"+num;
        num++;
    }
    _fromVar = "from";
    num = 0;
    while(isExistingVariable(_fromVar,_translation_unit,_scope_link)){
        _fromVar = "from"+num;
        num++;
    }
    _coordVectorVar = "coordVector";
    num = 0;
    while(isExistingVariable(_coordVectorVar,_translation_unit,_scope_link)){
        _coordVectorVar = "coordVector"+num;
        num++;
    }
}
void TransPhase::divideTask() {
    ObjectList<Symbol> allSym = _scope_link.get_scope(_translation_unit).get_all_symbols(false);
    ObjectList<Symbol> functionsWithConstructs;
    for(int i =0; i <allSym.size();++i){
        if(allSym[i].is_function()) {
            if(!allSym[i].get_point_of_definition().prettyprint().empty()) {
                
                TransPhase::TraverseASTFunctor4LocateOMP expr_traverse(_scope_link);
                ObjectList<AST_t> expr_list = allSym[i].get_point_of_definition().depth_subtrees(expr_traverse);
                if(expr_list.size()>0){
                    functionsWithConstructs.push_back(allSym[i]);
                }
            } 
        }
        //cout<<i<<": "<<allSym[i].get_point_of_declaration().prettyprint()<<endl;
    }
    
    for(int i =0; i <functionsWithConstructs.size();++i){
        FunctionDefinition fD(functionsWithConstructs[i].get_point_of_declaration(),_scope_link);
        //cout<<fD.get_function_body().get_ast()<<endl;
        //cin.get();
        assignMasterWork(fD.get_function_body().get_ast(), functionsWithConstructs, fD.get_function_symbol().get_name());
    }
    //    cin.get();
    
}

void TransPhase::assignMasterWork(AST_t functionAST, ObjectList<Symbol> functionsWithOMP, string functionName) {
    
    TraverseASTFunctor4All expr_traverse(_scope_link);
    ObjectList<AST_t> expr_list = functionAST.depth_subtrees(expr_traverse);
    ObjectList<Symbol> allSymbols = _scope_link.get_scope(functionAST).get_all_symbols(false);
    Source masterWork;
    AST_t masterWorkAST, ast2follow;
    Source initASTSource;
    initASTSource <<"int "<<_myidVar<<";\n"
            << "MPI_Status "<<_statVar<<";"
            "int "<<_sizeVar<<";"
            "int *"<<_argcVar<<"=NULL;"
            "char *** "<<_argvVar<<"=NULL;"
            "MPI_Init("<<_argcVar<<","<<_argvVar<<");"
            "MPI_Comm_size(MPI_COMM_WORLD,&"<<_sizeVar<<");"
            "MPI_Comm_rank(MPI_COMM_WORLD,&"<<_myidVar<<");"
            ;
    AST_t initAST = initASTSource.parse_statement(functionAST, _scope_link);
    masterWork << "{"<<initAST.prettyprint();
    _initializedFunctions[functionName]=initAST;
    int opened = 0;
    int lastLine = 0;
    for (int l = 0;l < expr_list.size(); l++) {
        //        cout<<l<<endl;
        Expression expr(expr_list[l], _scope_link);
        if(expr.is_function_call()) {
            cout<<"function Call"<<endl;
            
            Symbol fSym = expr.get_called_entity();
            if(fSym.is_valid()) {
                //                    cout<< fSym.get_name() << endl;
                int f = 0;
                for(int i = 0; i<functionsWithOMP.size(); ++i) {
                    if(fSym == functionsWithOMP[i]) {
                        if(opened>0) {
                            //                                if(opened==1)
                            //                                    masterWork << "int test=0;";
                            masterWork << "}\n";
                            opened = 0;
                        }
                        masterWork  << addCommaIfNeeded(expr_list[l].prettyprint())<<"\n";
                        expr_list[l].remove_in_list();
                        lastLine = expr_list[l].get_line();
                        f = 1;
                    } 
                }
                if(!f) {
                    if(expr_list[l].get_line()>lastLine) {
                        
                        //                            cout<<expr_list[l].prettyprint()<<endl;
                        lastLine = expr_list[l].get_line();
                        if(opened==0) {
                            masterWork << "if("<<_myidVar<<" == 0) {\n";
                            
                        }
                        opened++;
                        masterWork << (expr_list[l].prettyprint())<<"\n";
                        expr_list[l].remove_in_list();
                    }
                }
            } else {
                if(expr_list[l].get_line()>lastLine ) {
                    //                        cout<<"NV:"<<expr_list[l].prettyprint()<<endl;
                    lastLine = expr_list[l].get_line();
                    if(opened==0) {
                        masterWork << "if("<<_myidVar<<" == 0) {\n";
                        
                    }
                    opened++;
                    masterWork << addCommaIfNeeded(expr_list[l].prettyprint())<<"\n";
                    expr_list[l].remove_in_list();
                }
            }
            //
        } else if(expr_list[l].prettyprint().find("return ")!=0) {
            //                    cout<<expr_list[l].get_line()<<endl;
            int realLine = get_real_line(functionAST, _scope_link, expr_list[l],1,0,0);
            if(expr_list[l].is_valid() && expr_list[l].get_line()>lastLine 
                    && (!is_inside_bucle(expr_list[l],_scope_link,realLine,0) 
                    || ForStatement::predicate(expr_list[l]) 
                    || WhileStatement::predicate(expr_list[l])
                    || DoWhileStatement::predicate(expr_list[l]))) {
                PragmaCustomConstruct test(expr_list[l],expr.get_scope_link());
                int check = 0;
                if(test.is_construct()) {
                    
                    TL::PragmaCustomClause check_clause = test.get_clause("check");
                    if(check_clause.is_defined()) {
                        cout<<"OMP check"<<endl;
                        check = 1;
                        if(opened>0) {
                            //                                       if(opened==1)
                            //                                        masterWork << "int test=0;";
                            masterWork << "}\n";
                            opened = 0;
                        }
                        masterWork << addCommaIfNeeded(expr_list[l].prettyprint())<<"\n";
                    } else {
                        cout<<"OMP no check"<<endl;
                        if(opened==0) {
                            masterWork << "if("<<_myidVar<<" == 0) {\n";
                            
                        }
                        opened++;
                        masterWork << addCommaIfNeeded(expr_list[l].prettyprint());
                        //                                   cout<<"ACCEPTED NOT CHECK CONSTRUCT: ("<<expr_list[l].get_line()<<")"<<expr_list[l].prettyprint()<<endl;
                        
                        
                    }
                    expr_list[l].remove_in_list();
                    //                              cout<<lastLine<<endl;
                    //AST_t forAST = ;
                    AST_t lastA = get_last_ast(test.get_statement().get_ast(), test.get_scope_link());
                    
                    while(ForStatement::predicate(lastA)) {
                        ForStatement fS(lastA,test.get_scope_link());
                        cout<<fS.get_loop_body().prettyprint()<<endl;
                        lastA = get_last_ast(fS.get_loop_body().get_ast(), test.get_scope_link());
                    }
                    
                    //cout<<lastA.prettyprint()<<endl;
                    lastLine = lastA.get_line();
                    //                              cout<<lastLine<<endl;
                    //cout<<std::string(masterWork)<<endl;
                    //                              cin.get();
                    //break;
                } else if(ForStatement::predicate(expr_list[l])|| WhileStatement::predicate(expr_list[l])
                        || DoWhileStatement::predicate(expr_list[l])) {
                    if(opened==0) {
                        masterWork << "if("<<_myidVar<<" == 0) {\n";
                    }
                    opened++;
                    masterWork << addCommaIfNeeded(expr_list[l].prettyprint());
                    //                            cout<<"Loop"<<endl;
                    //                            cout<<lastLine;
                    AST_t lastA = get_last_ast(expr_list[l], test.get_scope_link());
                    cout<<lastA.prettyprint()<<endl;
                    lastLine = lastA.get_line();
                    //                            cout<<lastLine<<endl;
                    //                            cin.get();
                } else if((cleanWhiteSpaces(expr_list[l].prettyprint()).find_first_of(" ")>=0 &&
                        cleanWhiteSpaces(expr_list[l].prettyprint()).find_first_of(" ")<cleanWhiteSpaces(expr_list[l].prettyprint()).length())) {
                    Expression expr(expr_list[l],_scope_link);
                    if(isDeclarationLine(expr_list[l],expr.get_enclosing_function().get_scope().get_all_symbols(false),_scope_link))  {
                        if(opened>0) {
                            //                                     if(opened==1)
                            //                                    masterWork << "int test=0;";
                            masterWork << "}";
                            opened = 0;
                        }
                        masterWork << addCommaIfNeeded(expr_list[l].prettyprint())<<"\n";
                        expr_list[l].remove_in_list();              
                    } else {
                        if(opened==0) {
                            masterWork << "if("<<_myidVar<<" == 0) {\n";
                        }
                        opened++;
                        masterWork << addCommaIfNeeded(expr_list[l].prettyprint());
                        expr_list[l].remove_in_list();
                    }
                    lastLine = expr_list[l].get_line();
                } 
                //                        cout<<"BYE"<<endl;
                
            } 
        } else {
            //                    cout<<"DISCARTED: "<<expr_list[l].prettyprint()<<endl;
            if(expr_list[l].get_line()>lastLine)
                lastLine = expr_list[l].get_line();
            //  
        } 
        
        
        
        
        
    }
    
    
    masterWork << "}}";
    //        cout<< std::string(masterWork)<< endl;
    //        cin.get();
    masterWorkAST = masterWork.parse_statement(functionAST,_scope_link);  
    functionAST.replace_with(masterWorkAST);
    //                cout<<"FINAL AST: "<<ast2follow.prettyprint()<<endl;
    //                
    
}
int TransPhase::isDeclarationLine(AST_t ast, ObjectList<Symbol> allSym, ScopeLink sL) {
    int l = ast.get_line();
    
    for (int i=0; i<allSym.size();++i){
        //        cout<<i<<endl;
        if(allSym[i].is_defined()) {
            if(allSym[i].is_function()) {
                FunctionDefinition fD(allSym[i].get_point_of_definition().get_enclosing_function_definition(),sL);
                if(isDeclarationLine(ast, fD.get_function_body().get_scope().get_all_symbols(false),fD.get_scope_link()))
                    return 1;
            } else {
                if(ast.prettyprint().compare(allSym[i].get_point_of_definition().prettyprint()) == 0 && !ast.prettyprint().empty()) {
                    //                    cout<<"AST line: "<<l<<endl;
                    //                    cin.get();
                    return 1;
                }
            }
        }
        
    }
    return 0;
}

void TransPhase::pragma_postorder(PragmaCustomConstruct construct) {
    
    
    string pragmaInstruction = construct.get_pragma_line().prettyprint(false);
    FunctionDefinition function_def = construct.get_enclosing_function();
    Symbol function_sym = function_def.get_function_symbol();
    Scope functionScope = function_def.get_function_body().get_scope();
    Scope globalScope = function_def.get_scope();
    cout<<"OMP("<<pragmaInstruction<<" in: "<<function_sym.get_name()<<")"<<endl;
    TL::PragmaCustomClause check_clause = construct.get_clause("check");
    if(check_clause.is_defined()) { 
        TraverseASTFunctor4LocateFunction expr_traverseFunc(construct.get_scope_link());
        ObjectList<AST_t> expr_listFunc = construct.get_statement().get_ast().depth_subtrees(expr_traverseFunc);
        if(expr_listFunc.size()>0) {
            cerr<<"Function Found in construct. Please use Inline Phase before execute OMP2MPI"<<endl;
            cin.get();
            exit(-1);
            for(int f = 0; f<expr_listFunc.size();++f) {
                Expression exprF(expr_listFunc[f],construct.get_scope_link());
            }
            //InlinePhase.inlineFunction(exprF.get_called_entity(),exprF);
            
            // a.find_functions(construct.get_statement().get_ast(), construct.get_scope_link());
            
        }
        
        _num_transformed_blocks++;
        _file_tree = construct.get_statement().get_ast().get_enclosing_global_tree();
        Statement statement = construct.get_statement();
        
        _ioVars.clear();
        _inVars.clear();
        _ioParams.clear();
        _inParams.clear();
        _smart_use_table.clear();
        _uploadedVars.clear();
        int block_line = get_real_line(construct.get_enclosing_function().get_ast(), construct.get_enclosing_function().get_scope_link(), construct.get_ast(),0,0,1);
        // cin.get();
        //int block_line = construct.get_ast().get_line();
        //            cout<<"S: "<<statement.prettyprint()<<endl;
        //            
        TL::HLT::Outline outlineAux(construct.get_enclosing_function().get_scope_link(), statement);
        
        
        
        
        
        _prmters = outlineAux.get_parameter_list();
        
        if(_prmters.size()==0) {         
            _prmters =outlineAux.recomputeParameters(); // Error in compute_referenced_entities has to repeat this function
        }
        //prmters = outlineAux.get_parameter_list();
        //  cout<<"Hola"<<endl;
        //  
        AST_t prevAST;
        
        _construct_inside_bucle = is_inside_bucle(construct.get_ast(),construct.get_enclosing_function().get_scope_link(),block_line, 1);
        _construct_num_loop = _for_num;
        _construct_loop = _for_ast;
        AST_t minAST = NULL;
        int minLine= std::numeric_limits<int>::max();
        for(int i = 0; i<_prmters.size();++i)
            cout<<_prmters[i].get_name()<<endl;
        if(_prmters.size()>0) {            
            cout<<"Finding "<<_prmters.size()<<" parameters"<<endl;
            //cout<<construct.get_enclosing_function().get_ast().prettyprint()<<endl;
            
            
            AST_t last_ast = fill_smart_use_table(function_def.get_function_body().get_ast(), function_def.get_function_body().get_scope_link(), function_def.get_scope(), block_line, _prmters,2,0, prevAST);
            // cout<<last_ast.prettyprint()<<endl;
            //
            for (Mymap::const_iterator it = _smart_use_table.begin(); 
                    it != _smart_use_table.end(); ++it) {
                if(it->second.row_last_read_cpu.row!=0) 
                    std::cout<<it->first<< "- LR(CPU)("<<it->second.row_last_read_cpu.for_num<<"): "<<it->second.row_last_read_cpu.row<<" -> "<<it->second.row_last_read_cpu.ast.prettyprint()<<endl;
                if(it->second.row_last_write_cpu.row!=0) 
                    std::cout<<it->first<< "- LW(CPU)("<<it->second.row_last_write_cpu.for_num<<"): "<<it->second.row_last_write_cpu.row<<" -> "<<it->second.row_last_write_cpu.ast.prettyprint()<<endl;
                if(it->second.row_first_read_cpu.row!=0) {
                    std::cout<<it->first<< "- FR(CPU)("<<it->second.row_first_read_cpu.for_num<<"): "<<it->second.row_first_read_cpu.row<<" -> "<<it->second.row_first_read_cpu.ast.prettyprint()<<endl;
                    
                }
                minLine = block_line;
                minAST = construct.get_ast();
                
                if(it->second.row_first_write_cpu.row!=0) 
                    std::cout<<it->first<< " -FW (CPU)("<<it->second.row_first_write_cpu.for_num<<"): "<<it->second.row_first_write_cpu.row<<" -> "<<it->second.row_first_write_cpu.ast.prettyprint()<<endl;
                
                std::cout<<"---------------------------"<<endl;
            }
            
            //                 
            cout<<"Context Analized"<<endl;
            cout<<"Getting out params"<<endl;
            //                        cout<<"HI"<<endl;
            _ioParams = outlineAux.get_parameter_io(construct.get_scope());
            //                        cout<<"BYE"<<endl;
            //                        cin.get();
            cout<<"This block has "<<_ioParams.size()<<" OUT variables"<<endl;
            cout<<"Getting in params"<<endl;
            _inParams = outlineAux.get_parameter_in(construct.get_scope());
            cout<<"This block has "<<_inParams.size()<<" IN variables"<<endl;
            
        }
        
        
        //            cout<<"InVars:"<<endl;
        //            typedef std::unordered_map <std::string,AST_t> iter4in; 
        //            for (iter4in::const_iterator it = _inParams.begin(); it != _inParams.end(); ++it) {
        //                cout<<it->first<<": "<<it->second.prettyprint()<<endl;
        //            }
        //            
        //_inParams =
        
        Source commented_loop;
        PragmaCustomClause red_clause = construct.get_clause("reduction");
        
        PragmaCustomClause static_clause = construct.get_clause("schedule");
        if(_lastFunctionName.compare(function_sym.get_name())!=0) {
            _initialized = 0;
            _lastFunctionName = function_sym.get_name();
        }
        int staticC = 0;
        cout<<"Studing static clause"<<endl;
        if(static_clause.is_defined()) {
            ObjectList<std::string> static_args = static_clause.get_arguments();
            for (ObjectList<std::string>::iterator it = static_args.begin(); it != static_args.end(); it++) {
                string actArg(*it);
                if(actArg.compare("static") == 0) {
                    staticC = 1;
                    cout<< "Static Transformation"<<endl;
                } else if(actArg.compare("guided") == 0) {
                    cout<<"Guided Transformation";
                    staticC = 2;
                } else if(actArg.compare("dynamic") == 0){
                    cout<< "Dynamic Transformation"<<endl;
                } else {
                    cout<< "Static in :"<<actArg<<endl;
                    cout<< "Not possible to work with harcoded number of processors"<<endl;
                    cin.get();
                }
            }
            
        } else {
            cout<< "Dynamic Transformation"<<endl;
        }
        Source arg;
        
        
        _reducedVarsIndexStart = _reducedVars.size();
        _reducedVars.clear();
        Source varInitialization;
        
        //Initialization Common in all
        TL::Statement function_body = function_def.get_function_body();
        Source mpiFixStructurePart1, mpiFixStructurePart2, constructASTS;
        Source mpiVariantStructurePart1, mpiVariantStructurePart2, mpiVariantStructurePart3;
        int varDefinedInFor = 1;
        Source initVar, initValue, initType, initS;
        string varToWork, conditionToWork;
        _isForDirective = 0;
        AST_t newASTStart;
        if(checkDirective(construct,"for")) {
            _isForDirective = 1;
            ForStatement fS(construct.get_statement());
            AST_t pragma2mpi = fS.get_loop_body().get_ast();
            construct.get_ast().replace_with(pragma2mpi);
            Expression iterating = fS.get_iterating_expression();
            Expression condition = fS.get_iterating_condition();
            AST_t init = fS.get_iterating_init();
            cout<<"Analyzing for expression"<<endl;
            Expression exprInit(init, fS.get_scope_link());
            
            initS << exprInit.prettyprint();
            initVar << fS.get_induction_variable().prettyprint();
            string tempInitValue = std::string(initS).substr(std::string(initS).find_first_of("=")+1,std::string(initS).length());
            if(tempInitValue.find_first_of(";")>=0 && tempInitValue.find_first_of(";")<tempInitValue.length()) {
                cout<<"; found"<<endl;
                tempInitValue = tempInitValue.substr(0,tempInitValue.find_first_of(";"));
            }
            initValue << tempInitValue;
            //            cout<< tempInitValue<<endl;
            //            
            string type = std::string(initS).substr(0, std::string(initS).find_first_of(std::string(initVar)));
            
            varDefinedInFor = 1;
            if(type.empty()) {
                
                type = fS.get_induction_variable().get_symbol().get_point_of_declaration().prettyprint();
                type = type.substr(0, type.find_first_of(" "));
                varDefinedInFor=0;
            } 
            
            initType << type;
            conditionToWork = condition.prettyprint();
            
            
            if(conditionToWork.find_first_of(";")>=0 && conditionToWork.find_first_of(";")<conditionToWork.length()){
                conditionToWork.substr(0,conditionToWork.find_first_of(";")-1);
            }
            if(conditionToWork.find_first_of("=")>=0 && conditionToWork.find_first_of("=")<conditionToWork.length()){
                varToWork = conditionToWork.substr(0, conditionToWork.find_first_of("="));
                conditionToWork = conditionToWork.substr(conditionToWork.find_first_of("=")+1,conditionToWork.length());
                
            }
            if(conditionToWork.find_first_of("<")>=0 && conditionToWork.find_first_of("<")<conditionToWork.length()){
                varToWork = conditionToWork.substr(0, conditionToWork.find_first_of("<"));
                conditionToWork =conditionToWork.substr(conditionToWork.find_first_of("<")+1,conditionToWork.length());
                
            }
            if(conditionToWork.find_first_of(">")>=0 && conditionToWork.find_first_of(">")<conditionToWork.length()){
                varToWork = conditionToWork.substr(0, conditionToWork.find_first_of("<"));
                conditionToWork =conditionToWork.substr(conditionToWork.find_first_of(">")+1,conditionToWork.length());
                
            }   
        }
        
        
        //conditionToWork = cleanWhiteSpaces(conditionToWork);
        cout<<"Analyzing Reduction Clause"<<endl;
        if (red_clause.is_defined()) {
            ObjectList<std::string> red_args = red_clause.get_arguments();
            for (ObjectList<std::string>::iterator it = red_args.begin(); it != red_args.end(); it++) {
                string argument(*it);
                string act, operation;
                while(argument.find_first_of(":")>=0 && argument.find_first_of(":")<argument.length()) {
                    operation = argument.substr(0,argument.find_first_of(":"));
                    //std::cout <<"n: "<<num<<std::endl;
                    if(argument.find_first_of(",")>=0 && argument.find_first_of(",")<argument.length()) {
                        act = argument.substr(argument.find_first_of(":")+1,argument.find_first_of(",")-1);
                        argument = argument.substr(argument.find_first_of(",")+1,argument.length());
                    } else {
                        act = argument.substr(argument.find_first_of(":")+1,argument.length());
                        argument = argument.substr(argument.find_first_of(":")+1,argument.length());
                    }
                    infoVar newR;
                    newR.name << act;
                    newR.operation << operation;
                    // cout << "N: -"<< std::string(newR.name) <<"- O: -"<< std::string(newR.operation) <<"-"<< endl;
                    Symbol findedS = functionScope.get_symbol_from_name(newR.name);
                    string declaration;
                    if(!findedS.is_valid()){
                        findedS = globalScope.get_symbol_from_name(newR.name);
                        if(findedS.is_valid()){
                            declaration = std::string(findedS.get_type().get_declaration(globalScope,newR.name));
                            declaration = declaration.substr(0, declaration.find(newR.name));
                        }
                    } else {
                        declaration = std::string(findedS.get_type().get_declaration(functionScope,newR.name));
                        declaration = declaration.substr(0, declaration.find(newR.name));
                    }
                    declaration = cleanWhiteSpaces(declaration);
                    
                    //cout<< "FS: -"<<declaration<<"-"<<endl;
                    newR.type <<  declaration;
                    _reducedVars.push_back(newR);
                    
                    
                }
                
            } 
            
            for(int i = 0; i<_reducedVars.size(); ++i){
                varInitialization<< _reducedVars[i].type <<" work"<<_reducedVarsIndexStart+i<<";";  
            }
            
            if(varDefinedInFor)
                varInitialization<<initType<<" "<<varToWork<<"="<<initValue<<";";
            
        } 
        
        cout<<"Analyzing Shared Clause"<<endl;
        PragmaCustomClause shared_clause = construct.get_clause("shared");
        if (shared_clause.is_defined()) {
            commented_loop
                    << "// Arguments found in shared clausule: \n";
            cout << "// Arguments found in shared clausule: " << endl;
            ObjectList<Expression> shared_arguments = shared_clause.get_expression_list();
            for (ObjectList<Expression>::iterator it = shared_arguments.begin(); it != shared_arguments.end(); it++) {
                Expression argument(*it);
                commented_loop
                << "//  - " << argument.prettyprint() << "\n";
                cout << "//  - " << argument.prettyprint() << endl;
            }
        }
        cout<<"Analyzing Private Clause"<<endl;
        PragmaCustomClause private_clause = construct.get_clause("private");
        if (private_clause.is_defined()) {
            commented_loop
                    << "// Arguments found in private clausule: \n";
            cout << "// Arguments found in private clausule: " << endl;
            ObjectList<Expression> private_arguments = private_clause.get_expression_list();
            for (ObjectList<Expression>::iterator it = private_arguments.begin(); it != private_arguments.end(); it++) {
                Expression argument(*it);
                _privateVars.push_back(argument.prettyprint());
            }
        }
        PragmaCustomClause tPrivate_clause = construct.get_clause("threadprivate");
        if (tPrivate_clause.is_defined()) {
            commented_loop
                    << "// Arguments found in threadprivate clausule: \n";
            cout << "// Arguments found in threadprivate clausule: " << endl;
            ObjectList<Expression> private_arguments = tPrivate_clause.get_expression_list();
            for (ObjectList<Expression>::iterator it = private_arguments.begin(); it != private_arguments.end(); it++) {
                Expression argument(*it);
                _privateVars.push_back(argument.prettyprint());
            }
        }
        PragmaCustomClause fPrivate_clause = construct.get_clause("firstprivate");
        if (fPrivate_clause.is_defined()) {
            commented_loop
                    << "// Arguments found in firstprivate clausule: \n";
            cout << "// Arguments found in firstprivate clausule: " << endl;
            ObjectList<Expression> private_arguments = fPrivate_clause.get_expression_list();
            for (ObjectList<Expression>::iterator it = private_arguments.begin(); it != private_arguments.end(); it++) {
                Expression argument(*it);
                _privateVars.push_back(argument.prettyprint());
            }
        }
        PragmaCustomClause lPrivate_clause = construct.get_clause("lastprivate");
        if (lPrivate_clause.is_defined()) {
            commented_loop
                    << "// Arguments found in lastprivate clausule: \n";
            cout << "// Arguments found in lastprivate clausule: " << endl;
            ObjectList<Expression> private_arguments = lPrivate_clause.get_expression_list();
            for (ObjectList<Expression>::iterator it = private_arguments.begin(); it != private_arguments.end(); it++) {
                Expression argument(*it);
                _privateVars.push_back(argument.prettyprint());
            }
        }
        cout<<"Filling OUT vars info"<<endl;
        _ioVars = fill_vars_info(_ioParams, outlineAux,  construct, initVar, functionScope, globalScope, 1); 
        cout <<"** OUT VARS **"<<endl;
        for(int i =0;i<_ioVars.size();++i){
            cout<<std::string(_ioVars[i].name)<<endl;
        }
        cout<<"Filling IN vars info"<<endl;
        _inVars = fill_vars_info(_inParams, outlineAux,  construct, initVar, functionScope, globalScope, 0); 
        cout <<"** IN VARS **"<<endl;
        for(int i =0;i<_inVars.size();++i){
            cout<<std::string(_inVars[i].name)<<endl;
        }
        
        
        //        cin.get();
        
        // 
        
        cout<<"Creating initializations"<<endl;
        if(!_initialized) {
            if(!_divideWork) {
                varInitialization<<
                        "MPI_Status "<<_statVar<<";"
                        "int "<<_sizeVar <<", "<<_myidVar<<";"
                        "int *"<<_argcVar<<"=NULL;"
                        "char *** "<<_argvVar<<"=NULL;"
                        "MPI_Init("<<_argcVar<<","<<_argvVar<<");"
                        "MPI_Comm_size(MPI_COMM_WORLD,&"<<_sizeVar<<");"
                        "MPI_Comm_rank(MPI_COMM_WORLD,&"<<_myidVar<<");"
                        ;
            }
            varInitialization<< "const int "<<_FTAG<<" = 0;"
                    "const int "<<_ATAG<<" = 1;"
                    "const int "<<_RTAG<<" = 2;"
                    "const int "<<_WTAG<<" = 3;"
                    "const int "<<_SWTAG<<" = 4;"
                    "const int "<<_FRTAG<<" = 5;"
                    "const int "<<_FWTAG<<" = 6;"
                    "double "<<_timeStartVar<<" = MPI_Wtime();"
                    "double "<<_timeFinishVar<<";";
            
            _maxManagedVarsCoor = 0;
            for(int j = 0; j<_inVars.size();++j) {  
                //cout<<std::string(_inVars[j].name)<<" S: "<<_inVars[j].size.size()<< endl;
                if(_inVars[j].size.size()>_maxManagedVarsCoor) {
                    _maxManagedVarsCoor = _inVars[j].size.size();
                    
                }
            }
            for(int j = 0; j<_ioVars.size();++j) {  
                //cout<<std::string(_inVars[j].name)<<" S: "<<_inVars[j].size.size()<< endl;
                if(_ioVars[j].size.size()>_maxManagedVarsCoor) {
                    _maxManagedVarsCoor = _ioVars[j].size.size();
                    
                }
            }
            //
            varInitialization << "int "<<_coordVectorVar << _num_transformed_blocks <<"["<<_maxManagedVarsCoor<<"];";
            //                if(_maxManagedVarsCoor>1) {
            //                    varInitialization << "int c0";
            //                    for(int n = 1; n<_maxManagedVarsCoor;++n)
            //                        varInitialization << ", c"<<n;
            //                    varInitialization <<";";
            //                }
        }
        
        //             cout<<std::string(varInitialization)<<endl;
        //             cin.get();
        
        
        //                cout<< "Array"<<endl;
        
        
        
        
        // cout<<conditionToWork<<endl;
        //
        stringstream maxSTemp;
        maxSTemp <<"("<<conditionToWork<<"- ("<<std::string(initValue)<<"))";
        string maxS = maxSTemp.str();
        //                  string maxS = "-1";
        //                  for(int i = 0; i<_ioVars.size(); ++i){
        //                      if(_ioVars[i].size>atoi(maxS.c_str()))
        //                          maxS=_ioVars[i].size;
        //                  }
        
        if(!_initialized) {
            if(_construct_inside_bucle && _isForDirective) {
                varInitialization << "int "<<_partSizeVar<<", "<<_offsetVar<<";";
            } else if(_isForDirective){
                varInitialization << "int "<<_partSizeVar<<" = ("<<maxS<<")/ ("<<_sizeVar<<"-1) > 0 ? ("<<maxS<<")/ ("<<_sizeVar<<"-1) : 1;";
                varInitialization << "int "<<_offsetVar<<";";
                //varInitialization << "int "<<_partSizeVar<<" = ("<<maxS<<") / 100000 * "<<_sizeVar<<"), "<<_offsetVar<<";";
            }
        } else {
            if(_isForDirective)
                varInitialization << _partSizeVar<<" = ("<<maxS<<")/ ("<<_sizeVar<<"-1) > 0 ? ("<<maxS<<")/ ("<<_sizeVar<<"-1) : 1;";
            varInitialization << "int "<<_coordVectorVar << _num_transformed_blocks <<"["<<_maxManagedVarsCoor<<"];";
        }
        
        
        TraverseASTFunctor4LocateUse expr_traverse(_scope_link);
        ObjectList<AST_t> expr_list = function_body.get_ast().depth_subtrees(expr_traverse);
        AST_t initalizationAST = varInitialization.parse_statement(function_body.get_ast(), function_body.get_scope_link());
        AST_t astToAttach;
        //                cout<< emptyAst.prettyprint()<<endl;
        if(!_initialized) {
            
            ObjectList<Symbol> allSymbols = functionScope.get_all_symbols(false);
            
            for(int j = 0; j<expr_list.size() ;++j ){
                int finded=0;
                //                    cout<<expr_list[j].prettyprint()<<endl;
                for(int i = 0; i<allSymbols.size();++i){
                    //cout<<"S: "<<allSymbols[i].get_point_of_definition().prettyprint()<<endl;
                    if(expr_list[j].prettyprint().compare(allSymbols[i].get_point_of_definition().prettyprint())==0) {   
                        finded = 1;
                        break;
                    }  
                }
                if(!finded) {
                    
                    int astToAppendLine = get_real_line(construct.get_enclosing_function().get_ast(),construct.get_enclosing_function().get_scope_link(), expr_list[j],1,0,0);
                    //astToAppendLine += _num_transformed_blocks;
                    
                    if(block_line>=astToAppendLine) {
                        
                        if(_construct_inside_bucle) {
                            astToAttach = _construct_loop;
                            Source partSizeSource;
                            if(_isForDirective) {
                                partSizeSource << _partSizeVar<<" = ("<<maxS<<")/ ("<<_sizeVar<<"-1) > 0 ? ("<<maxS<<")/ ("<<_sizeVar<<"-1) : 1;"; //<< "int coordVector" << _num_transformed_blocks <<"["<<_maxManagedVarsCoor<<"];";
                                construct.get_ast().prepend(partSizeSource.parse_statement(function_body.get_ast(), function_body.get_scope_link()));
                            }
                        } else {
                            astToAttach = construct.get_ast();
                            // cout<<"Prepend to2: "<<astToAttach.prettyprint()<<endl;  
                        }
                        astToAttach.prepend(initalizationAST);
                        
                    }  else {
                        astToAttach = expr_list[j];
                        astToAttach.append(initalizationAST);
                        //                            cout<<"Append to: "<<astToAttach.prettyprint()<<endl;  
                    }
                    break;
                }
            }
            _initialized =1;
            
        } else {
            
            astToAttach = _lastTransformInfo[_lastTransformInfo.size()-1]._lastModifiedAST;
            //                cout<<astToAttach<<endl;
            //                cin.get();
            astToAttach.append(initalizationAST);            
        }
        // cout<<astToAttach.prettyprint()<<endl;
        // 
        // 
        if(_isForDirective) {
            cout<<"Generating MPI Master code"<<endl;
            mpiFixStructurePart1 << "if("<<_myidVar<<" == 0) {\n ";
            if(_oldMPIStyle)
            {
                useOldStyle(staticC, mpiVariantStructurePart1, mpiVariantStructurePart2, mpiVariantStructurePart3, 
                        maxS, initVar, functionScope, initValue, 
                        conditionToWork, mpiFixStructurePart1, mpiFixStructurePart2, function_body,
                        construct, constructASTS, initType);
            } else {
                if(staticC!=0) {
                    
                    mpiVariantStructurePart1 << "for (int "<<_toVar<<" =1;"<<_toVar<<"<"<<_sizeVar<<";++"<<_toVar<<") {";
                    
                    mpiVariantStructurePart1 <<"if("<<_toVar<<"!="<<_sizeVar<<"-1) {";
                    mpiVariantStructurePart1 <<_partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1);";
                    if(_inVars.size()!=0)
                        mpiVariantStructurePart1       << _offsetVar<<" = ("<<_partSizeVar<<" * ("<<_toVar<<"-1))+"<<initValue<<";"
                                << "} else {";
                    
                    mpiVariantStructurePart1  << _partSizeVar<<" = ("<<maxS<<"/ ("<<_sizeVar<<"-1)) + ("<<maxS <<"%"<<"("<<_sizeVar<<"-1)) ;";
                    if(_inVars.size()!=0)
                        mpiVariantStructurePart1 << _offsetVar<<" = (" << maxS << "/ ("<<_sizeVar<<"-1) * ("<<_toVar<<"-1))+"<<initValue<<";"
                                << "}";
                    
                    mpiVariantStructurePart1 << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT,"<<_toVar<<","<<_ATAG<<",MPI_COMM_WORLD);";
                    mpiVariantStructurePart1 << generateMPIVariableMessagesSend(_inVars,initVar,functionScope,_toVar,_offsetVar, 1);
                    
                    
                    mpiVariantStructurePart1 << "}";
                    mpiVariantStructurePart1 << "for(int "<<_fromVar<<" = 1; "<<_fromVar<<"<"<<_sizeVar<<";++"<<_fromVar<<") { while(1) {";
                    mpiVariantStructurePart1 << "MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT,"<<_fromVar<<",MPI_ANY_TAG,MPI_COMM_WORLD, &"<<_statVar<<");";
                    mpiVariantStructurePart1 << handleMemory(_fromVar);
                    int maxDim=-1;
                    for(int t=0;t<_ioVars.size();++t)    
                        if(maxDim<_ioVars[t].size.size())
                            maxDim=_ioVars[t].size.size();
                    
                    mpiVariantStructurePart1<<" else if ("<<_statVar<<".MPI_TAG == "<<_ATAG<<") {";
                    
                    
                    mpiVariantStructurePart1 << "if("<<_fromVar<<"!="<<_sizeVar<<"-1) {"
                            << _partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1);";
                    if(maxDim>0) 
                        mpiVariantStructurePart1    <<_offsetVar<<" = ("<<_partSizeVar<<" * ("<<_fromVar<<"-1))+"<<initValue<<";";
                    
                    mpiVariantStructurePart1    << "} else {"
                            << _partSizeVar<<" = ("<<maxS<<"/ ("<<_sizeVar<<"-1)) + ("<<maxS <<"%"<<"("<<_sizeVar<<"-1)) ;";
                    if(maxDim>0) 
                        mpiVariantStructurePart1    <<_offsetVar<<" = (" << maxS << "/ ("<<_sizeVar<<"-1) * ("<<_fromVar<<"-1))+"<<initValue<<";";
                    mpiVariantStructurePart1    << "}";
                    
                    if(!_withMemoryLimitation) {
                        for(int i = 0; i<_ioVars.size(); ++i){
                            string upperType = std::string(_ioVars[i].type);
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            stringstream varSent, size;
                            
                            
                            
                            varSent << std::string(_ioVars[i].name)<<"["<<_offsetVar<<"]";
                            size << _partSizeVar;
                            for(int x=1; x<_ioVars[i].size.size();++x) {
                                size<<" * " <<_ioVars[i].size[x];
                            }
                            
                            
                            
                            if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                                mpiVariantStructurePart1 << "MPI_Recv(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_fromVar<<","<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                            } else {
                                mpiVariantStructurePart1 << "MPI_Recv(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<","<<_fromVar<<","<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                            }
                            
                        }
                    } else {
                        
                        for(int i = 0; i<_ioVars.size(); ++i){
                            if(_ioVars[i].size.size()==0) {
                                string upperType = std::string(_inVars[i].type);
                                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                                mpiVariantStructurePart1 << "MPI_Recv(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<","<<_fromVar<<","<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                            }
                        }
                        
                        
                    }
                    mpiVariantStructurePart1<<"MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_fromVar<<","<<_FTAG<<",MPI_COMM_WORLD);";
                    mpiVariantStructurePart1 << "break; }";
                    mpiVariantStructurePart1 << "} }";
                    
                    
                } else {
                    
                    mpiVariantStructurePart1 << "int "<<_followINVar<<" = "<<initValue<<"; int "<<_killedVar<<" = 0;"
                            << "for (int "<<_toVar<<"=1; "<<_toVar<<"<"<<_sizeVar<<"; ++"<<_toVar<<") {"
                            << "MPI_Send(&"<<_followINVar<<", 1, MPI_INT, "<<_toVar<<", "<<_ATAG<<", MPI_COMM_WORLD);"
                            << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_toVar<<", "<<_ATAG<<", MPI_COMM_WORLD);";
                    //                    cout<<"HI!"<<endl;
                    mpiVariantStructurePart1 << generateMPIVariableMessagesSend(_inVars,initVar,functionScope,_toVar,_followINVar,0);
                    //                    cout<<"HI"<<endl;
                    //                    cin.get();
                    
                    mpiVariantStructurePart1 << _followINVar<<" += "<<_partSizeVar<<";"
                            << "}"
                            << " while(1){"
                            << "MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");"
                            << "int "<<_sourceVar<<" = "<<_statVar<<".MPI_SOURCE;";
                    //if(_maxManagedVarsCoor>0)
                    mpiVariantStructurePart1 << handleMemory(_sourceVar)<< " else ";
                    mpiVariantStructurePart1<<"if ("<<_statVar<<".MPI_TAG == "<<_ATAG<<") {"
                            << "MPI_Recv(&"<<_offsetVar<<", 1, MPI_INT, "<<_sourceVar<<", ATAG, MPI_COMM_WORLD, &"<<_statVar<<");";
                    if(!_withMemoryLimitation) {
                        for(int i = 0; i<_ioVars.size(); ++i){
                            string upperType = std::string(_ioVars[i].type);
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            stringstream varSent, size;
                            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar) || _ioVars[i].size.size()<1) {
                                
                                
                                varSent << std::string(_ioVars[i].name)<<"["<<_offsetVar<<"]";
                                size << _partSizeVar;
                                for(int x=1; x<_ioVars[i].size.size();++x) {
                                    size<<" * " <<_ioVars[i].size[x];
                                }
                                
                                
                                
                                if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                                    mpiVariantStructurePart1 << "MPI_Recv(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_sourceVar<<","<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                                } else {
                                    mpiVariantStructurePart1 << "MPI_Recv(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<","<<_sourceVar<<","<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                                }
                            }
                            
                        }
                    } else {
                        
                        for(int i = 0; i<_ioVars.size(); ++i){
                            if(_ioVars[i].size.size()==0) {
                                string upperType = std::string(_inVars[i].type);
                                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                                mpiVariantStructurePart1 << "MPI_Recv(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<","<<_sourceVar<<","<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                            }
                        }
                        
                        
                    }
                    
                    for(int i = 0; i<_reducedVars.size(); ++i){
                        string upperType = std::string(_reducedVars[i].type);
                        std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                        mpiVariantStructurePart1<< "MPI_Recv(&work"<<_reducedVarsIndexStart+i<<", 1, MPI_"<<upperType<<", "<<_sourceVar<<", MPI_ANY_TAG, MPI_COMM_WORLD,&"<<_statVar<<");";
                        mpiVariantStructurePart1<< _reducedVars[i].name<<" "<<_reducedVars[i].operation<<"= work"<<_reducedVarsIndexStart+i<<";";
                    }
                    
                    mpiVariantStructurePart1 << "if (("<<_followINVar<<"+"<<_partSizeVar<<") <"<<conditionToWork<<") {"
                            << "MPI_Send(&"<<_followINVar<<", 1, MPI_INT, "<<_sourceVar<<", "<<_ATAG<<", MPI_COMM_WORLD);"
                            << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_sourceVar<<", "<<_ATAG<<", MPI_COMM_WORLD);";
                    mpiVariantStructurePart1 << generateMPIVariableMessagesSend(_inVars,initVar,functionScope,_sourceVar,_followINVar,0);
                    
                    //mpiVariantStructurePart1 << "} else if(("<<conditionToWork<<"-"<<_followINVar<<")< "<<_partSizeVar<<" && ("<<conditionToWork<<"-"<<_followINVar<<")>0) {"//MODIFIED
                    mpiVariantStructurePart1 << "} else if(("<<conditionToWork<<"-"<<_followINVar<<")>0) {"
                            << _partSizeVar<<" ="<<conditionToWork <<"-"<<_followINVar<<";"
                            << "MPI_Send(&"<<_followINVar<<", 1, MPI_INT, "<<_sourceVar<<", "<<_ATAG<<", MPI_COMM_WORLD);"
                            << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_sourceVar<<", "<<_ATAG<<", MPI_COMM_WORLD);";
                    mpiVariantStructurePart1 << generateMPIVariableMessagesSend(_inVars,initVar,functionScope,_sourceVar,_followINVar,0);
                    mpiVariantStructurePart1 << "}";
                    mpiVariantStructurePart1 << "if(("<<_followINVar<<"+"<<_partSizeVar<<") > "<<conditionToWork<<") {"
                            << "MPI_Send(&"<<_offsetVar<<", 1, MPI_INT, "<<_sourceVar<<", "<<_FTAG<<", MPI_COMM_WORLD);"
                            << ""<<_killedVar<<"++;"
                            << " }"
                            <<_followINVar<<"+="<<_partSizeVar<<";"
                            << "if("<<_killedVar<<"=="<<_sizeVar<<"-1) {"
                            << "break; }"
                            <<"}}";
                }   
                
                mpiFixStructurePart1 <<mpiVariantStructurePart1;
                
                mpiFixStructurePart1 <<"}";
                //pragma2mpi.prepend(ASTmpiFixStructurePart1);
                
                AST_t ast2start = mpiFixStructurePart1.parse_statement(function_body.get_ast(), function_body.get_scope_link());
                if(_construct_inside_bucle){
                    newASTStart = ast2start;
                } else {
                    newASTStart = ast2start;
                }
                construct.get_ast().prepend(ast2start);
                for(int k=0 ;k<_prmters.size();k++) {
                    cout<<"k:"<<_prmters[k].get_name()<<endl;
                }
                
                Source mpiVariantStructurePart4, mpiVariantStructurePart5, mpiVariantStructurePart6;
                
                cout<<"Generating MPI Slave code"<<endl;;
                if(staticC!=0) {
                    if(_inVars.size()!=0){
                        mpiVariantStructurePart4 
                                <<"if("<<_myidVar<<"!="<<_sizeVar<<"-1) {"<<_partSizeVar<<" = (" << maxS << ") / ("<<_sizeVar<<" - 1); "<<_offsetVar<<" = ("<<_partSizeVar<<" * ("<<_myidVar<<"-1)) +"<<initValue
                                <<";} else {"<<_offsetVar<<" = (" << maxS << "/ ("<<_sizeVar<<"-1) * ("<<_myidVar<<"-1))+"<<initValue<<";}";
                    }
                    mpiVariantStructurePart4 << "while(1){"
                            << "MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT, 0, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");"
                            << "int idxForReadWriteSwitch;";
                    for(int i = 0; i<_inVars.size(); ++i){
                        //if(isINVar(std::string(_inVars[i].name)) && !_withMemoryLimitation) {
                        if(!_withMemoryLimitation) {
                            transferInfo up;
                            up.name = std::string(_inVars[i].name);
                            up.start = _offsetVar;
                            up.end = _offsetVar + " + " +_partSizeVar;
                            _uploadedVars.push_back(up);
                            Source numberOfPointers;
                            string nameCopy= std::string(_inVars[i].name);
                            if(_workWithCopiesOnSlave)
                                nameCopy = std::string(_inVars[i].name)+"_MPICOPY";
                            
                            string upperType = std::string(_inVars[i].type);
                            
                            
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            stringstream varSent, size, iterators;
                            
                            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                                
                                varSent << nameCopy;
                                if(_workWithCopiesOnSlave)
                                    varSent <<"[0]";
                                else
                                    varSent <<"["<<_offsetVar<<"]";
                                
                                for(int x=0; x<_inVars[i].size.size();++x) {
                                    
                                    numberOfPointers <<"*";
                                    
                                    if(x>0) {
                                        size<<" * " <<_inVars[i].size[x];
                                        iterators <<"["<<_inVars[i].size[x]<<"]";
                                    } else {
                                        iterators <<"["<<_partSizeVar<<"]";
                                    }
                                }
                                
                            }
                            else {
                                varSent << nameCopy;
                                stringstream ss;
                                for(int x = 0;x<_inVars[i].size.size();++x) {
                                    if(x == 0) {
                                        ss << _inVars[i].size[x];
                                        iterators <<"["<<_partSizeVar<<"]";
                                    } else {
                                        ss << "* "<<_inVars[i].size[x];                                
                                        iterators <<"["<<_inVars[i].size[x]<<"]";
                                    }
                                }
                                size << ss.str();
                                
                            }
                            if(_inVars[i].size.size()>0) {
                                if(_workWithCopiesOnSlave)
                                    mpiVariantStructurePart6 <<std::string(_inVars[i].type)<<" "<< nameCopy<<iterators.str() <<"; ";
                            }
                            //
                            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                                mpiVariantStructurePart6<<"MPI_Recv(&"<<varSent.str()<<", "<<_partSizeVar<<" "<<size.str()<<", MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD, &"<<_statVar<<");";
                            } else {
                                mpiVariantStructurePart6<<"MPI_Recv(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD, &"<<_statVar<<");";
                            }
                        } 
                        
                    }
                    for (int i = 0; i<_ioVars.size();++i){
                        if(_ioVars[i].size.size()>0 && 
                                !isUploadedVar(std::string(_ioVars[i].name)) &&
                                _workWithCopiesOnSlave &&
                                iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar) &&
                                !_withMemoryLimitation) {
                            stringstream iterators;
                            for(int x=0; x<_ioVars[i].size.size();++x) {
                                if(x>0) {
                                    iterators <<"["<<_ioVars[i].size[x]<<"]";
                                } else {
                                    iterators <<"["<<_partSizeVar<<"]";
                                }
                            }
                            string nameCopy = std::string(_ioVars[i].name)+"_MPICOPY";
                            
                            mpiVariantStructurePart6 <<std::string(_ioVars[i].type)<<" "<< nameCopy<<iterators.str() <<"; ";
                            
                        }
                    }
                    if(_withMemoryLimitation){
                        for(int i = 0; i<_inVars.size(); ++i){
                            if(_inVars[i].size.size()==0) {
                                string upperType = std::string(_inVars[i].type);
                                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                                mpiVariantStructurePart6 << "MPI_Recv(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<",0,"<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                            }
                        }                    
                    }
                    for(int i = 0; i<_reducedVars.size(); ++i){
                        string upperType = std::string(_reducedVars[i].type);
                        std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                        mpiVariantStructurePart6 << "MPI_Recv(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<",MPI_ANY_SOURCE,MPI_ANY_TAG,MPI_COMM_WORLD,&"<<_statVar<<");";
                        
                        
                    }
                    
                    //                    for(int i = 0; i<_reducedVars.size(); ++i){
                    //                        string upperType = std::string(_reducedVars[i].type);
                    //                        std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                    //                        mpiVariantStructurePart2<< "MPI_Send(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<", 0, 0, MPI_COMM_WORLD);";                       
                    //                    }  
                    mpiVariantStructurePart2 << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, 0, "<<_ATAG<<", MPI_COMM_WORLD);";
                    if(_withMemoryLimitation) {
                        for(int i = 0; i<_ioVars.size(); ++i){
                            if(_ioVars[i].size.size()==0) {
                                string upperType = std::string(_inVars[i].type);
                                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                                mpiVariantStructurePart2 << "MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<",0,"<<_ATAG<<",MPI_COMM_WORLD);";
                            }
                        }
                    } else {
                        for(int i = 0; i<_ioVars.size(); ++i){
                            string upperType = std::string(_ioVars[i].type);
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            //                                                    cout<<std::string(_ioVars[i].name)<<" size "<<_ioVars[i].size.size()<<endl;
                            //                                                    cin.get();
                            if(_ioVars[i].size.size()>0) {
                                
                                string nameCopy= std::string(_ioVars[i].name);
                                if(_workWithCopiesOnSlave)
                                    nameCopy = std::string(_ioVars[i].name)+"_MPICOPY";
                                
                                stringstream varSent, size;
                                if(iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar) || _ioVars[i].size.size()<1) {
                                    varSent << nameCopy;
                                    size << _partSizeVar;
                                    if(_workWithCopiesOnSlave)
                                        varSent <<"[0]";
                                    else
                                        varSent <<"["<<_offsetVar<<"]";
                                    for(int x=0; x<_ioVars[i].size.size();++x) {
                                        if(x>0)
                                            size<<" * " <<_ioVars[i].size[x];
                                    }
                                    
                                    
                                    if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                                        mpiVariantStructurePart2<<"MPI_Send(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";
                                    } else {
                                        mpiVariantStructurePart2<<"MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";
                                    }
                                }
                            } else {
                                mpiVariantStructurePart2<< "MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";    
                            }
                        }
                    }
                    
                } else {
                    
                    mpiVariantStructurePart4<<"while(1){"
                            "MPI_Recv(&"<<_offsetVar<<", 1, MPI_INT, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");";
                    mpiVariantStructurePart6 << "MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT, 0, "<<_ATAG<<", MPI_COMM_WORLD, &"<<_statVar<<");";
                    
                    mpiVariantStructurePart6 << "int idxForReadWriteSwitch;";
                    for(int i = 0; i<_inVars.size(); ++i){
                        //if(isINVar(std::string(_inVars[i].name)) && !_withMemoryLimitation) {
                        if(!_withMemoryLimitation) {
                            Source numberOfPointers;
                            string nameCopy= std::string(_inVars[i].name);
                            if(_workWithCopiesOnSlave)
                                nameCopy = std::string(_inVars[i].name)+"_MPICOPY";
                            
                            string upperType = std::string(_inVars[i].type);
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            stringstream varSent, size, iterators;
                            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar) || _inVars[i].size.size()<1) {
                                transferInfo up;
                                up.name = std::string(_inVars[i].name);
                                up.start = _offsetVar;
                                up.end = _offsetVar + " + " + _partSizeVar;
                                _uploadedVars.push_back(up);
                                
                                
                                varSent << nameCopy;
                                if(_workWithCopiesOnSlave)
                                    varSent <<"[0]";
                                else
                                    varSent <<"["<<_offsetVar<<"]";
                                for(int x=0; x<_inVars[i].size.size();++x) {
                                    
                                    numberOfPointers <<"*";
                                    
                                    if(x>0) {
                                        size<<" * " <<_inVars[i].size[x];
                                        iterators <<"["<<_inVars[i].size[x]<<"]";
                                    } else {
                                        iterators <<"["<<_partSizeVar<<"]";
                                    }
                                }
                                
                                
                            }
                            
                            
                            //
                            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar) || _inVars[i].size.size()<1) {
                                if(_inVars[i].size.size()>0)
                                    if(_workWithCopiesOnSlave)
                                        mpiVariantStructurePart6 <<std::string(_inVars[i].type)<<" "<< nameCopy<<iterators.str() <<"; ";
                                if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                                    mpiVariantStructurePart6<<"MPI_Recv(&"<<varSent.str()<<", "<<_partSizeVar<<" "<<size.str()<<", MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD, &"<<_statVar<<");";
                                } else {
                                    mpiVariantStructurePart6<<"MPI_Recv(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD, &"<<_statVar<<");";
                                }
                            }
                            
                        } 
                        
                    }
                    for (int i = 0; i<_ioVars.size();++i){
                        if(_ioVars[i].size.size()>0 && 
                                !isUploadedVar(std::string(_ioVars[i].name)) &&
                                _workWithCopiesOnSlave &&
                                iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar) &&
                                !_withMemoryLimitation) {
                            stringstream iterators;
                            for(int x=0; x<_ioVars[i].size.size();++x) {
                                if(x>0) {
                                    iterators <<"["<<_ioVars[i].size[x]<<"]";
                                } else {
                                    iterators <<"["<<_partSizeVar<<"]";
                                }
                            }
                            string nameCopy = std::string(_ioVars[i].name)+"_MPICOPY";
                            
                            mpiVariantStructurePart6 <<std::string(_ioVars[i].type)<<" "<< nameCopy<<iterators.str() <<"; ";
                            
                        }
                    }
                    
                    if(_withMemoryLimitation){
                        for(int i = 0; i<_inVars.size(); ++i){
                            if(_inVars[i].size.size()==0) {
                                string upperType = std::string(_inVars[i].type);
                                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                                mpiVariantStructurePart6 << "MPI_Recv(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<",0,"<<_ATAG<<",MPI_COMM_WORLD, &"<<_statVar<<");";
                            }
                        }                    
                    }
                    for(int i=0;i<_reducedVars.size();++i) {
                        if(std::string(_reducedVars[i].operation).compare("+") == 0 || std::string(_reducedVars[i].operation).compare("-") == 0) {
                            mpiVariantStructurePart6<<_reducedVars[i].name << " = "<< "0;";
                        }else{
                            mpiVariantStructurePart6<<_reducedVars[i].name << " = "<< "1;";
                        }
                    }
                    //  cout<<"V: "<<std::string(mpiVariantStructurePart6)<<endl;
                    //  
                    mpiVariantStructurePart2 << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, 0, "<<_ATAG<<", MPI_COMM_WORLD);"
                            "MPI_Send(&"<<_offsetVar<<",1, MPI_INT, 0, "<<_ATAG<<", MPI_COMM_WORLD);";
                    if(_withMemoryLimitation) {
                        for(int i = 0; i<_ioVars.size(); ++i){
                            if(_ioVars[i].size.size()==0) {
                                string upperType = std::string(_inVars[i].type);
                                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                                mpiVariantStructurePart2 << "MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<",0,"<<_ATAG<<",MPI_COMM_WORLD);";
                            }
                        }
                    } else {
                        for(int i = 0; i<_ioVars.size(); ++i){
                            string upperType = std::string(_ioVars[i].type);
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            //                                                    cout<<std::string(_ioVars[i].name)<<" size "<<_ioVars[i].size.size()<<endl;
                            //                                                    cin.get();
                            if(_ioVars[i].size.size()>0) {
                                
                                string nameCopy= std::string(_ioVars[i].name);
                                if(_workWithCopiesOnSlave)
                                    nameCopy = std::string(_ioVars[i].name)+"_MPICOPY";
                                
                                stringstream varSent, size;
                                if(iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar) || _ioVars[i].size.size()<1) {
                                    varSent << nameCopy;
                                    size << _partSizeVar;
                                    if(_workWithCopiesOnSlave)
                                        varSent <<"[0]";
                                    else
                                        varSent <<"["<<_offsetVar<<"]";
                                    for(int x=0; x<_ioVars[i].size.size();++x) {
                                        if(x>0)
                                            size<<" * " <<_ioVars[i].size[x];
                                    }
                                    
                                    
                                    if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                                        mpiVariantStructurePart2<<"MPI_Send(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";
                                    } else {
                                        mpiVariantStructurePart2<<"MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";
                                    }
                                }
                            } else {
                                mpiVariantStructurePart2<< "MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";    
                            }
                        }
                    }
                    
                    
                }
                
                mpiFixStructurePart2 << "if("<<_myidVar<<" !=0){ "
                        <<mpiVariantStructurePart4
                        <<"if("<<_statVar<<".MPI_TAG == "<<_ATAG<<") {"
                        ;
                //                if(_withMemoryLimitation) {
                
                //                } else {
                //                    mpiFixStructurePart2 <<mpiVariantStructurePart6<< "for("<<initType<<" "<<initVar<<" = 0; "<<initVar<<"<partSize;++"<<initVar<<")";
                //                }
                Source constructASTwithKeys;
                constructASTwithKeys << "{"<<construct.get_ast().prettyprint()<<"}";
                //cout<<"1: "<<construct.get_ast().prettyprint()<<endl;
                
                construct.get_ast().replace_with(constructASTwithKeys.parse_statement(functionScope,function_def.get_function_body().get_scope_link()));
                //                cout<<"2: "<<construct.get_ast().prettyprint()<<endl;
                //                cin.get();
                //
                completeLoopsInAST(construct.get_ast(), function_def.get_function_body().get_scope_link());
                constructASTS = transformConstructAST(construct, function_def.get_function_body().get_scope_link(), functionScope, initVar); 
                mpiFixStructurePart2 <<mpiVariantStructurePart6<<_aditionalLinesRead<<"for("<<initType<<" "<<initVar<<" = "<<_offsetVar<<"; "<<initVar<<"<"<<_offsetVar<<"+"<<_partSizeVar<<";++"<<initVar<<")";
                mpiFixStructurePart2 <<"{"<<constructASTS<<"}"<<_aditionalLinesWrite<<mpiVariantStructurePart2;
                
                //mpiFixStructurePart2 << generateMPIVariableMessagesSend(_ioVars,initVar,functionScope,"0",_offsetVar,1);
                //                if(!_withMemoryLimitation){
                
                for(int i = 0; i<_reducedVars.size(); ++i){
                    string upperType = std::string(_reducedVars[i].type);
                    std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                    mpiFixStructurePart2<< "MPI_Send(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<", 0, "<<_ATAG<<", MPI_COMM_WORLD);";    
                    // constructASTS = modifyReductionOperation(_reducedVars[i], construct.get_ast(), construct);
                }  
                
                mpiFixStructurePart2 <<"} else if("<<_statVar<<".MPI_TAG == "<<_FTAG<<") {";
                mpiFixStructurePart2<<mpiVariantStructurePart3<<"break;}"
                        "} }";
                
                AST_t ASTmpiFixStructurePart2 = mpiFixStructurePart2.parse_statement(function_body.get_ast(), function_body.get_scope_link());
                construct.get_ast().replace_with(ASTmpiFixStructurePart2);
            }
            putBarrier(minLine, staticC, block_line, construct, function_sym, function_body, minAST, newASTStart);
            
            
        }else if(checkDirective(construct,"barrier")) {
            //            cout<<"barrier"<<endl;
            //            cin.get();
            Source newSource;
            
            newSource << "int thisIsANoopVariable2ReplacePreviousOpenMPDirective"<<_num_transformed_blocks<<";";
            newASTStart = newSource.parse_statement(construct.get_ast(),_scope_link);
            construct.get_ast().replace_with(newASTStart);
            putBarrier(minLine, staticC, block_line, construct, function_sym, function_body, minAST, newASTStart);
        } else if(checkDirective(construct,"master")) {
            
            cout<<"Master"<<endl;
            AST_t pragma2mpi = construct.get_statement().get_ast();
            Source newSource;
            newSource << "if ("<<_myidVar<<" ==0) {"<<pragma2mpi.prettyprint()<<"}";
            newASTStart = newSource.parse_statement(construct.get_ast(),_scope_link);
            construct.get_ast().replace_with(newASTStart);
            putBarrier(minLine, staticC, block_line, construct, function_sym, function_body, minAST, newASTStart);
            
        } else {
            cout<<"Parallel"<<endl;
            AST_t new_block;
            Source new_blockS;
            int preHMPPstart=0;
            string clauses;
            std::string fixedS,checkS;
            clauses =  construct.get_pragma_line().prettyprint();
            if(clauses.find("check")>=0 && clauses.find("check")<clauses.length()) {
                checkS=" check";
                preHMPPstart=1;
            }
            if(clauses.find("fixed")>=0 && clauses.find("fixed")<clauses.length()) {
                fixedS= clauses.substr(clauses.find("fixed"), clauses.find_last_of(")"));
                preHMPPstart=1;
            }
            if(preHMPPstart) {
                construct.get_ast().replace(construct.get_statement().get_ast());
                TraverseASTFunctor4LocateOMP expr_traverse(construct.get_scope_link());
                ObjectList<AST_t> expr_list = construct.get_ast().depth_subtrees(expr_traverse);
                int l=0;
                ObjectList<PragmaCustomConstruct> constructList;
                for (ObjectList<AST_t>::iterator it = expr_list.begin();it != expr_list.end(); it++, l++) {
                    
                    Expression expr(expr_list[l], construct.get_scope_link());
                    PragmaCustomConstruct test(expr.get_ast(),expr.get_scope_link());
                    
                    
                    if(test.is_construct()){
                        constructList.push_back(test);
                        Statement statement = test.get_statement();
                        clauses =  test.get_pragma_line().prettyprint();
                        string checkSinside,fixedSinside;
                        if(clauses.find("check")>=0 && clauses.find("check")<clauses.length()) {
                            if(fixedS.empty())
                                checkSinside=" check";    
                            clauses  = clauses.substr(0,clauses.find("check")-1);
                        }
                        if(clauses.find("fixed")>=0 && clauses.find("fixed")<clauses.length()) {
                            //                    if(!preHMPPstart)
                            fixedSinside= clauses.substr(clauses.find("fixed"), clauses.find_last_of(")"));
                            clauses  = clauses.substr(0,clauses.find("fixed")-1);
                        }
                        int outline_line = get_real_line(construct.get_enclosing_function().get_ast(), construct.get_enclosing_function().get_scope_link(), construct.get_ast(),1,0,0);
                        TL::HLT::Outline outlineAux(statement.get_scope_link(), statement,outline_line);
                        Source sharedVars,privateVars, s,sep,f;
                        s<<"shared(";
                        sep <<", ";
                        f <<") ";
                        sharedVars = outlineAux.get_parameter_io(statement.get_scope(),s,sep,f);
                        sharedVars = std::string(sharedVars).substr(std::string(sharedVars).find(", s")+1,std::string(sharedVars).length());
                        std::string astText= expr.get_ast().prettyprint(true);
                        int num = 0;
                        size_t forIndx=-1;
                        if(clauses.find("private")<0 || clauses.find("private")>clauses.length()) {
                            privateVars << "private(";
                            while(astText.find("for")>=0 && astText.find("for")<astText.length()){
                                astText = astText.substr(astText.find("for")+4,astText.length());
                                size_t spaces;
                                Source stringSpaces;
                                spaces = astText.substr(0,astText.find("(")).length();
                                for(int s=0;s<(int)spaces;s++){
                                    stringSpaces <<" ";
                                }
                                if(astText.substr(0,astText.find_first_of("(")).compare(std::string(stringSpaces))==0){
                                    astText = astText.substr(astText.find_first_of("(")+1,astText.length());
                                    
                                    std::string express;
                                    express = astText.substr(0,astText.find("="));
                                    // std::cout<<"0: "<<express<<std::endl;
                                    while(express.find(" ")==0) {
                                        express = express.substr(express.find(" ")+1,express.length());
                                        //  std::cout<<"1: "<<express<<std::endl;
                                    }
                                    while(express.find_last_of(" ")==express.length()-1){
                                        express = express.substr(0,express.find_last_of(" "));
                                        //  std::cout<<"2: "<<express<<std::endl;
                                    }
                                    
                                    if(express.find_last_of(" ")>0 && express.find_last_of(" ")<express.length()) {
                                        express= express.substr(express.find_last_of(" ")+1,express.length());
                                        //   std::cout<<"3: "<<express<<std::endl;
                                    }
                                    
                                    if(num==0)
                                        privateVars << express;
                                    else
                                        privateVars <<", "<<express;
                                    num++;
                                }
                            }
                            
                            
                            
                            privateVars<<")";
                        }
                        //                std::cout<<"Shared: "<<std::string(sharedVars)<<endl;
                        Source newSource;
                        if(fixedSinside.empty() && checkSinside.empty()) {
                            newSource<<"#pragma omp parallel "<<clauses<<sharedVars<<privateVars<<fixedS<<checkS<<"\n"<<statement.prettyprint()<<"\n";
                        }
                        if(!fixedSinside.empty() && checkSinside.empty()) {
                            newSource<<"#pragma omp parallel "<<clauses<<sharedVars<<privateVars<<fixedSinside<<"\n"<<statement.prettyprint()<<"\n";
                        }
                        if(fixedSinside.empty() && !checkSinside.empty()) {
                            newSource<<"#pragma omp parallel "<<clauses<<sharedVars<<privateVars<<checkSinside<<"\n"<<statement.prettyprint()<<"\n";
                        }
                        
                        AST_t newAst = newSource.parse_statement(construct.get_ast(), construct.get_enclosing_function().get_scope_link());
                        expr.get_ast().replace(newAst);
                        
                    }
                }
                int n =0;
                for(ObjectList<PragmaCustomConstruct>::iterator itC = constructList.begin(); itC!=constructList.end();itC++,n++) {    
                    pragma_postorder(constructList[n]);
                }
                
                AST_t translation_unit = _dto["translation_unit"]; 
                
            } else {
                construct.get_ast().replace(construct.get_statement().get_ast());               
                TraverseASTFunctor4LocateOMP expr_traverse(construct.get_scope_link());
                ObjectList<AST_t> expr_list = construct.get_ast().depth_subtrees(expr_traverse);
                int l=0;
                ObjectList<PragmaCustomConstruct> constructList;
                
                for (int l=0; l<expr_list.size();l++) {
                    
                    Expression expr(expr_list[l], construct.get_scope_link());
                    PragmaCustomConstruct test(expr.get_ast(),expr.get_scope_link());
                    
                    if(test.is_construct()){
                        Statement statement = test.get_statement();
                        //                cout<<"Statement: "<<statement.prettyprint()<<endl;
                        clauses =  test.get_pragma_line().prettyprint();
                        
                        string checkSinside,fixedSinside;
                        int inside = 0;
                        if(clauses.find("check")>=0 && clauses.find("check")<clauses.length()) {
                            clauses  = clauses.substr(0,clauses.find("check")-1);
                            inside =1;
                        }
                        if(clauses.find("fixed")>=0 && clauses.find("fixed")<clauses.length()) {
                            fixedSinside= clauses.substr(clauses.find("fixed"), clauses.find_last_of(")"));
                            clauses  = clauses.substr(0,clauses.find("fixed")-1);
                            inside=1;
                        }
                        if(inside) {
                            constructList.push_back(test);
                        }
                        _outline_line = get_real_line(construct.get_enclosing_function().get_ast(), construct.get_enclosing_function().get_scope_link(), construct.get_ast(),1,0,0);
                        TL::HLT::Outline outlineAux(statement.get_scope_link(), statement,_outline_line);
                        Source sharedVars,privateVars, s,sep,f;
                        s<<"shared(";
                        sep <<", ";
                        f <<") ";
                        sharedVars = outlineAux.get_parameter_io(statement.get_scope(),s,sep,f);
                        sharedVars = std::string(sharedVars).substr(std::string(sharedVars).find(", s")+1,std::string(sharedVars).length());
                        std::string astText= expr.get_ast().prettyprint(true);
                        int num = 0;
                        size_t forIndx=-1;
                        if(clauses.find("private")<0 || clauses.find("private")>clauses.length()) {
                            privateVars << "private(";
                            while(astText.find("for")>=0 && astText.find("for")<astText.length()){
                                forIndx = astText.find("for");
                                //std::cout<<"aC: "<<astText<<std::endl;
                                //std::cout <<astText.substr(astText.find_first_of(" for"),astText.find_first_of(" for")+4)<<std::endl;
                                astText = astText.substr(astText.find("for")+4,astText.length());
                                size_t spaces;
                                Source stringSpaces;
                                spaces = astText.substr(0,astText.find("(")).length();
                                for(int s=0;s<(int)spaces;s++){
                                    stringSpaces <<" ";
                                }
                                if(astText.substr(0,astText.find_first_of("(")).compare(std::string(stringSpaces))==0){
                                    astText = astText.substr(astText.find_first_of("(")+1,astText.length());
                                    
                                    std::string express;
                                    express = astText.substr(0,astText.find("="));
                                    // std::cout<<"0: "<<express<<std::endl;
                                    while(express.find(" ")==0) {
                                        express = express.substr(express.find(" ")+1,express.length());
                                        //  std::cout<<"1: "<<express<<std::endl;
                                    }
                                    while(express.find_last_of(" ")==express.length()-1){
                                        express = express.substr(0,express.find_last_of(" "));
                                        //  std::cout<<"2: "<<express<<std::endl;
                                    }
                                    
                                    if(express.find_last_of(" ")>0 && express.find_last_of(" ")<express.length()) {
                                        express= express.substr(express.find_last_of(" ")+1,express.length());
                                        //   std::cout<<"3: "<<express<<std::endl;
                                    }
                                    
                                    if(num==0)
                                        privateVars << express;
                                    else
                                        privateVars <<", "<<express;
                                    num++;
                                }
                            }
                            privateVars<<")";
                        }
                        Source newSource;
                        if(fixedSinside.empty() && checkSinside.empty()) {
                            newSource<<"#pragma omp parallel "<<clauses<<sharedVars<<privateVars<<"\n"<<statement.prettyprint()<<"\n";
                        }
                        if(!fixedSinside.empty() && checkSinside.empty()) {
                            newSource<<"#pragma omp parallel "<<clauses<<sharedVars<<privateVars<<fixedSinside<<"\n"<<statement.prettyprint()<<"\n";
                        }
                        if(fixedSinside.empty() && !checkSinside.empty()) {
                            newSource<<"#pragma omp parallel "<<clauses<<sharedVars<<privateVars<<checkSinside<<"\n"<<statement.prettyprint()<<"\n";
                        }
                        AST_t newAst = newSource.parse_statement(construct.get_ast(), construct.get_enclosing_function().get_scope_link());
                        expr.get_ast().replace(newAst);
                    }
                    
                }
                int n =0;
                //            std::cout<<"num constructs: "<<constructList.size()<<endl;
                for(int a =0; a<constructList.size();++a) {    
                    pragma_postorder(constructList[a]);
                }
                
                AST_t translation_unit = _dto["translation_unit"];  
            }
        }
    }
    
    
    
    
    
}
void TransPhase::putBarrier(int minLine, int staticC, int block_line, PragmaCustomConstruct construct, Symbol function_sym, Statement function_body, AST_t minAST, AST_t startAST){
    lastAst lA;
    lA._lastModifiedASTstart = startAST;
    if(minLine != std::numeric_limits<int>::max() && staticC!=2) {
        
        //        Source barrier;
        //        barrier << "MPI_Barrier(MPI_COMM_WORLD);";
        //        AST_t barrierAST = barrier.parse_global(function_body.get_ast(), function_body.get_scope_link());
        ////        cout<<minLine<<": "<<minAST.prettyprint()<<endl;
        //        if(minLine == block_line) {
        ////            cout<<"1"<<endl;
        //            minAST.append(barrierAST);
        //        } else {
        ////            cout<<"2"<<endl;
        //            minAST.prepend(barrierAST);
        //        }
        if(_construct_inside_bucle) {
            //            cout<<"3"<<endl;
            lA._wherePutFinal=_construct_loop;  
            
        } else {
            //            cout<<"4"<<endl;
            lA._wherePutFinal = minAST;
            //lA._wherePutFinal=barrierAST;  
            
        }
        lA._lastModifiedAST = minAST;
        // lA._lastModifiedAST=barrierAST;  
        
    } else {
        if(_construct_inside_bucle) {
            lA._wherePutFinal=_construct_loop;  
            
        } else {
            lA._wherePutFinal=construct.get_ast();
        }
        lA._lastModifiedAST=construct.get_ast();  
    }
    //    cin.get();
    lA._lastFunctionNameList=function_sym.get_name();
    _lastTransformInfo.push_back(lA);
}
void TransPhase::completeLoopsInAST(AST_t ast, ScopeLink scopeL){
    TraverseASTFunctor4LocateFor expr_traverseFor(scopeL);
    ObjectList<AST_t> expr_listFor = ast.depth_subtrees(expr_traverseFor);
    int lF=0;
    AST_t loopAst;
    AST_t fullLoopAst;
    for (ObjectList<AST_t>::iterator it = expr_listFor.begin();it != expr_listFor.end(); it++, lF++) {
        //completeLoopsInAST(loopAst,scopeL);
        if(ForStatement::predicate(expr_listFor[lF])) {
            ForStatement fS(expr_listFor[lF], scopeL);
            loopAst = fS.get_loop_body().get_ast();
            fullLoopAst = fS.get_enclosing_statement().get_ast();
            
        }
        
        if(WhileStatement::predicate(expr_listFor[lF])) {
            WhileStatement wS(expr_listFor[lF],scopeL);
            loopAst = wS.get_body().get_ast();
            fullLoopAst = wS.get_enclosing_statement().get_ast();
            
        }
        if(DoWhileStatement::predicate(expr_listFor[lF])) {
            DoWhileStatement dWS(expr_listFor[lF],scopeL);
            loopAst = dWS.get_body().get_ast();
            fullLoopAst = dWS.get_enclosing_statement().get_ast();
        }
        
        if(loopAst.prettyprint().find("{")!=0){
            Source loopAstWithKeys;
            loopAstWithKeys << "{"<<loopAst.prettyprint()<<"}";
            //            cout<<"1: "<<loopAst.prettyprint()<<endl;
            loopAst.replace_with(loopAstWithKeys.parse_statement(ast,scopeL));
            //            cout<<"2: "<<loopAst.prettyprint()<<endl;
            //
        }
        if(!loopAst.prettyprint().empty()) {
            //            cout<<"Continue with: "<<loopAst.prettyprint()<<endl;
            //            cout<<"Or Continue with: "<<fullLoopAst.prettyprint()<<endl;
            completeLoopsInAST(loopAst,scopeL);
        }
    }
    //    cout<<"C:" <<ast.prettyprint()<<endl;
    //
    
    
}
string TransPhase::transformConstructAST(PragmaCustomConstruct construct, ScopeLink scopeL, Scope sC, Source initVar){
    string astPrettyprint;
    AST_t construct_ast = construct.get_ast();
    
    TraverseASTFunctor4LocateUse expr_traverse(scopeL);
    ObjectList<AST_t> expr_list = construct_ast.depth_subtrees(expr_traverse);
    int l = 0;
    vector<string> newVariables;
    vector<Source> copyVariables;
    int hasChanges = 0;
    for (ObjectList<AST_t>::iterator it = expr_list.begin();it != expr_list.end(); it++, l++) {
        
        PragmaCustomConstruct test(expr_list[l],construct.get_scope_link());
        if(test.is_construct()){
            string pragmaLine = test.get_pragma_line().prettyprint();
            if(pragmaLine.find("atomic")>=0 && pragmaLine.find("atomic")<pragmaLine.length()
                    || pragmaLine.find("critical")>=0 && pragmaLine.find("critical")<pragmaLine.length()) {
                _secureWrite =1;
                test.get_ast().replace_with(test.get_statement().get_ast());
                Source newExprSource;
                newExprSource << transformConstructAST(test,scopeL,sC,initVar);
                expr_list[l].replace_with(newExprSource.parse_statement(construct.get_scope(),construct.get_enclosing_function().get_scope_link()));
                _secureWrite = 0;
            } else if(pragmaLine.find("barrier")>=0 && pragmaLine.find("barrier")<pragmaLine.length()){
                Source barrier;
                barrier << "MPI_Barrier(MPI_COMM_WORLD);"<<test.get_statement().prettyprint();
                expr_list[l].replace_with(barrier.parse_statement(test.get_ast(),construct.get_enclosing_function().get_scope_link()));
            }else if(pragmaLine.find("nowait")>=0 && pragmaLine.find("nowait")<pragmaLine.length()) {
                Source newExprSource;
                newExprSource << test.get_statement().get_ast().prettyprint();
                expr_list[l].replace_with(newExprSource.parse_statement(construct.get_scope(),construct.get_enclosing_function().get_scope_link()));
            } else if(pragmaLine.find("master")>=0 && pragmaLine.find("master")<pragmaLine.length()){
                
            }
        } else {
            Source newExprSource;
            Source mpiReads;
            Source mpiWrites;
            Source secureWrite;
            Source variableInit;
            string line;
            line =  expr_list[l].prettyprint();
            int partVars = 0;
            int thisHasChanges = 0;
            if(expr_list[l].prettyprint().find_first_of("=")>= 0 && expr_list[l].prettyprint().find_first_of("=")<expr_list[l].prettyprint().length()) {
                
                ObjectList<Source> operands, operators;
                string firstO, secondO;
                
                firstO = expr_list[l].prettyprint().substr(0,expr_list[l].prettyprint().find_first_of("="));
                secondO = expr_list[l].prettyprint().substr(expr_list[l].prettyprint().find_first_of("=")+1, expr_list[l].prettyprint().length());
                
                //            cout<<"---------------------------"<<endl;
                //            cout<<expr_list[l].prettyprint()<<endl;
                //            cout<<"1srt: "<<firstO<<endl;
                //            cout<<"2nd: "<<secondO<<endl;   
                //line = replaceAll(line, " ", "");
                string op = expr_list[l].prettyprint().substr(expr_list[l].prettyprint().find_first_of("="), expr_list[l].prettyprint().length());
                //            cout<<"1: "<<firstO<< endl;
                //            cout<<"2: "<<secondO<<endl;
                //            cout<<"o: "<<op<<endl;
                
                
                if(firstO.find_first_of("[")>0 &&firstO.find_first_of("[")<firstO.length()){
                    string type = "";
                    string var = firstO;
                    if(firstO.find_first_of("[")>firstO.find_first_of(" ")) {
                        type = firstO.substr(0,firstO.find_first_of(" "));
                        var =  firstO.substr(firstO.find_first_of(" ")+1,firstO.length());
                    }
                    firstO = type + replaceAll(var, " ", "");
                }
                line = firstO + replaceAll(op, " ", "");
                //                        cout<<"1: "<<firstO<< endl;
                //                        cout<<"2: "<<secondO<<endl;
                //                        cout<<"o: "<<op<<endl;
                //                        cout<<"l: "<<line<<endl;
                //                        cin.get();
                operands = splitMathExpression(sC, secondO, 1);
                switch(expr_list[l].prettyprint()[expr_list[l].prettyprint().find_first_of("=")-1]) {
                    case '+':
                    case '-':
                    case '/':
                    case '*':
                        string newOP = firstO;
                        if(newOP.find_last_of("]")>=0 && newOP.find_last_of("]")<firstO.length()) {
                            newOP = newOP.substr(0, newOP.find_last_of("]")+1);
                        }
                        // cout<<"NO: "<<newOP<<endl;
                        // cin.get();
                        operands.push_back(newOP);
                        break;
                }
                if(firstO.find_first_of("[")>= 0 && firstO.find_first_of("[")<firstO.length()) {
                    Source dimensions;
                    string actArg = firstO.substr(0,firstO.find_first_of("["));
                    //                cout<<actArg<<endl;
                    //                cin.get();
                    string iterators = firstO.substr(firstO.find_first_of("[")+1, firstO.length());
                    actArg = cleanWhiteSpaces(actArg);
                    
                    int finded = -1;
                    
                    for(int k=0 ;k<_ioVars.size();k++) {
                        if(std::string(_ioVars[k].name).compare(actArg)==0) {
                            finded = k;
                            break;
                        }
                    }
                    string firstIterator; 
                    if(finded>-1) {
                        int isInRange = 0;
                        string rangeInitialValue = "0";
                        string rangeFinishValue = "1";
                        AST_t forIterated;
                        firstIterator = iterators.substr(0,iterators.find_first_of("]"));
                        firstIterator = cleanWhiteSpaces(firstIterator);
                        int lineA =  get_real_line(construct.get_enclosing_function().get_ast(), construct.get_enclosing_function().get_scope_link(), expr_list[l],1,0,0);
                        int maxLine = lineA;
                        for(int i = 0;i<_ioParams[actArg].size();++i){
                            int lineIO = get_real_line(construct.get_enclosing_function().get_ast(), construct.get_enclosing_function().get_scope_link(), _ioParams[actArg][i],1,0,0);
                            if(lineIO>maxLine) {
                                maxLine = lineIO;
                                cout<<"IO: "<<_ioParams[actArg][i].prettyprint()<<endl;
                            }
                        }
                        int numIoVar = 0;
                        //                    cout<<"act: "<<expr_list[l].prettyprint()<<endl;
                        
                        //                    cout<<"L: "<<lineA<<endl;
                        //                    cout<<"L: "<<maxLine<<endl;
                        //                    cin.get();
                        if(_fullArrayWrites && std::string(initVar).compare(std::string(firstIterator)) != 0 
                                && lineA>=maxLine && (isIOVar(actArg)|| !_smartUploadDownload)) {
                            int f = 0;
                            for(int x = 0; x<_downloadVars.size();++x){
                                if(std::string(_downloadVars[x].name).compare(actArg)==0) {
                                    numIoVar = x;
                                }
                            }
                            if(!f) {
                                transferInfo down;
                                down.name = actArg;
                                int itDependent = 0;
                                int numVar = 0;
                                for(int y=0;y<_ioVars.size();++y) {
                                    if(std::string(_ioVars[y].name).compare(actArg)==0) {
                                        numVar = y;
                                        for(int z=0;z<_ioVars[y].iterVar.size();++z) {
                                            if(std::string(initVar).compare(std::string(_ioVars[y].iterVar[z]))==0) {
                                                itDependent = 1;
                                            }
                                        }
                                    }
                                    
                                }
                                if(itDependent) {
                                    down.start = _offsetVar;
                                    down.end = _offsetVar + " + " + _partSizeVar;
                                } else {
                                    down.start = "0";
                                    down.end = _ioVars[numVar].size[0];
                                }
                                _downloadVars.push_back(down);
                                numIoVar = _downloadVars.size()-1;
                            }
                            
                            
                            isInRange = isInForIteratedBy(firstIterator, expr_list[l], construct.get_ast(), scopeL, actArg, 1);
                            rangeInitialValue = _rI;
                            rangeFinishValue = _rF;
                            forIterated = _forIter;
                            //                        cout<<"inRange: "<<std::string(actArg)<<endl;
                            //                        cin.get();
                        }
                        Source operandMPIWrites, operandMPISecureWrite;
                        Source variableNewName, variableDeclaration;
                        variableNewName <<actArg;
                        variableDeclaration << std::string(_ioVars[finded].type)<<" ";
                        string upperType = std::string(_ioVars[finded].type);
                        std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                        int n = 0;
                        int isLastWrite = 1; 
                        
                        int knowedVariable = 0;
                        if(!(_fullArrayWrites && !knowedVariable && isInRange)) {
                            if(!hasChanges) {
                                operandMPIWrites <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                            } else {
                                operandMPIWrites <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                            }
                        }
                        if(_secureWrite)
                            operandMPISecureWrite <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                        if(isLastWrite) {
                            if(_secureWrite) {
                                operandMPISecureWrite << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_SWTAG<<", MPI_COMM_WORLD);\n ";
                            }
                            if(!(_fullArrayWrites && !knowedVariable && isInRange)) {
                                operandMPIWrites << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_WTAG<<", MPI_COMM_WORLD);\n ";
                            }
                        }
                        string allIter = firstO.substr(firstO.find_first_of("["), firstO.length());
                        while(iterators.find_first_of("]")>= 0 && iterators.find_first_of("]")<iterators.length()) {
                            //cout<<"Process: "<<iterators<<endl;
                            string actIt = iterators.substr(0,iterators.find_first_of("]"));
                            if(n==0 && std::string(initVar).compare(std::string(actIt)) == 0 &&  !_withMemoryLimitation) {
                                knowedVariable = 1;
                                break;
                            }
                            cout<<"iterators: "<<actIt<<endl;
                            if(isLastWrite) {
                                if(!_fullArrayWrites || !isInRange) {
                                    operandMPIWrites << "("<<_coordVectorVar
                                            <<_num_transformed_blocks
                                            <<"["
                                            <<n
                                            <<
                                            "] = "
                                            <<actIt
                                            <<");\n";
                                } else {
                                    if(n>0)
                                        dimensions <<"* "<<_ioVars[finded].size[n];
                                }
                            }
                            if(iterators.find("[")>=0 && iterators.find("[")<iterators.length())
                                iterators = iterators.substr(iterators.find_first_of("[")+1, iterators.length());
                            else
                                iterators = iterators.substr(iterators.find_first_of("]")+1, iterators.length());
                            n++;
                            variableNewName << "_"<<actIt;
                            //cout<<"Continue with: "<<iterators<<endl;
                            //
                        }
                        string rectifiedVarName = rectifyName(std::string(variableNewName));
                        int finded2 = 0;
                        for(int k = 0; k<newVariables.size();++k){
                            if(newVariables[k].compare(rectifiedVarName)==0) {
                                finded2 = 1;
                                break;
                            }
                        }
                        if(!finded2 && !knowedVariable) {
                            variableInit << variableDeclaration<< rectifiedVarName<<";\n";
                            newVariables.push_back(rectifiedVarName);
                        }
                        if(isLastWrite && (!_fullArrayWrites || !isInRange)){
                            operandMPIWrites <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<n<<", MPI_INT, 0,"<<_WTAG<<", MPI_COMM_WORLD);";
                            operandMPIWrites <<"MPI_Send(&"<<rectifiedVarName<<", 1, MPI_"<<upperType<<", 0, "<<_WTAG<<", MPI_COMM_WORLD);\n";
                        }
                        if(!knowedVariable) {
                            //                        cout<<"L: "<<line<<endl;
                            //                        cout<<"I: "<<iterators<<endl;
                            //                        cout<<"L1: "<<line<<endl;
                            //                        cout<<"Replace "<<firstO<<" for "<<rectifiedVarName<<endl;
                            hasChanges = 1;
                            thisHasChanges = 1;
                            string s2change = firstO.substr(0,firstO.find_first_of(iterators));
                            line = replaceAll(line, s2change, rectifiedVarName);
                            Source variableCopyName;
                            string firstIterator = allIter.substr(0,allIter.find_first_of("]"));
                            firstIterator = firstIterator.substr(firstIterator.find_first_of("[")+1,firstIterator.length());
                            if(_workWithCopiesOnSlave)
                                variableCopyName << actArg<<"_MPICOPY["<<firstIterator<<"-"<<_offsetVar<<"]";
                            else
                                variableCopyName << actArg<<"["<<firstIterator<<"]";
                            copyVariables.push_back(std::string(variableCopyName));
                            
                            string restIters = "";
                            if((allIter.find_last_of("]"))!=allIter.length()) {
                                restIters = allIter.substr(allIter.find_first_of("]")+1,allIter.length());
                                restIters = restIters.substr(0,restIters.find_last_of("]")+1);
                            }
                            variableCopyName <<restIters;
                            //if(_withMemoryLimitation || !isUploadedVar(firstO)) {
                            if(_withMemoryLimitation || !isInRange) {
                                
                                
                                //                        cout<<"L2: "<<line<<endl;
                                //                        
                                //cout<<std::string(mpiReads)<<endl;
                                //             cout<<"L: "<<line<<endl;
                                //            cin.get();
                                
                                if(isUploadedVar(actArg) && _ioVars[finded].size.size()>0){
                                    operandMPIWrites<<"if ("<<firstIterator<<"< "<<_partSizeVar<<")"
                                            <<"("<<variableCopyName<<"="<<rectifiedVarName<<");";
                                }
                                mpiWrites << operandMPIWrites;
                                secureWrite << operandMPISecureWrite;
                            } else {
                                //                            cout<<"HI"<<endl;
                                //                            cin.get();
                                if(_fullArrayWrites && isInRange) {
                                    if(!_outsideAditionalWrites) {
                                        _downloadVars[numIoVar].start = _offsetVar;
                                        _downloadVars[numIoVar].end = _offsetVar+" + " + _partSizeVar;
                                    }
                                    Source preWrite;
                                    Source postWrite;
                                    preWrite <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                                    preWrite << "("<<_coordVectorVar
                                            <<_num_transformed_blocks
                                            <<"[0] = "
                                            <<rangeInitialValue<<");\n";
                                    preWrite << "("<<_coordVectorVar
                                            <<_num_transformed_blocks
                                            <<"[1] = ("<<_downloadVars[numIoVar].start<<" > "<<rangeFinishValue<<") ? ("
                                            <<rangeFinishValue<<" - "<<rangeInitialValue<<") : ("<<_downloadVars[numIoVar].start
                                            <<" -"<<rangeInitialValue<<")"
                                            <<");\n";
                                    preWrite <<"if (("<<rangeInitialValue<<") < "<<_downloadVars[numIoVar].start<<" && "<<_coordVectorVar
                                            <<_num_transformed_blocks<<"[1] > 0) {"
                                            <<"MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_FWTAG<<", MPI_COMM_WORLD);\n "
                                            <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<",2, MPI_INT, 0, "<<_FWTAG<<", MPI_COMM_WORLD);"
                                            <<"MPI_Send(&"<<actArg<<"["<<_coordVectorVar<<_num_transformed_blocks<<"[0]]"<<", "<<_coordVectorVar<<_num_transformed_blocks<<"[1]"<<dimensions<<" , MPI_"<<upperType<<", 0, "<<_FWTAG<<", MPI_COMM_WORLD);\n"
                                            <<"}";
                                    postWrite <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                                    postWrite << "("<<_coordVectorVar
                                            <<_num_transformed_blocks
                                            <<"[0] = (("<<_downloadVars[numIoVar].end<<") > ("<<rangeInitialValue<<")) ? ("
                                            <<_downloadVars[numIoVar].end<<") : ("<<rangeInitialValue<<")"
                                            <<");\n";
                                    postWrite << "("<<_coordVectorVar
                                            <<_num_transformed_blocks
                                            <<"[1] = (("<<_downloadVars[numIoVar].end<<") > ("<<rangeInitialValue<<")) ? ("
                                            <<rangeFinishValue<<" - ("<<_downloadVars[numIoVar].end<<") ) : ("<<rangeFinishValue<<" - "<<rangeInitialValue<<")"
                                            <<");\n";
                                    
                                    postWrite <<"if (("<<rangeFinishValue<<") > "<<_downloadVars[numIoVar].end<<" && "<<_coordVectorVar
                                            <<_num_transformed_blocks<<"[1] > 0) {"
                                            << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_FWTAG<<", MPI_COMM_WORLD);\n "
                                            <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<",2, MPI_INT, 0, "<<_FWTAG<<", MPI_COMM_WORLD);"
                                            <<"MPI_Send(&"<<actArg<<"["<<_coordVectorVar<<_num_transformed_blocks<<"[0]]"<<", "<<_coordVectorVar<<_num_transformed_blocks<<"[1]"<<dimensions<<" , MPI_"<<upperType<<", 0, "<<_FWTAG<<", MPI_COMM_WORLD);\n"
                                            <<"}";
                                    
                                    Source write;
                                    write << preWrite << postWrite;
                                    //                                    cout<< "R: "<<std::string(read)<<endl;
                                    //                                    cin.get();
                                    
                                    if(!_outsideAditionalWrites && !_fullArrayReads) {
                                        //                                    cout<<"NO additional"<<endl;
                                        cout<<forIterated.get_line()<<endl;
                                        cout<<construct_ast.get_line()<<endl;
                                        //                                        cout<<"append"<<endl;
                                        AST_t writeAST;
                                        writeAST = write.parse_statement(construct.get_scope(),construct.get_enclosing_function().get_scope_link());
                                        forIterated.append(writeAST);
                                        
                                    } else {
                                        //                                    cout<<"additional"<<endl;
                                        
                                        Source start, end;
                                        start << "(("<<_offsetVar<<" > "<<rangeInitialValue<<") ? "<<rangeInitialValue<<" : "<<_offsetVar<<")";
                                        end << "((("<<_offsetVar<<" + "<<_partSizeVar<<") < "<<rangeFinishValue<<") ? "<<rangeFinishValue<<" : ("<<_offsetVar<<" + "<<_partSizeVar<<"))";
                                        
                                        _downloadVars[numIoVar].start = std::string(start);
                                        _downloadVars[numIoVar].end = std::string(end);
                                        _aditionalLinesWrite << write;
                                        //                                       cout<<"Will be outside construct"<<endl;
                                    } 
                                    
                                } else {
                                    if(_secureWrite)
                                        secureWrite << "if ("<<firstIterator<<">"<<_offsetVar<<" + "<<_partSizeVar<<""<<" || "<<firstIterator<<"<"<<_offsetVar<<"){"<<operandMPISecureWrite<<"}";
                                    mpiWrites << "if ("<<firstIterator<<">"<<_offsetVar<<" + "<<_partSizeVar<<""<<" || "<<firstIterator<<"<"<<_offsetVar<<"){"<<operandMPIWrites<<"} else {("<<variableCopyName<<"="<<rectifiedVarName<<");}";
                                }
                            }
                        } else {
                            hasChanges = 1;
                            thisHasChanges = 1;
                            Source variableCopyName;
                            if(_workWithCopiesOnSlave)
                                variableCopyName << actArg<<"_MPICOPY["<<initVar<<"-"<<_offsetVar<<"]";
                            else
                                variableCopyName << actArg<<"["<<initVar<<"]";
                            copyVariables.push_back(std::string(variableCopyName));
                            string restIters = "";
                            
                            if((allIter.find_last_of("]"))!=allIter.length()) {
                                restIters = allIter.substr(allIter.find_first_of("]")+1,allIter.length());
                                restIters = restIters.substr(0,restIters.find_last_of("]")+1);
                            }
                            variableCopyName <<restIters;
                            //variableCopyName << actArg<<allIter;
                            
                            string s2change = firstO.substr(0,firstO.find_last_of("]")+1);
                            //                        cout<<s2change<<endl;
                            //                        cout<<std::string(variableCopyName)<<endl;
                            //                        cout<<line<<endl;
                            //                                cout<<s2change<<endl;
                            //                                cout<<rectifiedVarName<<endl;
                            
                            line = replaceAll(line, s2change, std::string(variableCopyName));
                            //                                cout<<line<<endl;
                            //                                cin.get();
                            
                            //                        cout<<line<<endl;
                            //                        cin.get();
                        }
                    }
                }
                
                for (int e=0;e<operands.size();e++){ //second Operand
                    Source operandMPIReads;
                    
                    if(std::string(operands[e]).find_first_of("[")>= 0 && std::string(operands[e]).find_first_of("[")<std::string(operands[e]).length()) {
                        string firstIterator; 
                        cout<<std::string(operands[e])<<endl;
                        string actArg = std::string(operands[e]).substr(0,std::string(operands[e]).find_first_of("["));
                        string iterators = std::string(operands[e]).substr(std::string(operands[e]).find_first_of("[")+1, std::string(operands[e]).length());
                        actArg = cleanWhiteSpaces(actArg);
                        
                        int finded = -1;
                        for(int k=0 ;k<_inVars.size();k++) {
                            //                        cout<<std::string(_inVars[k].name)<<" vs. "<<actArg<<endl;
                            if(std::string(_inVars[k].name).compare(actArg)==0) {
                                finded = k;
                                break;
                            }
                        }
                        if(finded>-1) {
                            
                            Source variableNewName, variableDeclaration, dimensions;
                            int isInRange = 0;
                            string rangeInitialValue = "0";
                            string rangeFinishValue = "1";
                            AST_t forIterated;
                            firstIterator = iterators.substr(0,iterators.find_first_of("]"));
                            firstIterator = cleanWhiteSpaces(firstIterator);
                            int minLine = expr_list[l].get_line();
                            for(int i = 0;i<_ioParams[actArg].size();++i){
                                if(_ioParams[actArg][i].get_line()<minLine)
                                    minLine = _ioParams[actArg][i].get_line();
                            }
                            //                        cout<<"MinLine = "<<minLine<<endl;
                            //                        cout<<"Read Line = "<<expr_list[l].get_line()<<endl;
                            //                        cin.get();
                            
                            int numUploadedVar = 0;
                            if(_fullArrayReads) {
                                isInRange = isInForIteratedBy(firstIterator, expr_list[l], construct.get_ast(), scopeL, actArg, 0);
                                rangeInitialValue = _rI;
                                rangeFinishValue = _rF;
                                forIterated = _forIter;
                                cout<<"inRange: "<<std::string(operands[e])<<endl;
                                if(_expandFullArrayReads && !isUploadedVar(actArg)){
                                    transferInfo up;
                                    up.start = rangeFinishValue;
                                    up.end = rangeInitialValue;
                                    up.name = actArg;
                                    _uploadedVars.push_back(up);
                                }
                            }
                            if(isInRange && isUploadedVar(actArg) 
                                    && expr_list[l].get_line()>=minLine && (isINVar(actArg)|| !_smartUploadDownload)) {
                                for(int x = 0; x<_uploadedVars.size();++x){
                                    if(_uploadedVars[x].name.compare(actArg)==0)
                                        numUploadedVar = x;
                                }
                            }
                            variableNewName <<actArg;
                            variableDeclaration << std::string(_inVars[finded].type)<<" ";
                            string upperType = std::string(_inVars[finded].type);
                            
                            int isFirstRead = 1; 
                            
                            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                            int n = 0, knowedVariable=0;
                            if(!hasChanges) {
                                
                                operandMPIReads <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                            } else {
                                operandMPIReads <<" (idxForReadWriteSwitch ="<<finded<<");\n";
                            }
                            
                            string  allIter = std::string(operands[e]).substr(std::string(operands[e]).find_first_of("["), std::string(operands[e]).length());
                            if(allIter.find(";")>=0 && allIter.find(";")<allIter.length())
                                allIter = allIter.substr(0,allIter.find(";"));
                            while(iterators.find_first_of("]")>= 0 && iterators.find_first_of("]")<iterators.length()) {
                                //cout<<"Process: "<<iterators<<endl;
                                string actIt = iterators.substr(0,iterators.find_first_of("]"));
                                //                            cout<<"iterators: "<<actIt<<endl;
                                if(n==0 && std::string(initVar).compare(std::string(actIt)) == 0 &&  !_withMemoryLimitation) {
                                    knowedVariable = 1;
                                    break;
                                }
                                if(isFirstRead) {
                                    if(!_fullArrayReads || !isInRange || !_expandFullArrayReads) {
                                        operandMPIReads << "("<<_coordVectorVar
                                                <<_num_transformed_blocks
                                                <<"["
                                                <<n
                                                <<
                                                "] = "
                                                <<actIt<<");\n";
                                    } else {
                                        if(n>0)
                                            dimensions <<"* "<<_inVars[finded].size[n];
                                    }
                                }
                                if(iterators.find("[")>=0 && iterators.find("[")<iterators.length())
                                    iterators = iterators.substr(iterators.find_first_of("[")+1, iterators.length());
                                else
                                    iterators = "";
                                variableNewName << "_"<<actIt;
                                
                                n++;
                                //cout<<"Continue with: "<<iterators<<endl;
                                //
                            }
                            
                            if(isFirstRead) {
                                if(_fullArrayReads && !knowedVariable && isInRange && isUploadedVar(actArg)) {
                                    operandMPIReads << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_FRTAG<<", MPI_COMM_WORLD); \n";
                                } else {
                                    operandMPIReads << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_RTAG<<", MPI_COMM_WORLD); \n";
                                }
                            }
                            
                            string rectifiedVarName = rectifyName(std::string(variableNewName));
                            
                            finded = 0;
                            for(int k = 0; k<newVariables.size();++k){
                                if(newVariables[k].compare(rectifiedVarName)==0) {
                                    finded = 1;
                                    break;
                                }
                            }
                            if(!finded && !knowedVariable) {
                                variableInit << variableDeclaration<< rectifiedVarName<<";\n";
                                newVariables.push_back(rectifiedVarName);
                            }
                            if(isFirstRead && (!_fullArrayReads || !isInRange || !isUploadedVar(actArg))) {
                                operandMPIReads <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<n<<", MPI_INT, 0, "<<_RTAG<<", MPI_COMM_WORLD);";
                                operandMPIReads <<"MPI_Recv(&"<<rectifiedVarName<<", 1, MPI_"<<upperType<<", 0, "<<_RTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
                            }
                            //  cout<<expr_list[l].prettyprint()<<endl;    
                            if(!knowedVariable) {
                                hasChanges =1;
                                thisHasChanges = 1;
                                
                                if(_withMemoryLimitation || !isUploadedVar(actArg)) {
                                    mpiReads << operandMPIReads;                                                     
                                } else {
                                    
                                    Source variableCopyName;
                                    string firstIterator = allIter.substr(0,allIter.find_first_of("]"));
                                    firstIterator = firstIterator.substr(firstIterator.find_first_of("[")+1,firstIterator.length());
                                    if(_workWithCopiesOnSlave) {
                                        variableCopyName << actArg<<"_MPICOPY["<<firstIterator<<"-"<<_offsetVar<<"]";
                                    } else {
                                        variableCopyName << actArg<<"["<<firstIterator<<"]";
                                    }
                                    if(_fullArrayReads && isInRange) {
                                        //                                    cout<<actArg<<endl;
                                        //                                    cin.get();
                                        if(!_outsideAditionalReads  && (firstIterator.compare(std::string(initVar))==0 || !_expandFullArrayReads)) {
                                            cout<<"HI"<<endl;cin.get();
                                            _uploadedVars[numUploadedVar].start = _offsetVar;
                                            _uploadedVars[numUploadedVar].end = _offsetVar +" + "+ _partSizeVar;
                                        }
                                        Source preRead;
                                        Source postRead;
                                        
                                        preRead << "("<<_coordVectorVar
                                                <<_num_transformed_blocks
                                                <<"[0] = "
                                                <<rangeInitialValue<<");\n";
                                        if(_uploadedVars[numUploadedVar].start.compare(rangeFinishValue) ==0) {
                                            preRead << "("<<_coordVectorVar
                                                    <<_num_transformed_blocks
                                                    <<"[1] = "<<rangeFinishValue<<");\n";
                                        } else {
                                            preRead << "("<<_coordVectorVar
                                                    <<_num_transformed_blocks
                                                    <<"[1] = ("<<_uploadedVars[numUploadedVar].start<<" > "<<rangeFinishValue<<") ? ("
                                                    <<rangeFinishValue<<" - "<<rangeInitialValue<<") : ("<<_uploadedVars[numUploadedVar].start
                                                    <<" -"<<rangeInitialValue<<")"
                                                    <<");\n";
                                        }
                                        if(_uploadedVars[numUploadedVar].start.compare(rangeFinishValue) !=0) {
                                            preRead <<"if (("<<rangeInitialValue<<") < "<<_uploadedVars[numUploadedVar].start<<" && "<<_coordVectorVar
                                                    <<_num_transformed_blocks<<"[1] > 0) {";
                                        }
                                        
                                        preRead <<operandMPIReads 
                                                <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<",2, MPI_INT, 0, "<<_FRTAG<<", MPI_COMM_WORLD);"
                                                <<"MPI_Recv(&"<<actArg<<"["<<_coordVectorVar<<_num_transformed_blocks<<"[0]]"<<", "<<_coordVectorVar<<_num_transformed_blocks<<"[1]"<<dimensions<<" , MPI_"<<upperType<<", 0, "<<_FRTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
                                        if(_uploadedVars[numUploadedVar].start.compare(rangeFinishValue) !=0) {
                                            preRead<<"}";
                                        }
                                        if(_uploadedVars[numUploadedVar].start.compare(rangeFinishValue) !=0) {
                                            postRead << "("<<_coordVectorVar
                                                    <<_num_transformed_blocks
                                                    <<"[0] = (("<<_uploadedVars[numUploadedVar].end<<") > ("<<rangeInitialValue<<")) ? ("
                                                    <<_uploadedVars[numUploadedVar].end<<") : ("<<rangeInitialValue<<")"
                                                    <<");\n";
                                            postRead << "("<<_coordVectorVar
                                                    <<_num_transformed_blocks
                                                    <<"[1] = (("<<_uploadedVars[numUploadedVar].end<<") > ("<<rangeInitialValue<<")) ? ("
                                                    <<rangeFinishValue<<" - ("<<_uploadedVars[numUploadedVar].end<<") ) : ("<<rangeFinishValue<<" - "<<rangeInitialValue<<")"
                                                    <<");\n";
                                            
                                            postRead <<"if (("<<rangeFinishValue<<") > "<<_uploadedVars[numUploadedVar].end<<" && "<<_coordVectorVar
                                                    <<_num_transformed_blocks<<"[1] > 0) {"
                                                    <<operandMPIReads 
                                                    <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<",2, MPI_INT, 0, "<<_FRTAG<<", MPI_COMM_WORLD);"
                                                    <<"MPI_Recv(&"<<actArg<<"["<<_coordVectorVar<<_num_transformed_blocks<<"[0]]"<<", "<<_coordVectorVar<<_num_transformed_blocks<<"[1]"<<dimensions<<" , MPI_"<<upperType<<", 0, "<<_FRTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n"
                                                    <<"}";
                                        }
                                        
                                        
                                        Source read;
                                        read << preRead << postRead;
                                        //                                    cout<< "R: "<<std::string(read)<<endl;
                                        //                                    cin.get();
                                        
                                        if(!_outsideAditionalReads && !_fullArrayWrites) {
                                            
                                            cout<<forIterated.get_line()<<endl;
                                            cout<<construct_ast.get_line()<<endl;
                                            //                                        cout<<"append"<<endl;
                                            AST_t readAST;
                                            readAST = read.parse_statement(construct.get_scope(),construct.get_enclosing_function().get_scope_link());
                                            forIterated.prepend(readAST);
                                            
                                        } else {
                                            Source start, end;
                                            start << "(("<<_offsetVar<<" > "<<rangeInitialValue<<") ? "<<rangeInitialValue<<" : "<<_offsetVar<<")";
                                            end << "((("<<_offsetVar<<" + "<<_partSizeVar<<") < "<<rangeFinishValue<<") ? "<<rangeFinishValue<<" : ("<<_offsetVar<<" + "<<_partSizeVar<<"))";
                                            
                                            _uploadedVars[numUploadedVar].start = std::string(start);
                                            _uploadedVars[numUploadedVar].end = std::string(end);
                                            _aditionalLinesRead << read;
                                            //                                       cout<<"Will be outside construct"<<endl;
                                        }
                                        
                                        //                                    cin.get();  
                                    } else {
                                        
                                        copyVariables.push_back(std::string(variableCopyName));
                                        string restIters = "";
                                        if((allIter.find_last_of("]"))!=allIter.length()) {
                                            restIters = allIter.substr(allIter.find_first_of("]")+1,allIter.length());
                                            restIters = restIters.substr(0,restIters.find_last_of("]")+1);
                                        }
                                        
                                        variableCopyName <<restIters;
                                        mpiReads << "if ("<<firstIterator<<">"<<_offsetVar<<" + "<<_partSizeVar<<""<<" || "<<firstIterator<<"<"<<_offsetVar<<"){"<<operandMPIReads<<"} else {("<<rectifiedVarName<<"="<<variableCopyName<<");}";
                                    }
                                }
                                
                                if(!_fullArrayReads || !isInRange || !_expandFullArrayReads) {
                                    //                                cout<<line<<endl;
                                    //                                cout<<std::string(operands[e])<<endl;
                                    //                                cout<<rectifiedVarName<<endl;
                                    
                                    line = replaceAll(line, operands[e], rectifiedVarName);
                                    //                                cout<<actArg<<endl;
                                    //                                cout<<line<<endl;
                                    //                                cin.get();
                                }
                                
                            } else {
                                Source variableCopyName;
                                if(_workWithCopiesOnSlave)
                                    variableCopyName << actArg<<"_MPICOPY["<<initVar<<"-"<<_offsetVar<<"]";
                                else
                                    variableCopyName << actArg<<"["<<initVar<<"]";
                                copyVariables.push_back(std::string(variableCopyName));
                                
                                string restIters = "";
                                if((allIter.find_last_of("]"))!=allIter.length()) {
                                    restIters = allIter.substr(allIter.find_first_of("]")+1,allIter.length());
                                    restIters = restIters.substr(0,restIters.find_last_of("]")+1);
                                }
                                variableCopyName <<restIters;
                                //variableCopyName << actArg<<allIter;
                                line = replaceAll(line, operands[e], std::string(variableCopyName));
                            }
                        }
                    }
                    
                } 
                if(line.find_first_of(";")>= 0 && line.find_first_of(";")<line.length())
                    line = line.substr(0,line.find_first_of(";"));    
                newExprSource  << secureWrite << mpiReads <<"("<<line<<")"<<";" <<"\n"<< mpiWrites;
                
                //            cout<<line<<endl;
                //            cin.get();
            } else if((expr_list[l].prettyprint().find_first_of("++")>= 0 && expr_list[l].prettyprint().find_first_of("++")<expr_list[l].prettyprint().length()) 
                    || (expr_list[l].prettyprint().find_first_of("--")>= 0 && expr_list[l].prettyprint().find_first_of("--")<expr_list[l].prettyprint().length())){
                string exprString =  expr_list[l].prettyprint();
                Source newSource, variableNewName, operandMPIWrites, operandMPIReads, variableDeclaration;
                int p = 0; // 0 prev 1 post
                int isLastWrite = 1;
                string operatorAS,sizeS;
                infoVar newR;
                
                if(exprString.find(";")>=0 && exprString.find(";")<exprString.length())
                    exprString = exprString.substr(0,exprString.find(";"));
                if(exprString.find("++")==0) {
                    exprString = exprString.substr(2,exprString.length());
                    operatorAS = "++";
                } else if(exprString.find("++")==(exprString.length()-2)) {
                    exprString = exprString.substr(0,exprString.length()-2);
                    p = 1;
                    operatorAS = "++";
                } else if(exprString.find("--")==0) {
                    exprString = exprString.substr(2,exprString.length());
                    operatorAS = "--";
                } else if(exprString.find("--")==(exprString.length()-2)) {
                    exprString = exprString.substr(0,exprString.length()-2);
                    p = 1;
                    operatorAS = "--";
                }
                
                string actArg = exprString;
                int finded = -1;
                if(exprString.find_first_of("[")>= 0 && exprString.find_first_of("[")<exprString.length()) {
                    actArg = exprString.substr(0,exprString.find_first_of("["));
                    
                } 
                int findedR = -1;
                int findedW = -1;
                
                for(int k=0 ;k<_ioVars.size();k++) {
                    if(std::string(_ioVars[k].name).compare(actArg)==0) {
                        findedW = k;
                        break;
                    }
                }
                for(int k=0 ;k<_inVars.size();k++) {
                    if(std::string(_inVars[k].name).compare(actArg)==0) {
                        findedR = k;
                        break;
                    }
                }
                if(findedW>-1) {
                    variableNewName <<actArg;
                    if(!hasChanges) {
                        
                        
                    } 
                    if(_secureWrite) {
                        secureWrite <<" (idxForReadWriteSwitch ="<<findedW<<");\n";
                        secureWrite << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_SWTAG<<", MPI_COMM_WORLD);\n ";
                    }
                    
                    int n=0;
                    
                    
                    variableDeclaration << std::string(_inVars[findedR].type)<<" ";
                    string upperType = std::string(_inVars[findedR].type);
                    std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                    string iterators = exprString.substr(exprString.find_first_of("[")+1, exprString.length());
                    string allIter;
                    if(exprString.find_first_of("[")>= 0 && exprString.find_first_of("[")<exprString.length())
                        allIter = exprString.substr(exprString.find_first_of("["), exprString.length());
                    int knowedVariable = 0;
                    while(iterators.find_first_of("]")>= 0 && iterators.find_first_of("]")<iterators.length()) {
                        string actIt = iterators.substr(0,iterators.find_first_of("]"));
                        if(n==0 && std::string(initVar).compare(std::string(actIt)) == 0 &&  !_withMemoryLimitation) {
                            knowedVariable = 1;
                            break;
                        }
                        variableNewName << "_"<<actIt;
                        
                        operandMPIWrites << "("<<_coordVectorVar
                                <<_num_transformed_blocks
                                <<"["
                                <<n
                                <<
                                "] = "
                                <<actIt
                                <<"(;\n";
                        operandMPIReads << "("<<_coordVectorVar
                                <<_num_transformed_blocks
                                <<"["
                                <<n
                                <<
                                "] = "
                                <<actIt
                                <<");\n";
                        if(iterators.find("[")>=0 && iterators.find("[")<iterators.length())
                            iterators = iterators.substr(iterators.find_first_of("[")+1, iterators.length());
                        else
                            iterators = iterators.substr(iterators.find_first_of("]")+1, iterators.length());
                        n++;
                    }
                    string rectifiedVarName = rectifyName(std::string(variableNewName));
                    int finded = 0;
                    for(int k = 0; k<newVariables.size();++k){
                        if(newVariables[k].compare(rectifiedVarName)==0) {
                            finded = 1;
                            break;
                        }
                    }
                    if(!finded && !knowedVariable) {
                        variableInit << variableDeclaration<< rectifiedVarName<<";\n";
                        newVariables.push_back(rectifiedVarName);
                    }
                    
                    hasChanges = 1;
                    thisHasChanges = 1;
                    if(!knowedVariable) {
                        
                        operandMPIReads <<" (idxForReadWriteSwitch ="<<findedR<<");\n";
                        operandMPIWrites <<" (idxForReadWriteSwitch ="<<findedW<<");\n";
                        operandMPIWrites << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_WTAG<<", MPI_COMM_WORLD);\n ";
                        operandMPIReads << "MPI_Send(&idxForReadWriteSwitch, 1, MPI_INT, 0, "<<_RTAG<<", MPI_COMM_WORLD);\n ";
                        if(_ioVars[findedW].size.size()>0) {
                            operandMPIReads <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<n<<", MPI_INT, 0, "<<_RTAG<<", MPI_COMM_WORLD);";
                            operandMPIWrites <<"MPI_Send(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<n<<", MPI_INT, 0, "<<_WTAG<<", MPI_COMM_WORLD);"; 
                        }
                        operandMPIReads <<"MPI_Recv(&"<<rectifiedVarName<<", 1, MPI_"<<upperType<<", 0, "<<_RTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
                        operandMPIWrites <<"MPI_Send(&"<<rectifiedVarName<<", 1, MPI_"<<upperType<<", 0, "<<_WTAG<<", MPI_COMM_WORLD);\n";
                        string s2change = exprString.substr(0,exprString.find_first_of(iterators));
                        exprString = replaceAll(exprString, s2change, rectifiedVarName);
                        
                        if(_withMemoryLimitation || !isUploadedVar(std::string(_inVars[findedR].name))) {
                            //                        cout<<expr_list[l].prettyprint()<<endl;
                            //                        cin.get();
                            if(p)
                                newExprSource  << secureWrite << operandMPIReads <<"("<<exprString<<operatorAS<<");" <<"\n"<< operandMPIWrites;
                            else
                                newExprSource  << secureWrite << operandMPIReads <<"("<<operatorAS<<exprString<<");" <<"\n"<< operandMPIWrites;
                            
                            exprString = cleanWhiteSpaces(exprString);
                            line = replaceAll(exprString, " ", "");
                        } else {
                            Source variableCopyName;
                            string firstIterator = allIter.substr(0,allIter.find_first_of("]"));
                            firstIterator = firstIterator.substr(firstIterator.find_first_of("[")+1,firstIterator.length());
                            if(_workWithCopiesOnSlave)
                                variableCopyName << actArg<<"_MPICOPY["<<firstIterator<<"-"<<_offsetVar<<"]";
                            else
                                variableCopyName << actArg<<"["<<firstIterator<<"]";
                            copyVariables.push_back(std::string(variableCopyName));
                            
                            string restIters = "";
                            if((allIter.find_last_of("]"))!=allIter.length()) {
                                restIters = allIter.substr(allIter.find_first_of("]")+1,allIter.length());
                                restIters = restIters.substr(0,restIters.find_last_of("]")+1);
                            }
                            variableCopyName <<restIters;
                            string exprS;
                            if(p)
                                exprS =exprString+operatorAS+";";
                            else
                                exprS =operatorAS+exprString+";";
                            Source condition;
                            condition << "if ("<<firstIterator<<">"<<_offsetVar<<" + "<<_partSizeVar<<""<<" || "<<firstIterator<<"<"<<_offsetVar<<"){";
                            newExprSource  << condition <<operandMPIReads <<"} else {("<<rectifiedVarName<<"="<<variableCopyName<<");}"
                                    <<"("<<exprString<<operatorAS<<");" <<"\n"
                                    << condition << operandMPIWrites <<"} else {("<<variableCopyName<<"="<<rectifiedVarName<<");}";
                            
                        }
                    } else {
                        
                        Source variableCopyName;
                        if(_workWithCopiesOnSlave)
                            variableCopyName << actArg<<"_MPICOPY["<<initVar<<"-"<<_offsetVar<<"]";
                        else
                            variableCopyName << actArg<<"["<<initVar<<"]"; 
                        copyVariables.push_back(std::string(variableCopyName));
                        
                        string restIters = "";
                        if((allIter.find_last_of("]"))!=allIter.length()) {
                            restIters = allIter.substr(allIter.find_first_of("]")+1,allIter.length());
                            restIters = restIters.substr(0,restIters.find_last_of("]")+1);
                        }
                        variableCopyName <<restIters;
                        if(p)
                            newExprSource  << secureWrite << operandMPIReads <<std::string(variableCopyName)<<operatorAS<<";" <<"\n"<< operandMPIWrites;
                        else
                            newExprSource  << secureWrite << operandMPIReads <<operatorAS<<std::string(variableCopyName)<<";" <<"\n"<< operandMPIWrites;
                        
                        exprString = cleanWhiteSpaces(exprString);
                        line = replaceAll(exprString, " ", "");
                    }
                    
                    
                    
                    
                }
                
                
                
            }
            
            
            if(!std::string(variableInit).empty())
                construct.get_ast().prepend(variableInit.parse_statement(construct.get_scope(),construct.get_enclosing_function().get_scope_link()));
            if(thisHasChanges) {
                // cout<<"----------------NEW AST-----------"<<endl;
                //                        cout<<"ast: "<<construct_ast.prettyprint()<<endl;
                //                        cout<< "EL: "<<expr_list[l].prettyprint()<<endl;
                //                        cout<< "NE: "<<std::string(newExprSource)<<endl;
                
                //cout<< "NAST: "<<construct.get_ast().prettyprint()<<endl;
                //cout<< "function: "<<construct.get_enclosing_function().prettyprint()<<endl;
                expr_list[l].replace_with(newExprSource.parse_statement(construct.get_scope(),construct.get_enclosing_function().get_scope_link()));
                //
            }
        }
        //        cout<<"L: "<<l<<endl;
    }
    
    
    
    astPrettyprint = construct_ast.prettyprint();
    //    cout<<astPrettyprint<<endl;
    //    cin.get();
    //    
    return astPrettyprint;
}
int TransPhase::isInForIteratedBy(string principalIt, AST_t ast, AST_t astWhereSearch, ScopeLink scopeL, string variableName, int io) {
    
    TraverseASTFunctor4LocateFor expr_traverseFor(scopeL);
    ObjectList<AST_t> expr_listFor = astWhereSearch.depth_subtrees(expr_traverseFor);
    int lF = 0;
    int minLine = ast.get_line();
    for(int i = 0;i<_ioParams[variableName].size();++i){
        if(_ioParams[variableName][i].get_line()<minLine)
            minLine = _ioParams[variableName][i].get_line();
    }
    //    cout<<"MinLine = "<<minLine<<endl;
    _outsideAditionalReads = !io;
    _outsideAditionalWrites = io;
    for (ObjectList<AST_t>::iterator it = expr_listFor.begin();it != expr_listFor.end(); it++, lF++) { 
        if(ForStatement::predicate(expr_listFor[lF])) {
            Statement s(expr_listFor[lF],scopeL);
            ForStatement fS(s);
            string inductionVar = fS.get_induction_variable().prettyprint();
            //            cout<<fS.get_iterating_init()<<endl;
            //            cout<<fS.get_iterating_condition().prettyprint()<<endl;
            //            cout<<inductionVar<<endl;
            //            cin.get();
            
            if(inductionVar.compare(principalIt) == 0) {
                
                TraverseASTFunctor4LocateUse expr_traverseUse(scopeL);
                ObjectList<AST_t> expr_listUse = fS.get_loop_body().get_ast().depth_subtrees(expr_traverseUse);
                int l = 0;
                int finded = 0;
                for (ObjectList<AST_t>::iterator it2 = expr_listUse.begin();it2 != expr_listUse.end(); it2++, l++) { 
                    if(ast.prettyprint().compare(expr_listUse[l].prettyprint())==0 && ast.get_line() == expr_listUse[l].get_line()) {
                        finded = 1;
                    }
                }
                if(finded) {
                    if(io) {
                        if(expr_listUse[l].get_line()>minLine) {
                            _forIter = expr_listFor[lF];
                            _outsideAditionalWrites = 0;
                            //                            cout<<"Read afterMinLine on "<<expr_listUse[l].get_line()<<endl;
                            //                            cin.get();
                        }
                    }
                    else if(expr_listUse[l].get_line()>minLine) {
                        _forIter = expr_listFor[lF];
                        _outsideAditionalReads = 0;
                        //                        cout<<"Read afterMinLine on "<<expr_listUse[l].get_line()<<endl;
                        //                        cin.get();
                    }
                    //                    cout<< fS.prettyprint()<<endl;
                    //                    cin.get();
                    Source initS;
                    AST_t init = fS.get_iterating_init();
                    Expression exprInit(init, fS.get_scope_link());
                    
                    initS << exprInit.prettyprint();
                    string tempInitValue = std::string(initS).substr(std::string(initS).find_first_of("=")+1,std::string(initS).length());
                    if(tempInitValue.find_first_of(";")>=0 && tempInitValue.find_first_of(";")<tempInitValue.length()) {
                        //                        cout<<"; found"<<endl;
                        tempInitValue = tempInitValue.substr(0,tempInitValue.find_first_of(";"));
                    }
                    tempInitValue = cleanWhiteSpaces(tempInitValue);
                    string varToWork;
                    Expression condition = fS.get_iterating_condition();
                    string conditionToWork = condition.prettyprint();
                    
                    
                    if(conditionToWork.find_first_of(";")>=0 && conditionToWork.find_first_of(";")<conditionToWork.length()){
                        conditionToWork.substr(0,conditionToWork.find_first_of(";")-1);
                    }
                    if(conditionToWork.find_first_of("=")>=0 && conditionToWork.find_first_of("=")<conditionToWork.length()){
                        varToWork = conditionToWork.substr(0, conditionToWork.find_first_of("="));
                        conditionToWork = conditionToWork.substr(conditionToWork.find_first_of("=")+1,conditionToWork.length());
                        
                    }
                    if(conditionToWork.find_first_of("<")>=0 && conditionToWork.find_first_of("<")<conditionToWork.length()){
                        varToWork = conditionToWork.substr(0, conditionToWork.find_first_of("<"));
                        conditionToWork =conditionToWork.substr(conditionToWork.find_first_of("<")+1,conditionToWork.length());
                        
                    }
                    if(conditionToWork.find_first_of(">")>=0 && conditionToWork.find_first_of(">")<conditionToWork.length()){
                        varToWork = conditionToWork.substr(0, conditionToWork.find_first_of("<"));
                        conditionToWork =conditionToWork.substr(conditionToWork.find_first_of(">")+1,conditionToWork.length());
                        
                    }
                    varToWork = cleanWhiteSpaces(varToWork);
                    if(varToWork.compare(principalIt)!=0){
                        cerr << "Complex for not supported"<<endl;
                        exit(-1);
                    }
                    conditionToWork =  cleanWhiteSpaces(conditionToWork);
                    _rI = tempInitValue;
                    _rF = conditionToWork;
                    
                    //                    cout<< _rI<< endl;
                    //                    cout<< _rF<< endl;
                    //                    cout<< _forIter.prettyprint()<< endl;
                    //                    cin.get();
                    return 1;
                }
                //                _forIter = fS.get_ast();
                //                _rF = "100";
            } else {
                //            
                return isInForIteratedBy(principalIt, ast, fS.get_loop_body().get_ast(), scopeL, variableName, io);
                //
            }
        }
    }
    
    return 0;
}
int TransPhase::isUploadedVar(string name){
    for (int i=0;i<_uploadedVars.size();++i)
        if(_uploadedVars[i].name.compare(name)==0) {
            //            cout<<name<<" is Uploaded var"<<endl;
            return 1;
        }
    //    cout<<name<<" is not Uploaded var"<<endl;
    return 0;
}
string TransPhase::rectifyName(string oldName) {
    string rectifiedVarName = replaceAll(oldName," ","_");
    rectifiedVarName = replaceAll(rectifiedVarName,"+","Plus");
    rectifiedVarName = replaceAll(rectifiedVarName,"-","Sub");
    rectifiedVarName = replaceAll(rectifiedVarName,"/","Div");
    rectifiedVarName = replaceAll(rectifiedVarName,"*","Mul");
    rectifiedVarName = replaceAll(rectifiedVarName,"(","Open");
    rectifiedVarName = replaceAll(rectifiedVarName,")","Close");
    return rectifiedVarName;
}


string TransPhase::replaceAll(std::string str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
    }
    return str;
}

vector<TransPhase::infoVar> TransPhase::fill_vars_info(std::unordered_map <std::string,ObjectList<AST_t>> params, TL::HLT::Outline outlineAux, PragmaCustomConstruct construct, Source initVar, Scope functionScope, Scope globalScope, int iNOUT){
    vector<infoVar> vars;
    typedef std::unordered_map <std::string,ObjectList<AST_t>> iter4vars; 
    cout<<"-------------------------"<<endl;
    for (iter4vars::const_iterator it = params.begin(); it != params.end(); ++it) {
        
        cout<<"Studying "<<it->first<<" variable"<<endl;
        
        // cin.get();
        infoVar newR;
        newR.name << it->first;
        for (int i=0;i<it->second.size();++i){
            AST_t actAST = it->second[i];
            
            ObjectList<Source> iterators;
            if(iNOUT){
                string actASTstring = actAST.prettyprint();
                if(actASTstring.find_first_of("=")>0 && actASTstring.find_first_of("=")<actASTstring.length())
                    actASTstring = actASTstring.substr(0,actASTstring.find_first_of("="));
                iterators = findPrincipalIterator(actASTstring, it->first);
                //                cout<<actAST<<endl;
                
                
                for(int j=0;j<iterators.size();++j) {
                    int find = 0;
                    
                    for(int x=0;x<newR.iterVar.size();++x) {
                        if(std::string(newR.iterVar[x]).compare(std::string(iterators[j]))==0)
                            find = 1;
                    }
                    if(!find) {
                        cout<<"adding "<<std::string(iterators[j])<<" to "<<std::string(newR.name)<<endl;
                        newR.iterVar.push_back(iterators[j]);
                    }
                }
                //                cin.get();
                for(int x=0;x<_inVars.size();++x) {
                    
                    if(std::string(newR.name).compare(std::string(_inVars[x].name))==0) {
                        //                        cout<<"Filling "<<std::string(newR.name)<<endl;
                        for(int y=0;y<_inVars[x].iterVar.size();++y) {
                            int finded =0;
                            //                            cout<<"Checking if has iterator: "<<std::string(_inVars[x].iterVar[y])<<endl;
                            for(int z = 0; z<newR.iterVar.size();++z) {
                                //                                cout<<"vs "<<std::string(newR.iterVar[z])<<endl;
                                if(std::string(newR.iterVar[z]).compare(std::string(_inVars[x].iterVar[y]))==0) {
                                    finded =1;
                                } 
                            }
                            if(!finded) {
                                //                                cout<<"adding "<<std::string(_inVars[x].iterVar[y])<<" to "<<std::string(_inVars[x].name)<<endl;
                                newR.iterVar.push_back(_inVars[x].iterVar[y]);
                            } 
                            
                        }
                        
                        _inVars[x].iterVar = newR.iterVar;
                    }
                }
                //                cin.get();
            } else {
                //                 cout<<"HI"<<endl;
                string actASTstring = actAST.prettyprint();
                if(actASTstring.find_first_of("=")>0 && actASTstring.find_first_of("=")<actASTstring.length())
                    actASTstring = actASTstring.substr(actASTstring.find_first_of("=")+1, actASTstring.length());
                string second = actASTstring;
                //                cout<<"HI2"<<endl;
                iterators = findPrincipalIterator(second, it->first);
                ObjectList<Source> iteratorsAdditional;
                switch(actAST.prettyprint()[actAST.prettyprint().find_first_of("=")-1]) {
                    case '+':
                    case '-':
                    case '/':
                    case '*':
                        Source firstO;
                        firstO = actAST.prettyprint().substr(0,actAST.prettyprint().find_first_of("=")-1); 
                        iteratorsAdditional = findPrincipalIterator(firstO, it->first);
                        break;
                }
                for(int x=0;x<iteratorsAdditional.size();++x) {
                    iterators.push_back(iteratorsAdditional[x]);
                }
                //               cout<<"HI3"<<endl;
                for(int j=0;j<iterators.size();++j) {
                    int find = 0;
                    
                    for(int x=0;x<newR.iterVar.size();++x) {
                        if(std::string(newR.iterVar[x]).compare(std::string(iterators[j]))==0)
                            find = 1;
                    }
                    if(!find) {
                        //                        cout<<"adding "<<std::string(iterators[j])<<" to "<<std::string(newR.name)<<endl;
                        newR.iterVar.push_back(iterators[j]);
                    }
                }
                for(int x=0;x<_ioVars.size();++x) {
                    //                    cout<<"H2I"<<endl;
                    if(std::string(newR.name).compare(std::string(_ioVars[x].name))==0) {
                        for(int y=0;y<_ioVars[x].iterVar.size();++y) {
                            int finded =0;
                            for(int z = 0; z<newR.iterVar.size();++z) {
                                if(std::string(newR.iterVar[z]).compare(std::string(_ioVars[x].iterVar[y]))==0)
                                    finded =1;
                            }
                            if(!finded)
                                newR.iterVar.push_back(_ioVars[x].iterVar[y]);
                            
                        }
                        
                        _ioVars[x].iterVar = newR.iterVar;
                    }
                }
                
            }
        }
        //        cout<<"HI4"<<endl;
        //Is iterator variable dependant
        
        //newR.iterVarInOperation = outlineAux.get_parameter_ioSpecificIsIteratorDependent(construct.get_scope(),it->first,std::string(initVar));
        //Var in second Operand disabled
        Symbol findedS = functionScope.get_symbol_from_name(newR.name);
        string declaration;
        string sizeS, maxS;
        string n2find = " "+std::string(it->first);
        if(!findedS.is_valid()){
            findedS = globalScope.get_symbol_from_name(newR.name);
            if(findedS.is_valid()){
                
                declaration = std::string(findedS.get_type().get_declaration(globalScope,newR.name));
                // cout<<"d1:"<<declaration<<endl;
                declaration = declaration.substr(0, declaration.find(n2find));
                //cout<<"d1:"<<declaration<<endl;
            }
        } else {
            declaration = std::string(findedS.get_type().get_declaration(functionScope,newR.name));
            
            //cout<<"d2:"<<declaration<<endl;
            declaration = declaration.substr(0, declaration.find(n2find));
            //cout<<"d2:"<<declaration<<endl;
        }
        if(findedS.is_valid()) {
            if(findedS.get_type().is_pointer()) {
                AST_t allocateAst;
                TraverseASTFunctor4Malloc expr_traverse(_scope_link);
                ObjectList<AST_t> asts = allocateAst.depth_subtrees(expr_traverse);
                int l=0;
                for (ObjectList<AST_t>::iterator it = asts.begin();it != asts.end();it++,l++) {
                    Expression expr(asts[l], _scope_link);
                    std::string firstOperand;
                    firstOperand = expr.get_first_operand().prettyprint();
                    size_t arrayAcces;
                    arrayAcces = firstOperand.find("[");
                    if(arrayAcces < 0 || arrayAcces>firstOperand.length()) {
                        //cout<<"3"<<endl;
                        Symbol sym = expr.get_first_operand().get_symbol();
                        if(sym.get_type().is_pointer()) {
                            std::string mallocExpr, mallocString;
                            mallocExpr = expr.prettyprint();
                            size_t findMalloc;
                            findMalloc = mallocExpr.find("malloc");
                            if(findMalloc > 0 && findMalloc<mallocExpr.length()) {
                                sizeS = mallocExpr.substr(findMalloc+6,mallocExpr.length());
                            }
                        }
                    } 
                } 
            } else if(findedS.get_type().is_array()) {
                string declaratrionS = findedS.get_point_of_declaration().prettyprint();
                while(declaratrionS.find_first_of("[")>=0 && declaratrionS.find_first_of("[")<declaratrionS.length()) {
                    std::string actIterator = declaratrionS.substr(declaratrionS.find_first_of("[")+1,declaratrionS.length());
                    actIterator = actIterator.substr(0,actIterator.find("]"));
                    //                                    std::cout<< std::string(newR.name) << "-> "<< actIterator <<" on  ("<<declaratrionS<<")"<<std::endl;
                    //                                    
                    
                    newR.size.push_back(actIterator);
                    declaratrionS = declaratrionS.substr(declaratrionS.find("]")+1, declaratrionS.length());
                }
            }
        }
        
        //cout<< "FS1: -"<<declaration<<"-"<<endl;
        declaration = cleanWhiteSpaces(declaration);
        
        //cout<< "FS: -"<<declaration<<"-"<<endl;
        newR.type <<  declaration;
        //cout<<"T: "<<std::string(newR.type)<<endl;
        //
        if(!isReducedVar(std::string(newR.name))  && !isPrivateVar(std::string(newR.name))){
            
            //cout<<"Test as: "<<std::string(newR.name)<<" iterated by "<<std::string(newR.iterVar[i])<<endl;
            if (iNOUT && (isIOVar(std::string(newR.name)) || !_smartUploadDownload)) {
                //if(iNOUT) {
                vars.push_back(newR);
                
                cout<<"OUTVAR: "<<std::string(newR.name);
                if(newR.iterVar.size()>0) {
                    cout <<" iterated by :";
                    for(int i=0;i<newR.iterVar.size();++i)
                        cout<<", "<<std::string(newR.iterVar[i]);
                    
                }
                cout<<endl;
            } else if (!iNOUT && (isINVar(std::string(newR.name)) || !_smartUploadDownload)) {
                //} else if (!iNOUT) {
                vars.push_back(newR);
                cout<<"INVAR: "<<std::string(newR.name);
                if(newR.iterVar.size()>0) {
                    cout<<" iterated by :";
                    for(int i=0;i<newR.iterVar.size();++i)
                        cout<<", "<<std::string(newR.iterVar[i]);
                }
                cout<<endl;
            }
            
            
            // 
        }
        
        
        
        
    }
    return vars;
}


int TransPhase::isReducedVar(string name) {
    for(int i = 0; i<_reducedVars.size();++i){
        if(std::string(_reducedVars[i].name).compare(name)==0) {
            return 1;
        }
    }
    return 0;
}

int TransPhase::isPrivateVar(string name) {
    for(int i = 0; i<_privateVars.size();++i){
        if(std::string(_privateVars[i]).compare(name)==0) {
            return 1;
        }
    }
    return 0;
}

int TransPhase::isIOVar(string name) {
    
    if(_smart_use_table[name].row_first_read_cpu.row>0) {
        if((_smart_use_table[name].row_first_write_cpu.row<=_smart_use_table[name].row_first_read_cpu.row))
            return 1;
    }else if(_construct_inside_bucle) {
        if(_smart_use_table[name].row_last_read_cpu.for_num == _construct_num_loop)
            if(_smart_use_table[name].row_last_read_cpu.row<_smart_use_table[name].row_last_write_cpu.row)
                return 1;
    } else {
        if(_scope_link.get_scope(_translation_unit).get_symbol_from_name(name).is_valid() && _divideWork && _smartUploadDownload){
            if(_scope_link.get_scope(_translation_unit).get_symbol_from_name(name).is_defined()){
                cout<<"Detected "<<name<<" as global variable (this will be allways transfered to ensure proper value updates)"<<endl;
                cin.get();
                return 1;
            }
        }
    }
    
    return 0;
}
int TransPhase::isINVar(string name) {
    if(_smart_use_table[name].row_last_write_cpu.row>0 
            || (_construct_inside_bucle && _smart_use_table[name].row_first_write_cpu.for_num == _construct_num_loop)) 
        return 1;   
    else  {
        //TODO check if is global
        if(_scope_link.get_scope(_translation_unit).get_symbol_from_name(name).is_valid() && _divideWork && _smartUploadDownload){
            if(_scope_link.get_scope(_translation_unit).get_symbol_from_name(name).is_defined()){
                cout<<"Detected "<<name<<" as global variable (this will be allways transfered to ensure proper value updates)"<<endl;
                cin.get();
                return 1;
            }
        }
        //        if(_scope_link.get_scope(_translation_unit).get_symbol_from_name(name).is_()) {
        //            cout<<name <<": "<<_smart_use_table[name].row_last_write_cpu.row<<endl;
        //            cin.get();
        //        }
    }
    return 0;
}


Source TransPhase::modifyReductionOperation(infoVar reducedVar, AST_t constructAST, PragmaCustomConstruct construct) {
    
    TraverseASTFunctor4LocateUse expr_traverse(construct.get_enclosing_function().get_scope_link());
    ObjectList<AST_t> expr_list = constructAST.depth_subtrees(expr_traverse);
    int l=expr_list.size()-1;
    for (ObjectList<AST_t>::iterator it = expr_list.end();it != expr_list.begin(); --it, --l) {
        Expression expr(expr_list[l], construct.get_enclosing_function().get_scope_link());
        string ppExpr = expr.prettyprint();
        //        cout<<"E:"<< ppExpr<<endl;
        //        cout<<"Red Var: "<<std::string(reducedVar.name)<<endl;
        if(expr.is_assignment()) {
            //            cout<<"A:"<< ppExpr<<endl;
            // 
            //borrar name de l'operacio 
            ObjectList<Source> oper = splitMathExpression(construct.get_enclosing_function().get_scope(), expr.get_second_operand().prettyprint(), 0);
            int finded =0;
            for(int i = 0; i<oper.size();++i) {
                if(std::string(oper[i]).compare(std::string(reducedVar.name))==0)
                    finded =1;
            }
            regex_t expEqual;
            regex_t expEqual2; //Our compiled expression
            stringstream equal,equal2;
            if(finded) {
                finded = 0;
                ppExpr = expr.get_second_operand().prettyprint()+";";            
                equal <<"\\s*"<< std::string(reducedVar.name)<<"\\s*"<<std::string(reducedVar.operation)<<"\\s*";
                
                if (regcomp(&expEqual, equal.str().c_str(), 0) != 0) {
                    exit(EXIT_FAILURE);
                }
                
                size_t     nmatch = 2;
                regmatch_t matchesEqual[2]; //A list of the matches in the string (a list of 1)
                string prev, post;
                if (regexec(&expEqual, ppExpr.c_str(), nmatch, matchesEqual, 0) == 0){
                    if(matchesEqual[0].rm_so>=0 && matchesEqual[0].rm_eo< ppExpr.length()) {
                        finded = 1;
                        post = ppExpr.substr(matchesEqual[0].rm_eo, ppExpr.length());
                        prev = ppExpr.substr(0, matchesEqual[0].rm_so);
                    }
                }
                if(!finded) {
                    
                    ppExpr = expr.get_second_operand().prettyprint()+";";
                    equal2 <<std::string(reducedVar.operation)<<"\\s*"<<std::string(reducedVar.name)<<"\\s*";
                    if (regcomp(&expEqual2, equal2.str().c_str(), 0) != 0) {
                        exit(EXIT_FAILURE);
                    }
                    
                    if (regexec(&expEqual2, ppExpr.c_str(), nmatch, matchesEqual, 0) == 0){
                        if(matchesEqual[0].rm_so>=0 && matchesEqual[0].rm_eo< ppExpr.length()) {
                            finded = 1;
                            
                            post = ppExpr.substr(matchesEqual[0].rm_eo, ppExpr.length());
                            prev = ppExpr.substr(0, matchesEqual[0].rm_so);
                            
                        }
                        
                    }
                }
                if(finded) {
                    Source newExpr;
                    AST_t newASTexpr;
                    newExpr << prev << post;
                    newASTexpr = newExpr.parse_statement(constructAST, construct.get_scope_link());
                    expr.get_second_operand().get_ast().replace(newASTexpr);
                }
            }
            
            
        } else if(expr.is_operation_assignment()) {
            //            cout<<"O:"<< ppExpr<<endl;
            if(expr.get_first_operand().prettyprint().compare(reducedVar.name)==0) {
                //                cout<<"OK:"<< ppExpr<<endl;
                
                Source newExpr;
                AST_t newASTexpr;
                newExpr << reducedVar.name << " = "<< expr.get_second_operand()<<";";
                newASTexpr = newExpr.parse_statement(constructAST, construct.get_scope_link());
                expr_list[l].replace(newASTexpr);
            }
            
        }
        else if(ppExpr.find_first_of("=")>=0 
                && ppExpr.find_first_of("=")<=ppExpr.length() 
                && ppExpr.find_first_of(std::string(reducedVar.name))+std::string(reducedVar.name).length() < ppExpr.find_first_of("=")
                && ppExpr.find_first_of(std::string(reducedVar.name)) >= 0
                && ppExpr.find_first_of(std::string(reducedVar.name)) < ppExpr.length()) {
            cout<<"exception:"<< ppExpr<<endl;
            Source newExpr;
            AST_t newASTexpr;
            newExpr << reducedVar.name << " = "<< ppExpr.substr(ppExpr.find_first_of("=")+1,ppExpr.length());
            cout <<"new expression: "<< std::string(newExpr) << endl;
            newASTexpr = newExpr.parse_statement(constructAST, construct.get_scope_link());
            expr_list[l].replace(newASTexpr);
            
        }
        
    }
    // 
    
    return constructAST.prettyprint();
}
ObjectList<Source> TransPhase::findPrincipalIterator(string varUse, string name) {
    regex_t expEqual; //Our compiled expression
    stringstream equal;
    string sizeS = "1";
    equal << "\\("<<name<<"\\s*"<<"\\["<<"\\s*"<<".*"<<"\\s*"<<"\\]"<<"\\)";
    ObjectList<Source> iteratorS;
    //cout <<varUse.prettyprint() <<endl;
    if (regcomp(&expEqual, equal.str().c_str(), 0) != 0) {
        exit(EXIT_FAILURE);
    }
    size_t     nmatch = 2;
    regmatch_t matchesEqual[2]; //A list of the matches in the string (a list of 1)
    //    cout<<"V: "<<varUse<<endl;
    //    cin.get();
    while (regexec(&expEqual, varUse.c_str(), nmatch, matchesEqual, 0) == 0){
        sizeS = varUse.substr(matchesEqual[0].rm_so + name.length()+1, varUse.length());
        sizeS = sizeS.substr(0, sizeS.find_first_of("]"));
        sizeS = replaceAll(sizeS," ", "");
        iteratorS.push_back(sizeS);
        varUse = varUse.substr(matchesEqual[0].rm_so + name.length()+1, varUse.length());          
    }
    return iteratorS;
}
int TransPhase::get_size_of_array(string name, string declaration) {
    regex_t expEqual; //Our compiled expression
    stringstream equal;
    string sizeS = "1";
    //    cout<<declaration<<endl;
    //    
    equal << "\\("<<name<<"\\s*"<<"\\["<<"\\s*"<<"[0-9]*"<<"\\s*"<<"\\]"<<"\\)";
    //cout <<declaration <<endl;
    if (regcomp(&expEqual, equal.str().c_str(), 0) != 0) {
        exit(EXIT_FAILURE);
    }
    size_t     nmatch = 2;
    regmatch_t matchesEqual[2]; //A list of the matches in the string (a list of 1)
    
    if (regexec(&expEqual, declaration.c_str(), nmatch, matchesEqual, 0) == 0){
        sizeS = declaration.substr(matchesEqual[0].rm_so + name.length()+1, declaration.length());
        sizeS = sizeS.substr(0, sizeS.find_first_of("]"));
    }
    return atoi((const char *)sizeS.c_str());
}
bool TransPhase::checkDirective(PragmaCustomConstruct construct, string directiveName) {
    PragmaCustomClause clause = construct.get_clause(directiveName);
    //    cout<<clause.prettyprint()<<endl;
    //    cin.get();
    if (clause.is_defined()) {
        return 1;
    }
    return 0;
}
void TransPhase::finalize() {
    
    Source fin;
    
    fin << "if("<<_myidVar<<" == 0) {("<<_timeFinishVar<<" = MPI_Wtime());";
    if(_divideWork)
        fin << "printf(\"MPI_Wtime measured: %1.2f\\n\", "<<_timeFinishVar<<"-"<<_timeStartVar<<");";
    fin << "}"<< "MPI_Finalize();";
    AST_t finAST = fin.parse_statement(_translation_unit,_scope_link);
    ObjectList<string> taskDividedFunctions;
    
    for (int i=0; i < _lastTransformInfo.size(); ++i) {
        //        if(i==0) {
        //            cout<<0<<": "<<_lastTransformInfo[i]._lastModifiedASTstart.prettyprint()<<endl;
        //        } else {
        //            cout<<1<<": "<<_lastTransformInfo[i]._lastModifiedASTstart.prettyprint()<<endl;
        //        }
        //cin.get();
        int assigned = 0;
        if(i+1<_lastTransformInfo.size()) {
            if(_lastTransformInfo[i]._lastFunctionNameList.compare(_lastTransformInfo[i+1]._lastFunctionNameList)!=0) {
                _lastTransformInfo[i]._wherePutFinal.append(finAST);
                assigned = 1;
            }
        } else {
            _lastTransformInfo[i]._wherePutFinal.append(finAST);
            assigned = 1;
            
        }
        if(assigned && !_divideWork) {
            //assignMasterWork(_lastTransformInfo[i]._lastFunctionNameList);    
            assignMasterWork(_lastTransformInfo[i]);
        }
        
        //        assignMasterWork(_lastTransformInfo[i]);
        //cout<<_lastTransformInfo[i]._wherePutFinal.get_enclosing_statement().prettyprint()<<endl;
        
    } 
    
}



void TransPhase::assignMasterWork(lastAst ast2Work) {
    Expression lastExpression(ast2Work._wherePutFinal,_scope_link);
    //ObjectList<AST_t> child = ast2Work._wherePutFinal.children();
    //cout<<child[0].children()[0].prettyprint()<<endl;
    
    FunctionDefinition fD = lastExpression.get_enclosing_function();
    Scope fScope = fD.get_scope();
    ScopeLink sL = fD.get_scope_link();
    AST_t functionAST = fD.get_function_body().get_ast();
    TraverseASTFunctor4All expr_traverse(sL);
    ObjectList<AST_t> expr_list = functionAST.depth_subtrees(expr_traverse);
    int finded = 0;
    Source masterWork;
    AST_t masterWorkAST, ast2follow;
    masterWork << "if ("<<_myidVar<<" == 0) {\n"; 
    if(fD.get_function_symbol().get_name().compare("main")==0) {
        masterWork<<"printf(\"MPI_Wtime measured: %1.2f\\n\", "<<_timeFinishVar<<"-"<<_timeStartVar<<");";
    }
    int lastLine = 0;
    for (int l = 0;l < expr_list.size(); l++) {
        if(finded) {
            Expression expr(expr_list[l], sL);
            if(expr.is_function_call()) {
                //                cout<<"function Call"<<endl;
                
                Symbol fSym = expr.get_called_entity();
                if(fSym.is_valid()) {
                    //                    cout<< fSym.get_name() << endl;
                    int f = 0;
                    for(int i = 0; i<_lastTransformInfo.size(); ++i) {
                        if(fSym.get_name().compare(_lastTransformInfo[i]._lastFunctionNameList) == 0) {
                            masterWork << "}" << addCommaIfNeeded(expr_list[l].prettyprint())<<" if("<<_myidVar<<" == 0) {\n";
                            expr_list[l].remove_in_list();
                            lastLine = expr_list[l].get_line();
                            f = 1;
                        } 
                    }
                    if(!f) {
                        if(expr_list[l].get_line()>lastLine ) {
                            //                            cout<<expr_list[l].prettyprint()<<endl;
                            lastLine = expr_list[l].get_line();
                            masterWork << (expr_list[l].prettyprint());
                            expr_list[l].remove_in_list();
                        }
                    }
                } else {
                    if(expr_list[l].get_line()>lastLine ) {
                        //                        cout<<"NV:"<<expr_list[l].prettyprint()<<endl;
                        lastLine = expr_list[l].get_line();
                        masterWork << addCommaIfNeeded(expr_list[l].prettyprint());
                        expr_list[l].remove_in_list();
                    }
                }
                //
            } else
                if(expr_list[l].prettyprint().find("return ")!=0) {
                    //                    cout<<expr_list[l].get_line()<<endl;
                    int realLine = get_real_line(functionAST, sL, expr_list[l],1,0,0);
                    if(expr_list[l].is_valid() && expr_list[l].get_line()>lastLine 
                            && (!is_inside_bucle(expr_list[l],sL,realLine,0) 
                            || ForStatement::predicate(expr_list[l]) 
                            || WhileStatement::predicate(expr_list[l])
                            || DoWhileStatement::predicate(expr_list[l]))) {
                        if(ForStatement::predicate(expr_list[l])|| WhileStatement::predicate(expr_list[l])
                                || DoWhileStatement::predicate(expr_list[l])) {
                            lastLine = get_last_ast(expr_list[l], sL).get_line();
                        } else {
                            lastLine = expr_list[l].get_line();
                        }
                        masterWork << addCommaIfNeeded(expr_list[l].prettyprint());
                        //                        cout<<"ACCEPTED: ("<<expr_list[l].get_line()<<")"<<expr_list[l].prettyprint()<<endl;
                        expr_list[l].remove_in_list();
                        //                    
                    }
                } else {
                    //                    cout<<"DISCARTED: "<<expr_list[l].prettyprint()<<endl;
                    if(expr_list[l].get_line()>lastLine)
                        lastLine = expr_list[l].get_line();
                    //  
                } 
            
        }
        // 
        if(expr_list[l].prettyprint().compare("MPI_Finalize();")==0) {
            ast2follow = expr_list[l];
            lastLine = expr_list[l].get_line();
            //                       cout<< "AST 2 FOLLOW: "<<ast2follow.prettyprint()<<endl;
            finded = 1;
        } 
        
        
    }
    
    
    masterWork << "}";
    //    cout<<finded<<" :"<< std::string(masterWork)<< endl;
    if(finded==1) {
        masterWorkAST = masterWork.parse_statement(functionAST,sL);  
        ast2follow.append(masterWorkAST);
        //                cout<<"FINAL AST: "<<ast2follow.prettyprint()<<endl;
        //                
    }
    
}
string TransPhase::addCommaIfNeeded(string arrayToCheck) {
    if(arrayToCheck.find_first_of(";")<0 || arrayToCheck.find_first_of(";")>arrayToCheck.length())
        return arrayToCheck+";";
    return arrayToCheck;
}
string TransPhase::cleanWhiteSpaces(string toClean) {
    if(!toClean.empty()) {
        while(std::string(toClean).find_first_of(" ")==0){                       
            toClean = std::string(toClean).substr(1,std::string(toClean).length());
        }
        while(std::string(toClean).find_last_of(" ")==std::string(toClean).length()-1){
            toClean = std::string(toClean).substr(0,std::string(toClean).length()-1);
        }
    }
    return toClean;
}


//*********************

AST_t TransPhase::fill_smart_use_table(AST_t asT, ScopeLink scopeL, Scope sC, int outline_num_line, ObjectList<Symbol> prmters , int kind, int offsetLine, AST_t prevAST){
    //    cout<<"Finding "<<prmters.size()<<" parameters"<<endl;
    //    for(int i = 0; i<prmters.size();++i)
    //                cout<<prmters[i].get_name()<<endl;
    //            
    int l=0;
    int line=0;
    //std::cout<<"Working Line: "<<outline_num_line<<endl;
    
    int k=0;
    int f=0;
    int maxLine=offsetLine;
    std::istringstream allAST(asT.prettyprint(false));
    std::string lineActAst;    
    Source workingSource,lastSource;
    int q =0;
    AST_t actAst, workingAst,lastAst;
    while (std::getline(allAST, lineActAst)) {
        maxLine++;
        if(q!=0)
            workingSource << lineActAst <<"\n";
        lastSource << lineActAst <<"\n";
        q++;
    }
    int inside =0;
    if(kind!=2 && kind!=3) {       
        actAst =asT;
        workingAst=workingSource.parse_statement(sC,scopeL);
    } else {
        workingAst = asT;
        
        if(kind==3) {
            inside = 1;
        }
    }
    
    std::string actWord;
    TraverseASTFunctor4LocateUse expr_traverse(scopeL);
    ObjectList<AST_t> expr_list = workingAst.depth_subtrees(expr_traverse);
    for (ObjectList<AST_t>::iterator it = expr_list.begin();it != expr_list.end(); it++, l++) {
        
        
        
        f=0; 
        
        Expression expr(expr_list[l], scopeL);
        
        std::string ppExpr = expr.prettyprint();
        cout<<"-"<<ppExpr<<"-"<<endl;
        Source deleteComma;
        //        if(ppExpr.find_first_of(";")>0&&ppExpr.find_first_of(";")<ppExpr.length()) {
        //            deleteComma = ppExpr.substr(0,ppExpr.find_first_of(";"));
        //            Expression e(deleteComma.parse_statement(expr_list[l],scopeL),scopeL);
        //            if(e.is_valid()){
        //                if(e.is_function_call()) {
        //                    cout<<"function call: "<<std::string(deleteComma)<<endl;
        //                    cin.get();
        //                }
        //            }
        //            
        //        }
        //        cin.get();
        //
        lastAst = expr.get_ast();
        if(kind!=2 && kind!=3) {
            line = offsetLine;
        } else if(kind!=3){
            actAst = expr_list[l];
            line = offsetLine+l;
        } else {
            line = offsetLine;
            kind=1;
            actAst = prevAST;              
        }
        
        
        cout<<"Studied expression("<<l<<"/"<<expr_list.size()<<")"<<endl;
        //        cout<<ppExpr<<endl;
        //        cout<<"L: "<<line<<endl;
        //        cout<<"OL: "<<outline_num_line<<endl;
        //        cin.get();
        if(kind!=1) {
            
            if(line < outline_num_line) {
                _insideMaster = is_inside_master(expr_list[l],scopeL, line, 0);
                if(_insideMaster) {
                    cout<<expr.prettyprint()<<" is inside master"<<endl;

                } else {
                    cout<<expr.prettyprint()<<" is not inside master"<<endl;  
                }
                //            cin.get();
            }
        } else {
            // _insideMaster = is_inside_master(expr_list[l],scopeL, line, 0);
            if(_insideMaster) {
                cout<<"Expression on function: "<<expr.prettyprint()<<" is inside master"<<endl;

            } else {
                cout<<"Expression on function: "<<expr.prettyprint()<<" is not inside master"<<endl;  
            }
        }
        //Check if is inside Master(slave does not have the updated value) or next reads/writes 
        if(_insideMaster || line > outline_num_line) {
            
            
            if(line!=outline_num_line) {
                if((expr.is_assignment() || expr.is_operation_assignment()) && f==0) {
                    cout<<"Operation assignment: "<<ppExpr<<endl;
                    f=1; 
                    if(kind == 2) 
                        _inside_loop=is_inside_bucle(expr_list[l],scopeL, line, 0);
                    Expression firstOperand = expr.get_first_operand();
                    
                    Expression secondOperand = expr.get_second_operand();
                    
                    Source cutParam;
                    size_t EndPart1 = std::string(firstOperand.prettyprint()).find_first_of("[");
                    if(EndPart1>=0 && EndPart1<std::string(firstOperand.prettyprint()).length()) {
                        cutParam << std::string(std::string(firstOperand.prettyprint()).substr(0, EndPart1));
                    } else {
                        cutParam << std::string(firstOperand.prettyprint());
                    }
                    
                    while(std::string(cutParam).find_first_of(" ")==0)
                        std::string(cutParam) = std::string(cutParam).substr(1,std::string(cutParam).length());
                    while(std::string(cutParam).find_first_of(" ")<std::string(cutParam).length())
                        std::string(cutParam) = std::string(cutParam).substr(0,std::string(cutParam).length()-1);
                    
                    
                    Symbol findedS = sC.get_symbol_from_name(std::string(cutParam));
                    if(!findedS.is_invalid()) {
                        actWord = findedS.get_name();
                        
                        //                    std::cout<<"(ass)Var use "<< findedS.get_name()<<" in "<<line<<endl;
                        if(line<outline_num_line) {
                            
                            if(!kind || kind == 2) {
                                if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                    if(_insideMaster) {
                                        _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                                    }
                                }
                            } else {
                                if(inside) {
                                    if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                        if(_insideMaster) {
                                            _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                                        }
                                    }
                                }
                            }
                        } else {
                            if(!kind || kind == 2) {
                                if((_smart_use_table[actWord].row_first_write_cpu.row > line || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)) {
                                    _smart_use_table[actWord].row_first_write_cpu = fill_use(line,actAst);    
                                }
                            } 
                            
                        }
                    }
                    
                    //} 
                    ObjectList<Source> operands;
                    operands = splitMathExpression(sC, secondOperand.prettyprint(), 0);
                    //                    std::cout<<"-----------SO:"<< expr_list[l].prettyprint()<<"--------------"<<endl;
                    for (int e=0;e<operands.size();e++){
                        //                        std::cout<<"e: "<<std::string(operands[e])<<endl;
                        EndPart1 = std::string(operands[e]).find_first_of("[");
                        Source cutParam;
                        if(EndPart1>0 && EndPart1<std::string(operands[e]).length()) {
                            cutParam << std::string(std::string(operands[e]).substr(0, EndPart1));
                        } else {
                            cutParam << std::string(std::string(operands[e]));
                        }
                        //                        std::cout<<"-"<<std::string(cutParam)<<"-"<<endl;
                        while(std::string(cutParam).find_first_of(" ")==0){                       
                            cutParam = std::string(cutParam).substr(1,std::string(cutParam).length());
                            //      std::cout<<"-"<<std::string(cutParam)<<"-"<<endl;
                        }
                        
                        while(std::string(cutParam).find_first_of(" ")<std::string(cutParam).length()){
                            cutParam = std::string(cutParam).substr(0,std::string(cutParam).length()-1);
                            //     
                        }
                        //                        std::cout<<"-"<<std::string(cutParam)<<"-"<<endl;
                        //Symbol paramSym = scope_of_decls.get_symbol_from_name(std::string(cutParam));
                        Symbol findedS = sC.get_symbol_from_name(std::string(cutParam));
                        if(!findedS.is_invalid()) {
                            //                            cout<<"Valid:"<<std::string(cutParam)<<endl;
                            actWord = findedS.get_name();
                            if(line<outline_num_line) {
                                if(!kind || kind == 2) {
                                    if((_smart_use_table[actWord].row_last_read_cpu.row < line || _smart_use_table[actWord].row_last_read_cpu.row == 0) && isParam(actWord)) {
                                        _smart_use_table[actWord].row_last_read_cpu = fill_use(line,actAst);
                                    }
                                }  
                            } else {
                                if(!kind || kind == 2) {
                                    if((_smart_use_table[actWord].row_first_read_cpu.row > line || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)) {
                                        _smart_use_table[actWord].row_first_read_cpu = fill_use(line,actAst);
                                    }
                                } 
                                
                            }
                        }
                        
                        // } 
                    }
                    //                                    
                    
                }
                
                PragmaCustomConstruct test(expr.get_ast(),expr.get_scope_link());
                if(test.is_construct() && f==0 && outline_num_line !=line){
                    cout<<"Detected Future MPI work"<<endl;
                    f=1;
                    if(kind == 2) 
                        _inside_loop=is_inside_bucle(expr_list[l],scopeL, line, 0);
                    
                    
                    
                    std::istringstream actASTtext(test.prettyprint());
                    std::string lineAct;    
                    signed int maxLinePragma=line+offsetLine;
                    Source workingSource;
                    int h=0;
                    while (std::getline(actASTtext, lineAct)) {
                        if(h>0)
                            workingSource <<lineAct<<"\n";
                        maxLinePragma++;
                        h++;
                    }
                    //                std::cout<<line<<endl;
                    TL::PragmaCustomClause shared_clause = test.get_clause("shared");
                    TL::PragmaCustomClause private_clause = test.get_clause("private");
                    TL::PragmaCustomClause red_clause = test.get_clause("reduction");
                    TL::PragmaCustomClause check_clause = test.get_clause("check");
                    TL::PragmaCustomClause fixed_clause = test.get_clause("fixed");
                    int hmpp=0;
                    if(shared_clause.is_defined()) {
                        ObjectList<Expression> shared_arguments = shared_clause.get_expression_list();
                        for (ObjectList<Expression>::iterator it = shared_arguments.begin(); it != shared_arguments.end(); it++) {
                            Expression argument(*it);
                            actWord = argument.prettyprint();
                            //                        cout << "//  S: " << argument.prettyprint() << endl;
                            if(!hmpp && kind!=1) {
                                if((_smart_use_table[actWord].row_first_read_cpu.row>offsetLine || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)){
                                    _smart_use_table[actWord].row_first_read_cpu = fill_use(offsetLine,actAst);
                                }
                                if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                    _smart_use_table[actWord].row_first_write_cpu = fill_use(offsetLine,actAst);
                                    
                                }
                                
                            } else {
                                if(inside) {
                                    if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                        _smart_use_table[actWord].row_first_write_cpu = fill_use(maxLinePragma,actAst);
                                    }
                                }
                                
                                
                            }
                        }
                    }
                    if(private_clause.is_defined()) {
                        ObjectList<Expression> private_arguments = private_clause.get_expression_list();
                        for (ObjectList<Expression>::iterator it = private_arguments.begin(); it != private_arguments.end(); it++) {
                            Expression argument(*it);
                            actWord = argument.prettyprint();
                            //                        cout << "//  P: " << argument.prettyprint() << endl;
                            if(!hmpp && kind!=1) {
                                
                                if((_smart_use_table[actWord].row_first_read_cpu.row>offsetLine || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)){
                                    _smart_use_table[actWord].row_first_read_cpu = fill_use(offsetLine,actAst);
                                    
                                }
                                if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                    _smart_use_table[actWord].row_first_write_cpu = fill_use(offsetLine,actAst);
                                }
                                
                            } else {
                                if(inside) {
                                    if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                        _smart_use_table[actWord].row_first_write_cpu = fill_use(maxLinePragma,actAst);
                                        
                                    }
                                }
                                
                            }
                        }
                    }
                    if(red_clause.is_defined()) {
                        ObjectList<std::string> red_args = red_clause.get_arguments();
                        for (ObjectList<std::string>::iterator it = red_args.begin(); it != red_args.end(); it++) {
                            string argument(*it);
                            string actArgList;
                            while(argument.find(":")>=0 && argument.find(":")<argument.length()){
                                actArgList=argument.substr(argument.find_first_of(":")+1,argument.length());
                                argument = actArgList;
                                string actArg;
                                while(actArgList.find(",")>=0 && actArgList.find(",")<actArgList.length()) {
                                    actArg=actArgList.substr(0,actArgList.find_first_of(","));
                                    actArgList = actArgList.substr(actArgList.find_first_of(",")+1,actArgList.length());
                                    while(actArg.find_first_of(" ")==0)
                                        actArg = actArg.substr(1,actArg.length());
                                    while(actArg.find_first_of(" ")<actArg.length())
                                        actArg = actArg.substr(0,actArg.length()-1);
                                    //                                cout << "//  R1:  " << actArg << endl;
                                    actWord=actArg;
                                    if(!hmpp && kind!=1) {
                                        if((_smart_use_table[actWord].row_first_read_cpu.row>offsetLine || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)){
                                            _smart_use_table[actWord].row_first_read_cpu = fill_use(offsetLine,actAst);
                                            
                                        }
                                        if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                            _smart_use_table[actWord].row_first_write_cpu = fill_use(offsetLine,actAst);
                                        }
                                        
                                    } else {
                                        if(inside) {
                                            if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                                _smart_use_table[actWord].row_first_write_cpu = fill_use(maxLinePragma,actAst);
                                            }
                                        }
                                        
                                    }
                                }
                                actArg=actArgList;
                                while(actArg.find_first_of(" ")==0)
                                    actArg = actArg.substr(1,actArg.length());
                                while(actArg.find_first_of(" ")<actArg.length())
                                    actArg = actArg.substr(0,actArg.length()-1);
                                //                            cout << "//  R2:  " << actArg << endl;
                                actWord=actArg;
                                if(!hmpp && kind!=1) {
                                    if((_smart_use_table[actWord].row_first_read_cpu.row>offsetLine || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)){
                                        _smart_use_table[actWord].row_first_read_cpu = fill_use(offsetLine,actAst);
                                    }
                                    if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                        _smart_use_table[actWord].row_first_write_cpu = fill_use(offsetLine,actAst);
                                    }
                                    
                                } else {
                                    if(inside) {
                                        if((_smart_use_table[actWord].row_first_write_cpu.row>offsetLine || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)){
                                            _smart_use_table[actWord].row_first_write_cpu = fill_use(maxLinePragma,actAst);
                                        }
                                    }
                                    
                                }
                            }
                            
                        }
                    }
                    cout<<"------------------"<<endl;
                    AST_t nouse =fill_smart_use_table(test.get_ast(), scopeL, sC, outline_num_line, prmters, hmpp, line, actAst);
                    
                }
                if(ppExpr.find("MPI_Send")==0) {
                    cout<<"MPI_Send detected"<<endl;
                    string actWord = ppExpr.substr(0,ppExpr.find_first_of(","));
                    actWord = actWord.substr(actWord.find_first_of("&")+1, actWord.length());
                    if(actWord.find("[")>=0 && actWord.find("[")<actWord.length())
                        actWord = actWord.substr(0,actWord.find_first_of("["));
                    actWord = cleanWhiteSpaces(actWord);
                    // cout<<actWord;
                    //cin.get();
                    f=1;
                    if(line<outline_num_line) {
                        if(!kind || kind == 2) {
                            if((_smart_use_table[actWord].row_last_read_cpu.row < line || _smart_use_table[actWord].row_last_read_cpu.row == 0) && isParam(actWord)) {
                                _smart_use_table[actWord].row_last_read_cpu = fill_use(line,actAst);
                            }
                        } 
                    }
                }
                if(ppExpr.find("MPI_Recv")==0) {
                    cout<<"MPI_Recv detected"<<endl;
                    string actWord = ppExpr.substr(0,ppExpr.find_first_of(","));
                    actWord = actWord.substr(actWord.find_first_of("&")+1, actWord.length());
                    if(actWord.find("[")>=0 && actWord.find("[")<actWord.length())
                        actWord = actWord.substr(0,actWord.find_first_of("["));
                    actWord = cleanWhiteSpaces(actWord);
                    // cout<<actWord;
                    //cin.get();
                    f=1;
                    if(line<outline_num_line) {
                        if(!kind || kind == 2) {
                            if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                if(_insideMaster)
                                    _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                            }
                        } else {
                            
                            if(inside) {
                                if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                    if(_insideMaster)
                                        _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                                }
                            }
                        }
                    }
                }
                //                if(insideMaster) {
                   
              //This tries to solve Mercurium Errors on parsing
                if(!expr.is_function_call() && f == 0) {
                    TraverseASTFunctor4LocateFunction expr_traverseFunc(scopeL);
                    ObjectList<AST_t> expr_listFunc = expr_list[l].depth_subtrees(expr_traverseFunc);
                    if(expr_listFunc.size()>0) {
                        Expression exprUndetected(expr_listFunc[0], _ifScopeL);
                        cout<<exprUndetected.get_called_expression().prettyprint()<<endl;
                        Symbol sym = sC.get_symbol_from_name(exprUndetected.get_called_expression().prettyprint());
                        if(sym.is_defined()){
                            FunctionDefinition fD(sym.get_definition_tree(),_scope_link);
//                            cout<<"S: "<<fD.get_function_body().get_ast()<<endl;
//                            cin.get();
//                            f=1;
                            cout<<"------------------"<<endl;
                            fill_smart_use_table(fD.get_function_body().get_ast(), fD.get_scope_link(), fD.get_scope(), outline_num_line, prmters, 3, line, actAst);
                            cout<<"------------------"<<endl;
                        }
//                        cin.get();
                        //expr = exprUndetected;
                    }
                }
                    
                if(expr.is_function_call()&& f==0){
                    
                    //Symbol functionS = expr.get_symbol();
//                    IdExpression id_expr = expr.get_id_expression();
//                    cout<<id_expr.get_declaration().prettyprint()<<endl;
//                    cin.get();
//                    Symbol called_sym = .get_computed_symbol();//id_expr.get_symbol();
//                    if(called_sym.is_valid()){
//                        cout<<called_sym.get_name()<<endl;
//                        cin.get();
//                    }
                    //scopeL.get_scope(expr_list[l]).get_symbol_from_name()
//                    if(functionS.is_defined()){
//                        cout<<"Possible work to do with: "<< functionS.get_name()<<endl;
//                        cin.get();
//                    }
                    
                    f=1;
                    
                    if(kind == 2) 
                        _inside_loop=is_inside_bucle(expr_list[l],scopeL, line, 0);
                    std::string exprS =expr.prettyprint();
                    
                    exprS = exprS.substr(exprS.find_first_of("(")+1, exprS.length());
                    exprS = exprS.substr(0,exprS.find_last_of(")"));
                    
//                    exprS = cleanWhiteSpaces(exprS);
//                                        cout<<expr.prettyprint()<<" is function call"<<endl;
//                                        cout<<"-"<<exprS<<"-"<<endl;
//                                        cin.get();
                    if(exprS.compare("")!=0) {
                        
                        
                        std::string actWord;
                        while(exprS.find_first_of(",")>0 && exprS.find_first_of(",")<exprS.length()){
                            actWord = exprS.substr(0,exprS.find_first_of(","));
                            if((exprS.find_first_of("\"")<0 || exprS.find_first_of("\"")>exprS.length()) && actWord.compare("")!=0) {
                                actWord = cleanWhiteSpaces(actWord);
                                if(actWord.find_first_of("[")>=0 && actWord.find_first_of("[")<actWord.length())
                                    actWord = actWord.substr(0,actWord.find_first_of("["));
                                if(line<outline_num_line) {
                                    if(!kind || kind == 2) {
                                        if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                            if(_insideMaster)
                                                _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                                        }
                                        if((_smart_use_table[actWord].row_last_read_cpu.row < line || _smart_use_table[actWord].row_last_read_cpu.row == 0) && isParam(actWord)) {
                                            _smart_use_table[actWord].row_last_read_cpu = fill_use(line,actAst);
                                        }
                                    } else {
                                        
                                        if(inside) {
                                            if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                                if(_insideMaster)
                                                    _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                                            }
                                        }
                                    }
                                } else {
                                    if(!kind || kind == 2) {
                                        if((_smart_use_table[actWord].row_first_write_cpu.row > line || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)) {
                                            _smart_use_table[actWord].row_first_write_cpu = fill_use(line,actAst);    
                                            
                                        }
                                        if((_smart_use_table[actWord].row_first_read_cpu.row > line || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)) {
                                            _smart_use_table[actWord].row_first_read_cpu = fill_use(line,actAst);    
                                        }
                                    } else {
                                        
                                        if(inside) {
                                            if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                                if(_insideMaster)
                                                    _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                            }
                                        }
                                    }
                                }
                            }
                            exprS = exprS.substr(exprS.find_first_of(",")+1,exprS.length());
                        }
                        actWord = exprS;
                        if((exprS.find("\"")<0 || exprS.find_first_of("\"")>exprS.length()) && actWord.compare("")!=0){
                            actWord = cleanWhiteSpaces(actWord);
                            if(actWord.find_first_of("[")>=0 && actWord.find_first_of("[")<actWord.length())
                                actWord = actWord.substr(0,actWord.find_first_of("["));
                            if(line<outline_num_line) {
                                if(!kind || kind == 2) {
                                    if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                        _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                    }
                                    if((_smart_use_table[actWord].row_last_read_cpu.row < line || _smart_use_table[actWord].row_last_read_cpu.row == 0) && isParam(actWord)) {
                                        _smart_use_table[actWord].row_last_read_cpu = fill_use(line,actAst); 
                                    }
                                } else {
                                    
                                    if(inside) {
                                        if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                            if(_insideMaster)
                                                _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                        }
                                    }
                                }
                            } else {
                                if(!kind || kind == 2) {
                                    if((_smart_use_table[actWord].row_first_write_cpu.row > line || _smart_use_table[actWord].row_first_write_cpu.row == 0) && isParam(actWord)) {
                                        if(_insideMaster)
                                            _smart_use_table[actWord].row_first_write_cpu = fill_use(line,actAst); 
                                    }
                                    if((_smart_use_table[actWord].row_first_read_cpu.row > line || _smart_use_table[actWord].row_first_read_cpu.row == 0) && isParam(actWord)) {
                                        _smart_use_table[actWord].row_first_read_cpu = fill_use(line,actAst); 
                                    }
                                } else {
                                    
                                    if(inside) {
                                        if((_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) && isParam(actWord)) {
                                            if(_insideMaster)
                                                _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                        }
                                    }
                                }
                            }
                        }
                        
                    }
                    
                }
                
                stringstream equal;
                equal<<"[^<>][=][^=]";
                regex_t expEqual; //Our compiled expression
                int rev = regcomp(&expEqual, equal.str().c_str(), REG_EXTENDED);
                if (rev != 0) {
                    printf("regcomp failed with %d\n", rev);
                }
                regmatch_t matchesEqual[1]; //A list of the matches in the string (a list of 1)
                //cout<<"PP: " << ppExpr<<endl;
                
                if (f==0 && regexec(&expEqual, ppExpr.c_str(), 1, matchesEqual, 0) == 0){
                    cout<<"Uncertain expression"<<endl;
                    //                                    std::cout<<"regex expr: "<<ppExpr<<endl;
                    
                    
                    //                cout<<"PP1: " << ppExpr<<endl;
                    if(kind == 2)  
                        _inside_loop=is_inside_bucle(expr_list[l],scopeL, line, 0);
                    f=1;
                    if(prmters.size()>0){
                        k=0;
                        vector<string> sub_strings;
                        for (ObjectList<Symbol>::iterator it = prmters.begin();it != prmters.end(); it++,k++) {
                            //                        if(insideMaster) {
                            //                            cout <<expr_list[l].prettyprint()<< " is inside master work"<<endl;
                            //                            
                            //                        }
//                            cout<<"Looking 4: "<<prmters[k].get_name()<<" on: "<<ppExpr<<endl;
//                            cin.get();
                            //                        
                            // if(prmters[k].get_type().is_array() || (prmters[k].get_point_of_declaration().prettyprint(true).find_first_of("[")>=0 && prmters[k].get_point_of_declaration().prettyprint(true).find_first_of("[")<prmters[k].get_point_of_declaration().prettyprint(true).length())) {
                            stringstream pattern, pattern2,pattern3;
                            //pattern<<"[^a-zA-Z0-9]"<<prmters[k].get_name()<<"[^a-zA-Z0-9][ \r\t\n\f]*[\r\t\n\f]*";
                            //pattern2<<"[^a-zA-Z0-9]"<<prmters[k].get_name()<<"[^a-zA-Z0-9]\\s*\\[[\\d+]*[a-z]*\\]";
                            pattern<<"[^a-zA-Z0-9]"<<prmters[k].get_name()<<"[^a-zA-Z0-9=]";
                            pattern2<<"[ ]*[^a-zA-Z0-9]*"<<prmters[k].get_name()<<"[^a-zA-Z0-9=]*";
                            pattern3<<"[^a-zA-Z0-9]"<<prmters[k].get_name()<<"[^a-zA-Z0-9=]";
                            //                            std::cout<<"P: "<<pattern.str()<<endl;
                            int rv;
                            regex_t exp, exp2, exp3; //Our compiled expression
                            
                            rv = regcomp(&exp, pattern.str().c_str(), REG_EXTENDED);
                            if (rv != 0) {
                                printf("regcomp failed with %d\n", rv);
                            }
                            rv = regcomp(&exp2, pattern2.str().c_str(), REG_EXTENDED);
                            if (rv != 0) {
                                printf("regcomp failed with %d\n", rv);
                            }
                            rv = regcomp(&exp3, pattern3.str().c_str(), REG_EXTENDED);
                            if (rv != 0) {
                                printf("regcomp failed with %d\n", rv);
                            }
                            regmatch_t matches[1]; //A list of the matches in the string (a list of 1)
                            if(regexec(&exp, ppExpr.c_str(), 1, matches, 0) == 0 || 
                                    regexec(&exp2, ppExpr.c_str(), 1, matches, 0) == 0 || 
                                    regexec(&exp3, ppExpr.c_str(), 1, matches, 0) == 0) {    
                                
                                std::string actWord = prmters[k].get_name();
//                                cout<<actWord<<" found"<<endl;
//                                cin.get();
                                //                                
                                if(ppExpr.find(prmters[k].get_name())<ppExpr.find("=")) {
                                    
                                    if(line<outline_num_line) {
                                        if(!kind || kind==2){
                                            if(_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0 && isParam(actWord)) {
                                                if(_insideMaster)
                                                    _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                            }
                                        } else {
                                            
                                            if(inside) {
                                                if(_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0 && isParam(actWord)) {
                                                    if(_insideMaster)
                                                        _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                                }
                                            }
                                        }
                                    } else {
                                        if(!kind || kind==2){
                                            if(_smart_use_table[actWord].row_first_write_cpu.row > line || _smart_use_table[actWord].row_first_write_cpu.row == 0 && isParam(actWord)) {
                                                _smart_use_table[actWord].row_first_write_cpu = fill_use(line,actAst);
                                            }
                                        } 
                                    }
                                } else {
                                    //                                    std::cout<<"(read)"<<prmters[k].get_name()<<endl;
                                    if(line<outline_num_line) {
                                        if(!kind || kind==2){
                                            if(_smart_use_table[actWord].row_last_read_cpu.row < line || _smart_use_table[actWord].row_last_read_cpu.row == 0 && isParam(actWord)) {
                                                _smart_use_table[actWord].row_last_read_cpu = fill_use(line,actAst);
                                            }
                                        } else {
                                            if(inside) {
                                                if(_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0 && isParam(actWord)) {
                                                    if(_insideMaster)
                                                        _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst);
                                                }
                                            }
                                        }
                                    } else {
                                        if(!kind || kind==2){
                                            if(_smart_use_table[actWord].row_first_read_cpu.row > line || _smart_use_table[actWord].row_first_read_cpu.row == 0 && isParam(actWord)) {
                                                _smart_use_table[actWord].row_first_read_cpu = fill_use(line,actAst);
                                                
                                            }
                                        } 
                                    }
                                }
                                
                            }
                            
                            // }
                            
                        }
                    } 
                    
                }
                string r = "return";
                if(f==0 && ppExpr.substr(0,r.size()).compare(r)==0) {
                    cout<<"return detected"<<endl;
                    f==1;              
                    actWord = cleanWhiteSpaces(ppExpr.substr(r.size()+1,ppExpr.length()));
                    if(scopeL.get_scope(expr.get_ast()).get_symbol_from_name(actWord).is_valid()){
                        if(_smart_use_table[actWord].row_first_read_cpu.row > line || _smart_use_table[actWord].row_first_read_cpu.row == 0) {
                            _smart_use_table[actWord].row_first_read_cpu = fill_use(line,actAst);
                        }
                    }
                }
                if(f==0 && (ppExpr.find_first_of("++")>=0 && ppExpr.find_first_of("++")<ppExpr.length() ||
                        ppExpr.find_first_of("--")>=0 && ppExpr.find_first_of("--")<ppExpr.length())) {
                    f==1;
                    cout<<"increment/decrement expression"<<endl;
                    if(ppExpr.find("++")==0) {
                        actWord = ppExpr.substr(2,ppExpr.length());
                    } else if(ppExpr.find("++")==(ppExpr.length()-2)) {
                        actWord = ppExpr.substr(0,ppExpr.length()-2);
                    } else if(ppExpr.find("--")==0) {
                        actWord = ppExpr.substr(2,ppExpr.length());
                    } else if(ppExpr.find("--")==(ppExpr.length()-2)) {
                        actWord = actWord.substr(0,ppExpr.length()-2);
                    }
                    if(actWord.find_first_of("[")>= 0 && actWord.find_first_of("[")<actWord.length()) {
                        actWord = actWord.substr(0,actWord.find_first_of("["));
                        
                    }  
                    actWord = cleanWhiteSpaces(actWord);
                    if(line<outline_num_line) {
                        if(!kind || kind==2){
                            if(_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) {
                                if(_insideMaster)
                                    _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                            }
                        } else {
                            
                            if(inside) {
                                if(_smart_use_table[actWord].row_last_write_cpu.row < line || _smart_use_table[actWord].row_last_write_cpu.row == 0) {
                                    if(_insideMaster)
                                        _smart_use_table[actWord].row_last_write_cpu = fill_use(line,actAst); 
                                }
                            }
                        }
                    } else {
                        if(!kind || kind==2){
                            if(_smart_use_table[actWord].row_first_write_cpu.row > line || _smart_use_table[actWord].row_first_write_cpu.row == 0) {
                                _smart_use_table[actWord].row_first_write_cpu = fill_use(line,actAst);
                            }
                            if(_smart_use_table[actWord].row_first_read_cpu.row > line || _smart_use_table[actWord].row_first_read_cpu.row == 0) {
                                _smart_use_table[actWord].row_first_read_cpu = fill_use(line,actAst);
                            }
                        } 
                    }
                    
                }
                if(inside){
                    kind=3;
                }
                //                cin.get();
                
            }
        }
    }
    
    for (Mymap::iterator itSm = _smart_use_table.begin(); 
            itSm != _smart_use_table.end(); ++itSm) {
        if(itSm->second.row_first_read_cpu.row==0) {
            itSm->second.row_first_read_cpu.ast=asT; 
            itSm->second.row_first_read_cpu.inside_loop=0; 
            itSm->second.row_first_read_cpu.for_num=-1; 
            itSm->second.row_first_read_cpu.for_ast = NULL;
        }
        if(itSm->second.row_first_write_cpu.row==0) {
            itSm->second.row_first_write_cpu.ast=asT; 
            itSm->second.row_first_write_cpu.inside_loop=0; 
            itSm->second.row_first_write_cpu.for_num=-1; 
            itSm->second.row_first_write_cpu.for_ast = NULL;
        }
    }
    return lastAst;
}

int TransPhase::isParam(string p2check){
    if(_divideWork) {
        for(int i=0;i<_prmters.size();++i){
            if(_prmters[i].get_name().compare(p2check)==0)
                return 1;
        }
        return 0;
    }
        
    return 1;
}

ObjectList<Source> TransPhase::splitMathExpression(Scope sC,std::string secondO, int includeIterators)
{
    //    std::cout<<"Second Operator: "<<secondO<<endl;
    ObjectList<Source> operators;
    int numElem=0;
    Source empty;
    string math[11] = {"+","*","/","-","<",">","=","?",":","&","|"};
    operators.clear();
    operators.push_back(empty);
    int isInsideIndex = 0;
    for (int i=0;i<secondO.length();++i){
        std::string actChar,nextChar;
        actChar = (secondO[i]);
        int l = i+1;
        while(l < secondO.length()-1){
            if(secondO[l] != 32) {
                nextChar = secondO[l];
                l=secondO.length();
            } else {
                l++;
            }
        }
        int find=0;
        
        if(!(std::string(actChar).compare(")")==0 || std::string(actChar).compare(" ")==0  || std::string(actChar).compare("(")==0)) {
            for(int x=0; x<11;++x){
                if(std::string(actChar).compare(math[x])==0) {
                    find=1; 
                }
                if(math[x].compare("<")==0 || math[x].compare(">")==0) {
                    if(nextChar.compare("=")==0)
                        i++;
                    
                }
                if(math[x].compare("&")==0) {
                    if(nextChar.compare("&")==0)
                        i++;
                    
                }
                if(math[x].compare("|")==0 ) {
                    if(nextChar.compare("|")==0)
                        i++;
                    
                }
                if(math[x].compare("<")==0) {
                    if(nextChar.compare("<")==0) {
                        i++;
                    }
                    
                }
                if(math[x].compare("-")==0) {
                    if(nextChar.compare(">")==0) {
                        //                        cout<<"HI!"<<endl;
                        i++;
                        find = 0;
                    }
                    
                }
                
            }
            if(includeIterators){
                if(std::string(actChar).compare("[")==0) {
                    isInsideIndex++;
                }
                if(std::string(actChar).compare("]")==0) {
                    isInsideIndex--;
                }
                //                cout<<"F: "<< find <<" inside: "<<isInsideIndex<<endl;
            } else {
                if(std::string(actChar).compare("[")==0 || std::string(actChar).compare("]")==0) {
                    find =1;
                }
            }
            if(!find || isInsideIndex>0){
                Source actElem;
                actElem = operators[numElem];
                actElem<<actChar;
                operators.pop_back();
                operators.push_back(actElem);
                //                cout<<std::string(actElem)<<endl;
                //                
                Symbol findedS = sC.get_symbol_from_name(std::string(operators[numElem]));
                
                if(!findedS.is_invalid()) {
                    if(findedS.is_function()) {
                        if(nextChar.compare("(")==0) {
                            //                                std::cout<<std::string(operators[numElem])<<" discarted is function!!"<<endl;
                            operators[numElem]=empty;
                        }
                    }
                }
                
            }else if(std::string(operators[numElem]).compare(std::string(empty))!=0){
                operators.push_back(empty);
                numElem++;           
                operators[numElem]=empty;
                
            }
        } else if(std::string(actChar).compare(")")==0 && std::string(operators[numElem]).compare(std::string(empty))!=0){
            operators.push_back(empty);
            numElem++;           
            operators[numElem]=empty;
        }
        
    }
    if(std::string(operators[0]).compare("")==0) {
        operators.clear();
    }
    return operators;
}



TransPhase::use TransPhase::fill_use(int line, AST_t actAst){
    use actUse;
    actUse.row=line;
    actUse.ast=actAst;
    actUse.inside_loop = _inside_loop;
    actUse.for_num = _for_num;
    actUse.for_ast = _for_ast;
    actUse.for_internal_ast_last = _for_internal_ast_last;
    return actUse;
    
}

int TransPhase::is_inside_bucle(AST_t ast2check, ScopeLink scopeL, int exprLine, int searching_construct) {
    
    TraverseASTFunctor4LocateFor expr_traverseFor(scopeL);
    ObjectList<AST_t> expr_listFor = _file_tree.depth_subtrees(expr_traverseFor);
    _for_min_line =-1;
    int lF=0;
    int num_for=-1;
    for (ObjectList<AST_t>::iterator it = expr_listFor.begin();it != expr_listFor.end(); it++, lF++) {
        
        Expression exprI(ast2check, scopeL);
        
        if(expr_listFor[lF].is_valid()) {
            Expression exprF(expr_listFor[lF], scopeL);
            
            FunctionDefinition fdF(exprF.get_enclosing_function());
            FunctionDefinition fdI(exprI.get_enclosing_function());
            
            string nameF = fdF.get_function_name().get_symbol().get_name();
            string nameI = fdI.get_function_name().get_symbol().get_name();
            
            //cout <<"nF: -"<<nameF<<"- vs nI: -"<<nameI<<"-"<<endl;
            if (nameF.compare(nameI)==0){
                //cout<<"******************************\nFOR: "<<exprF.prettyprint()<<endl;
                AST_t loopAst;
                Statement s(expr_listFor[lF],scopeL);
                if(ForStatement::predicate(expr_listFor[lF])) {
                    ForStatement fS(s);
                    loopAst = fS.get_loop_body().get_ast();
                    
                }
                
                if(WhileStatement::predicate(expr_listFor[lF])) {
                    WhileStatement wS(expr_listFor[lF],scopeL);
                    loopAst = wS.get_body().get_ast();
                    
                }
                if(DoWhileStatement::predicate(expr_listFor[lF])) {
                    DoWhileStatement dWS(expr_listFor[lF],scopeL);
                    loopAst = dWS.get_body().get_ast();
                }
                if(loopAst.prettyprint().compare("")!=0 && _for_min_line==-1){
                    
                    _for_min_line = get_real_line(loopAst, scopeL, exprI.get_ast(), 0, searching_construct,0);
                    //cout<<"LS: "<<_for_min_line<<"***********************"<<endl;
                    if(_for_min_line>=0) {
                        _for_internal_ast_last = get_last_ast(loopAst, scopeL);
                        _for_internal_ast_first = get_first_ast(loopAst, scopeL);
                        loopAst = loopAst.get_enclosing_function_definition_declaration();
                        _for_min_line = get_real_line(loopAst, scopeL, exprI.get_ast(), 0, searching_construct,0);
                        if(searching_construct) {
                            _for_min_line-=_notOutlined;
                            _for_min_line-=_pragma_lines;
                        }
                        num_for= expr_listFor[lF].get_line();
                        _for_ast = expr_listFor[lF];
                    }
                }
            }
        }
        
        
    }
    if(_for_min_line==exprLine){
        _for_num = num_for;
        return 1;
    }else{
        _for_num = -1;
        return 0;
    }
}

int TransPhase::is_inside_master(AST_t ast2check, ScopeLink scopeL, int exprLine, int searching_construct) {
    
    TraverseASTFunctor4LocateIf expr_traverseIf(scopeL);
    ObjectList<AST_t> expr_listIf = _file_tree.depth_subtrees(expr_traverseIf);
    int lF=0;
    
    //    cout<<"Looking 4 expression: "<<ast2check.prettyprint() <<"("<<exprLine<<")"<<endl;
    int numIF = 0;
    int numMasterIf = -1;
    for (ObjectList<AST_t>::iterator it = expr_listIf.begin();it != expr_listIf.end(); it++, lF++) {
        Expression exprI(ast2check, scopeL);
        IfStatement iS(expr_listIf[lF],scopeL);
        AST_t ifAST;
        ifAST = iS.get_then_body().get_ast();
        string myIDcomparission = _myidVar+" == 0";
        if(iS.get_condition().prettyprint().compare(myIDcomparission)==0) {
            //                        cout<<"Master Work if found"<<endl;
            //                        cout<<iS.get_ast().prettyprint()<<endl;
            //                        cin.get();
            numMasterIf++;
            Expression exprF(expr_listIf[lF], scopeL);
            
            FunctionDefinition fdF(exprF.get_enclosing_function());
            FunctionDefinition fdI(exprI.get_enclosing_function());
            
            string nameF = fdF.get_function_name().get_symbol().get_name();
            string nameI = fdI.get_function_name().get_symbol().get_name();
            
            //            cout <<"nF: -"<<nameF<<"- vs nI: -"<<nameI<<"-"<<endl;
            if (nameF.compare(nameI)==0){
                numIF++;
                TraverseASTFunctor4LocateUse expr_traverseUse(scopeL);
                ObjectList<AST_t> expr_listUse = ifAST.depth_subtrees(expr_traverseUse);
                int lU = 0;
                for (ObjectList<AST_t>::iterator it = expr_listUse.begin();it != expr_listUse.end(); it++, lU++) {
                    Expression exprL(expr_listUse[lU], scopeL);
 
                    //cout<<"Checking vs expression: "<<expr_listUse[lU].prettyprint()<<"("<<checkExprLine<<")"<<endl;
                    if(ast2check.prettyprint().compare(expr_listUse[lU].prettyprint())==0) {
                        int checkExprLine =get_real_line(exprL.get_enclosing_function().get_function_body().get_ast(), scopeL, exprI.get_ast(), 0, 0,0);
                        
                       // checkExprLine+=numIF+(_num_transformed_blocks)-numMasterIf+2;
//                                                cout<<"1: "<<expr_listUse[lU].prettyprint()<<" - "<<exprLine<<endl;
//                                                cout<<"2: "<<ast2check.prettyprint()<<" - "<<checkExprLine<<endl;
//                                                cout<<"3: "<<numMasterIf<<endl;
//                                                cin.get();
                        if(exprLine == checkExprLine) {
                            _ifScope = iS.get_scope();
                            _ifScopeL = iS.get_scope_link();
                            //cin.get();
                            return 1;
                            
                        }
                    }
                }
                
                
            }
        }
        
    }
    
    return 0;
    
}

int TransPhase::get_real_line(AST_t asT, ScopeLink scopeL, AST_t actLineAST, int update, int searching_construct, int initialConstruct) {
    std::string actLine;
    actLine= actLineAST.prettyprint();
    
    TraverseASTFunctor4LocateUse expr_traverse(scopeL);
    ObjectList<AST_t> expr_list = asT.depth_subtrees(expr_traverse);
    int line=-1;
    int l=0; 
    if(update) {
        _pragma_lines=0;
        p_l_s.clear();
    }
    for (ObjectList<AST_t>::iterator it = expr_list.begin();it != expr_list.end(); it++, l++) {
        Expression expr(expr_list[l], scopeL);
        std::string ppExpr;
        ppExpr=expr.prettyprint();
        if(update) {
            if(ppExpr.find("#pragma hmpp ")>=0 && ppExpr.find("#pragma hmpp ")<ppExpr.length()){
                if(ppExpr.find(" group")>0 && ppExpr.find(" group")<ppExpr.length()){
                    _pragma_lines++;
                    p_l_s.push_back(ppExpr);
                }
                if(ppExpr.find(" mapbyname,")>0 && ppExpr.find(" mapbyname,")<ppExpr.length()){
                    //                        cout<<ppExpr<<endl;
                    _pragma_lines++;
                    p_l_s.push_back(ppExpr);
                }
                if(ppExpr.find(" advancedload,")>0 && ppExpr.find(" advancedload,")<ppExpr.length()){
                    
                    _pragma_lines++;
                    p_l_s.push_back(ppExpr);
                }
                if(ppExpr.find(" delegatedstore,")>0 && ppExpr.find(" delegatedstore,")<ppExpr.length()){
                    //                        cout<<ppExpr<<endl;
                    _pragma_lines++; 
                    p_l_s.push_back(ppExpr);
                }
                
                if(ppExpr.find(" synchronize")>0 && ppExpr.find(" synchronize")<ppExpr.length()){
                    //                        cout<<ppExpr<<endl;
                    _pragma_lines++;
                    p_l_s.push_back(ppExpr);
                }
                
                if(ppExpr.find(" release")>0 && ppExpr.find(" release")<ppExpr.length()){
                    //                        cout<<ppExpr<<endl;
                    _pragma_lines++;
                    p_l_s.push_back(ppExpr);
                }
            }
        }
        if(actLine.compare(ppExpr)==0) {
            
            
            line = l;
            
            if(actLineAST.get_line() == expr_list[l].get_line() || searching_construct || actLineAST.get_line()==1){
                
                if(initialConstruct){
                    PragmaCustomConstruct test(actLineAST,scopeL);
                    if(test.is_construct()){
                        
                        TraverseASTFunctor4LocateUse expr_traverse2(scopeL);
                        
                        ObjectList<AST_t> expr_list2 = test.get_statement().get_ast().depth_subtrees(expr_traverse2);
                        //            if(searching_construct) {
                        //                            cout<<actLineAST.prettyprint()<<endl;
                        //                            if(expr_list2.size()>1) {
                        //                                line+=expr_list2.size();
                        //                                cout<<"Incrementing line in: "<<expr_list2.size()<<endl;
                        
                        //            }
                        //                            }
                        
                    }
                }
                //                cout<<line<<endl;
                //                cin.get();
                it = expr_list.end();
                break;
            }
        }  
    }
    return line;
    //return line+_num_transformed_blocks;
}
int TransPhase::iteratedVarCorrespondstoAnyVarIdx(string initVar, ObjectList<TL::Source> iter) {
    //    cout<<"-"<<initVar<<"-"<<endl;
    for(int i=0;i<iter.size();++i) {
        //        cout<<"vs -"<<std::string(iter[i])<<"-"<<endl;
        if(std::string(iter[i]).compare(initVar)==0)
            return 1;
    }
    return 0;
    
}
Source TransPhase::generateMPIVariableMessagesSend(vector<infoVar> vars, Source initVar, Scope functionScope, string dest, string offset, int withReduced) {
    Source mpiMessages;
    if(!_withMemoryLimitation) {
        for(int i = 0; i<vars.size(); ++i){
            
            //if(isINVar(std::string(vars[i].name))) {
            string upperType = std::string(vars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            cout<<"-----------"<<endl;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, vars[i].iterVar) || vars[i].size.size()<1) {
                varSent << std::string(_inVars[i].name)<<"["<<offset<<"]";
                size <<_partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
                
                
                
                
                if(functionScope.get_symbol_from_name(vars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(vars[i].name).get_type().is_pointer())
                    mpiMessages << "MPI_Send(&"<<varSent.str()<<" , "<<size.str()<<", MPI_"<<upperType<<","<<dest<<","<<_ATAG<<",MPI_COMM_WORLD);";
                else
                    mpiMessages << "MPI_Send(&"<<vars[i].name<<", 1, MPI_"<<upperType<<","<<dest<<","<<_ATAG<<",MPI_COMM_WORLD);";
                //}
            }
            //            if(std::string(_inVars[i].name).compare("B")==0)
            //                cin.get();
            
        }
    } else {
        for(int i = 0; i<vars.size(); ++i){
            if(vars[i].size.size()==0) {
                string upperType = std::string(vars[i].type);
                std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                mpiMessages << "MPI_Send(&"<<vars[i].name<<", 1, MPI_"<<upperType<<","<<dest<<","<<_ATAG<<",MPI_COMM_WORLD);";
            }
        }
    }
    if(withReduced) {
        for(int i = 0; i<_reducedVars.size(); ++i){
            string upperType = std::string(_reducedVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            if(std::string(_reducedVars[i].operation).compare("+") == 0 || std::string(_reducedVars[i].operation).compare("-") == 0) {
                mpiMessages<<_reducedVars[i].name << " = "<< "0;";
            }else{
                mpiMessages<<_reducedVars[i].name << " = "<< "1;";
            }
            mpiMessages<< "MPI_Send(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<","<<dest<<","<<_ATAG<<",MPI_COMM_WORLD);";
        }
    }
    return mpiMessages;
}

Source TransPhase::handleMemory(string source) {
    Source memorySource;
    int elseNeeded = 0;
    if(_inVars.size()>0) {
        elseNeeded = 1;
        memorySource << "if("<<_statVar<<".MPI_TAG == "<<_RTAG<<") {\n"
                "switch ("<<_partSizeVar<<") {\n";
        for (int i = 0; i< _inVars.size();++i){
            //if(_inVars[i].size.size()>0) {
            Source dimensions;
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            //if(_inVars[i].size.size()>0) {
            memorySource<< "case  "<<i<<": \n";
            if(_inVars[i].size.size()>0) {
                memorySource<<"MPI_Recv(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<_inVars[i].size.size()<<",MPI_INT,"<<source<<", "<<_RTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
            }
            for(int x=0; x<_inVars[i].size.size();++x) {
                dimensions<<"["<<_coordVectorVar<<_num_transformed_blocks<<"["<<x<<"]]";
            }
            memorySource << "MPI_Send(&"<<_inVars[i].name<<dimensions<<", 1, MPI_"<<upperType<<", "<<source<<", "<<_RTAG<<", MPI_COMM_WORLD);\n";
            memorySource << "break;\n";
            //}
            
            //}
            
        }
        memorySource<<"}\n }";
    }
    if(_ioVars.size()>0) {
        if(elseNeeded)
            memorySource<<"else "; 
        elseNeeded = 1;
        memorySource<<"if("<<_statVar<<".MPI_TAG == "<<_WTAG;
        if(_inVars.size()==0) {
            memorySource<<" || "<<_statVar<<".MPI_TAG == "<<_SWTAG;
        }
        memorySource<<") {\n switch ("<<_partSizeVar<<") {\n";
        for (int i = 0; i< _ioVars.size();++i){
            //if(_ioVars[i].size.size()>0) {
            Source dimensions;
            string upperType = std::string(_ioVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            //if(_ioVars[i].size.size()>0) {
            memorySource<< "case  "<<i<<": \n";
            if(_ioVars[i].size.size()>0) {
                memorySource<<"MPI_Recv(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<_ioVars[i].size.size()<<",MPI_INT,"<<source<<", "<<_WTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
            }
            
            for(int x=0; x<_ioVars[i].size.size();++x) {
                dimensions<<"["<<_coordVectorVar<<_num_transformed_blocks<<"["<<x<<"]]";
            }
            memorySource << "MPI_Recv(&"<<_ioVars[i].name<<dimensions<<", 1, MPI_"<<upperType<<", "<<source<<", "<<_WTAG<<", MPI_COMM_WORLD,&"<<_statVar<<");\n";
            
            
            memorySource << "break;\n";
            //}
            //}
        }
        memorySource<<"}\n }";
    }
    if(_ioVars.size()>0 && _inVars.size()>0){
        if(elseNeeded)
            memorySource<<"else "; 
        elseNeeded = 1;
        memorySource<<"if("<<_statVar<<".MPI_TAG == "<<_SWTAG<<") {\n"
                "switch ("<<_partSizeVar<<") {\n";
        for (int n = 0; n< _ioVars.size();++n){
            //if(_ioVars[i].size.size()>0) {
            Source dimensions;
            string upperType = std::string(_ioVars[n].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            //if(_ioVars[i].size.size()>0) {
            memorySource<< "case  "<<n<<": \n";
            if(_inVars.size()>0) {
                memorySource<<"do {\n"
                        <<"MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT, "<<source<<", MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");\n"
                        <<"if ("<<_statVar<<".MPI_TAG == RTAG) {\n"
                        <<"switch ("<<_partSizeVar<<") {\n";
                for (int i = 0; i< _inVars.size();++i){
                    //if(_inVars[i].size.size()>0) {
                    Source dimensions;
                    string upperType = std::string(_inVars[i].type);
                    std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
                    //if(_inVars[i].size.size()>0) {
                    memorySource<< "case  "<<i<<": ";
                    if(_inVars[i].size.size()>0) {
                        memorySource<<"MPI_Recv(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<_inVars[i].size.size()<<",MPI_INT,"<<source<<", "<<_RTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
                    }
                    for(int x=0; x<_inVars[i].size.size();++x) {
                        dimensions<<"["<<_coordVectorVar<<_num_transformed_blocks<<"["<<x<<"]]";
                    }
                    memorySource << "MPI_Send(&"<<_inVars[i].name<<dimensions<<", 1, MPI_"<<upperType<<", "<<source<<", "<<_RTAG<<", MPI_COMM_WORLD);\n";
                    memorySource << "break;\n";
                    //}
                    
                    //}
                }
                memorySource<<"}\n }\n }while("<<_statVar<<".MPI_TAG != "<<_WTAG<<");\n";
            }
            
            if(_ioVars[n].size.size()>0) {
                memorySource<<"MPI_Recv(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<_ioVars[n].size.size()<<",MPI_INT,"<<source<<", "<<_WTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
            }
            
            for(int x=0; x<_ioVars[n].size.size();++x) {
                dimensions<<"["<<_coordVectorVar<<_num_transformed_blocks<<"["<<x<<"]]";
            }
            memorySource << "MPI_Recv(&"<<_ioVars[n].name<<dimensions<<", 1, MPI_"<<upperType<<", "<<source<<", "<<_WTAG<<", MPI_COMM_WORLD,&"<<_statVar<<");\n";
            
            
            memorySource << "break;\n";
            //}
            //}
        }
        memorySource<<"}\n }";
    }
    if(_fullArrayReads && _inVars.size()>0) {
        if(elseNeeded)
            memorySource<<"else "; 
        elseNeeded = 1;
        memorySource<<"if("<<_statVar<<".MPI_TAG == "<<_FRTAG<<") {"
                "switch ("<<_partSizeVar<<") \n{";
        for (int i = 0; i< _inVars.size();++i){
            //if(_inVars[i].size.size()>0) {
            Source dimensions;
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            //if(_inVars[i].size.size()>0) {
            memorySource<< "case  "<<i<<": \n";
            if(_inVars[i].size.size()>0) {
                memorySource<<"MPI_Recv(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<_inVars[i].size.size()<<",MPI_INT,"<<source<<", "<<_FRTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
            }
            for(int x=1; x<_inVars[i].size.size();++x) {
                dimensions<<" * "<<std::string(_inVars[i].size[x]);
            }
            memorySource << "MPI_Send(&"<<_inVars[i].name<<"["<<_coordVectorVar<<_num_transformed_blocks<<"[0]]"<<", "<<_coordVectorVar<<_num_transformed_blocks<<"[1]"<<dimensions<<", MPI_"<<upperType<<", "<<source<<", "<<_FRTAG<<", MPI_COMM_WORLD);\n";
            memorySource << "break;";
            //}
            
            //}
        }
        memorySource<<"}\n } ";
    }
    
    if(_fullArrayWrites && _ioVars.size()>0) {
        if(elseNeeded)
            memorySource<<"else "; 
        elseNeeded = 1;
        memorySource<<"if("<<_statVar<<".MPI_TAG == "<<_FWTAG<<") {\n"
                "switch ("<<_partSizeVar<<") {\n";
        for (int i = 0; i< _ioVars.size();++i){
            //if(_inVars[i].size.size()>0) {
            Source dimensions;
            string upperType = std::string(_ioVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            //if(_inVars[i].size.size()>0) {
            memorySource<< "case  "<<i<<": \n";
            if(_ioVars[i].size.size()>0) {
                memorySource<<"MPI_Recv(&"<<_coordVectorVar<<_num_transformed_blocks<<","<<_ioVars[i].size.size()<<",MPI_INT,"<<source<<", "<<_FWTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
            }
            for(int x=1; x<_ioVars[i].size.size();++x) {
                dimensions<<" * "<<std::string(_ioVars[i].size[x]);
            }
            memorySource << "MPI_Recv(&"<<_ioVars[i].name<<"["<<_coordVectorVar<<_num_transformed_blocks<<"[0]]"<<", "<<_coordVectorVar<<_num_transformed_blocks<<"[1]"<<dimensions<<", MPI_"<<upperType<<", "<<source<<", "<<_FWTAG<<", MPI_COMM_WORLD, &"<<_statVar<<");\n";
            memorySource << "break;\n";
            //}
            
            //}
        }
        memorySource<<"}\n }";           
    }
    
    //    cout<<std::string(memorySource)<<endl;
    //    cin.get();
    return memorySource;
}
AST_t TransPhase::get_last_ast(AST_t ast, ScopeLink scopeL){
    TraverseASTFunctor4LocateUse expr_traverse(scopeL);
    ObjectList<AST_t> expr_list = ast.depth_subtrees(expr_traverse);
    return expr_list[expr_list.size()-1];
}

AST_t TransPhase::get_first_ast(AST_t ast, ScopeLink scopeL){
    TraverseASTFunctor4LocateUse expr_traverse(scopeL);
    ObjectList<AST_t> expr_list = ast.depth_subtrees(expr_traverse);
    return expr_list[0];
}
void TransPhase::useOldStyle(int staticC, Source mpiVariantStructurePart1, Source mpiVariantStructurePart2, Source mpiVariantStructurePart3, 
        string maxS, Source initVar, Scope functionScope, Source initValue, 
        Source conditionToWork, Source mpiFixStructurePart1, Source mpiFixStructurePart2, Statement function_body,
        PragmaCustomConstruct construct, Source constructASTS, Source initType){
    if(staticC!=0) {
        mpiVariantStructurePart1 << "for (int "<<_toVar<<"=1;"<<_toVar<<"<"<<_sizeVar<<";++"<<_toVar<<") {";
        mpiVariantStructurePart1 <<"if("<<_toVar<<"!="<<_sizeVar<<"-1) {";
        if(_inVars.size()!=0)
            mpiVariantStructurePart1 <<""<<_partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1);";
        mpiVariantStructurePart1 << ""<<_offsetVar<<" = "<<_partSizeVar<<" * ("<<_toVar<<"-1);"
                << "} else {";
        if(_inVars.size()!=0)
            mpiVariantStructurePart1 << ""<<_partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1) + "<<maxS <<"%"<<"("<<_sizeVar<<"-1) ;";
        mpiVariantStructurePart1 << ""<<_offsetVar<<" = " << maxS << "/ ("<<_sizeVar<<"-1) * ("<<_toVar<<"-1);"
                << "}";
        if(_inVars.size()==0)
            mpiVariantStructurePart1 << "MPI_Send(&"<<_offsetVar<<", 1, MPI_INT,"<<_toVar<<",ATAG,MPI_COMM_WORLD);";
        for(int i = 0; i<_inVars.size(); ++i){
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                varSent << std::string(_inVars[i].name)<<"["<<_offsetVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_inVars[i].name);
                stringstream ss;
                for(int x = 0;x<_inVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _inVars[i].size[x];
                    else
                        ss << "* "<<_inVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_pointer())
                mpiVariantStructurePart1 << "MPI_Send(&"<<varSent.str()<<" , "<<size.str()<<", MPI_"<<upperType<<","<<_toVar<<",ATAG,MPI_COMM_WORLD);";
            else
                mpiVariantStructurePart1 << "MPI_Send(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<","<<_toVar<<",ATAG,MPI_COMM_WORLD);";
        }
        for(int i = 0; i<_reducedVars.size(); ++i){
            string upperType = std::string(_reducedVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            if(std::string(_reducedVars[i].operation).compare("+") == 0 || std::string(_reducedVars[i].operation).compare("-") == 0) {
                mpiVariantStructurePart1<<_reducedVars[i].name << " = "<< "0;";
            }else{
                mpiVariantStructurePart1<<_reducedVars[i].name << " = "<< "1;";
            }
            mpiVariantStructurePart1<< "MPI_Send(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<","<<_toVar<<",ATAG,MPI_COMM_WORLD);";
        }
        mpiVariantStructurePart1 << "}";
        mpiVariantStructurePart1 << "for(int "<<_fromVar<<" = 1; "<<_fromVar<<"<"<<_sizeVar<<";++"<<_fromVar<<") {";
        if(_ioVars.size()>0) {
            mpiVariantStructurePart1 << "if("<<_fromVar<<"!="<<_sizeVar<<"-1) {"
                    << _partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1);"
                    << _offsetVar<<" = "<<_partSizeVar<<" * ("<<_fromVar<<"-1);"
                    << "} else {"
                    << _partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1) + "<<maxS <<"%"<<"("<<_sizeVar<<"-1) ;"
                    << _offsetVar<<" = " << maxS << "/ ("<<_sizeVar<<"-1) * ("<<_fromVar<<"-1);"
                    << "}";
        }
        for(int i = 0; i<_ioVars.size(); ++i){
            string upperType = std::string(_ioVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar)) {
                varSent << std::string(_ioVars[i].name)<<"["<<_offsetVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_ioVars[i].size.size();++x) {
                    size<<" * " <<_ioVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_ioVars[i].name);
                stringstream ss;
                for(int x = 0;x<_ioVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _ioVars[i].size[x];
                    else
                        ss << "* "<<_ioVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart1 << "MPI_Recv(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_fromVar<<",MPI_ANY_TAG,MPI_COMM_WORLD, &"<<_statVar<<");";
            } else {
                mpiVariantStructurePart1 << "MPI_Recv(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<","<<_fromVar<<",MPI_ANY_TAG,MPI_COMM_WORLD, &"<<_statVar<<");";
            }
        }
        for(int i = 0; i<_reducedVars.size(); ++i){
            string upperType = std::string(_reducedVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            mpiVariantStructurePart1<< "MPI_Recv(&work"<<_reducedVarsIndexStart+i<<", 1, MPI_"<<upperType<<", "<<_fromVar<<", MPI_ANY_TAG, MPI_COMM_WORLD,&"<<_statVar<<");";
            mpiVariantStructurePart1<< _reducedVars[i].name<<" "<<_reducedVars[i].operation<<"= work"<<_reducedVarsIndexStart+i<<";";
        }
        mpiVariantStructurePart1 << "}"
                << "for (int s = 0; s <"<<_sizeVar<<"; ++s) {"
                << " MPI_Send(&s, 1, MPI_INT, s,FTAG,MPI_COMM_WORLD);"
                <<"}";
    } else {
        mpiVariantStructurePart1 << "int "<<_followINVar<<" = "<<initValue<<"; int "<<_killedVar<<" = 0;"
                << "for (int "<<_toVar<<"=1; "<<_toVar<<"<"<<_sizeVar<<"; ++"<<_toVar<<") {"
                << "MPI_Send(&"<<_followINVar<<", 1, MPI_INT, "<<_toVar<<", ATAG, MPI_COMM_WORLD);"
                << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_toVar<<", ATAG, MPI_COMM_WORLD);";
        for(int i=0; i< _inVars.size(); ++i){
            string upperType = std::string(_inVars[0].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                varSent << std::string(_inVars[i].name)<<"["<<_followINVar<<"]";
                size <<_partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_inVars[i].name);
                stringstream ss;
                for(int x = 0;x<_inVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _inVars[i].size[x];
                    else
                        ss << "* "<<_inVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart1 << "MPI_Send(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_toVar<<",ATAG,MPI_COMM_WORLD);";
            } else {
                mpiVariantStructurePart1 << "MPI_Send(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<","<<_toVar<<",ATAG,MPI_COMM_WORLD);";
            }
        }
        mpiVariantStructurePart1 << ""<<_followINVar<<" += "<<_partSizeVar<<";"
                << "}"
                << " while(1){"
                << "MPI_Recv(&"<<_offsetVar<<", 1, MPI_INT, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");"
                << "int "<<_sourceVar<<" = "<<_statVar<<".MPI_SOURCE;"
                << "MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT, "<<_sourceVar<<", MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");";
        for(int i = 0; i<_ioVars.size(); ++i){
            string upperType = std::string(_ioVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar)) {
                varSent << std::string(_ioVars[i].name)<<"["<<_offsetVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_ioVars[i].size.size();++x) {
                    size<<" * " <<_ioVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_ioVars[i].name);
                stringstream ss;
                for(int x = 0;x<_ioVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _ioVars[i].size[x];
                    else
                        ss << "* "<<_ioVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart1 << "MPI_Recv(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_sourceVar<<",MPI_ANY_TAG,MPI_COMM_WORLD, &"<<_statVar<<");";
            } else {
                mpiVariantStructurePart1 << "MPI_Recv(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<","<<_sourceVar<<",MPI_ANY_TAG,MPI_COMM_WORLD, &"<<_statVar<<");";
            }
        }
        for(int i = 0; i<_reducedVars.size(); ++i){
            string upperType = std::string(_reducedVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            mpiVariantStructurePart1<< "MPI_Recv(&work"<<_reducedVarsIndexStart+i<<", 1, MPI_"<<upperType<<", "<<_sourceVar<<", MPI_ANY_TAG, MPI_COMM_WORLD,&"<<_statVar<<");";
            mpiVariantStructurePart1<< _reducedVars[i].name<<" "<<_reducedVars[i].operation<<"= work"<<_reducedVarsIndexStart+i<<";";
        }
        mpiVariantStructurePart1 << "if (("<<_followINVar<<"+"<<_partSizeVar<<") <"<<conditionToWork<<") {"
                << "MPI_Send(&"<<_followINVar<<", 1, MPI_INT, "<<_sourceVar<<", ATAG, MPI_COMM_WORLD);"
                << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_sourceVar<<", ATAG, MPI_COMM_WORLD);";
        for(int i = 0; i<_inVars.size(); ++i){
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                varSent << std::string(_inVars[i].name)<<"["<<_followINVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_inVars[i].name);
                stringstream ss;
                for(int x = 0;x<_inVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _inVars[i].size[x];
                    else
                        ss << "* "<<_inVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart1 << "MPI_Send(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_sourceVar<<",ATAG,MPI_COMM_WORLD);";
            } else {
                mpiVariantStructurePart1 << "MPI_Send(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<","<<_sourceVar<<",ATAG,MPI_COMM_WORLD);";
            }
        }
        mpiVariantStructurePart1 << "} else if(("<<conditionToWork<<"-"<<_followINVar<<")< "<<_partSizeVar<<" && ("<<conditionToWork<<"-"<<_followINVar<<")>0) {"
                << ""<<_partSizeVar<<" ="<<conditionToWork <<"-"<<_followINVar<<";"
                << "MPI_Send(&"<<_followINVar<<", 1, MPI_INT, "<<_sourceVar<<", ATAG, MPI_COMM_WORLD);"
                << "MPI_Send(&"<<_partSizeVar<<", 1, MPI_INT, "<<_sourceVar<<", ATAG, MPI_COMM_WORLD);";
        for(int i = 0; i<_inVars.size(); ++i){
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                varSent << std::string(_inVars[i].name)<<"["<<_followINVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_inVars[i].name);
                stringstream ss;
                for(int x = 0;x<_inVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _inVars[i].size[x];
                    else
                        ss << "* "<<_inVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart1 << "MPI_Send(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<","<<_sourceVar<<",ATAG,MPI_COMM_WORLD);";
            } else {
                mpiVariantStructurePart1 << "MPI_Send(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<","<<_sourceVar<<",ATAG,MPI_COMM_WORLD);";
            }
        }
        mpiVariantStructurePart1 << "}";
        mpiVariantStructurePart1 << "if(("<<_followINVar<<"+"<<_partSizeVar<<") > "<<conditionToWork<<") {"
                << "MPI_Send(&"<<_offsetVar<<", 1, MPI_INT, "<<_sourceVar<<", FTAG, MPI_COMM_WORLD);"
                << ""<<_killedVar<<"++;"
                << " }"
                << _followINVar<<"+="<<_partSizeVar<<";"
                << "if("<<_killedVar<<"=="<<_sizeVar<<"-1) {"
                << "break; }"
                <<"}";
    }
    mpiFixStructurePart1 <<mpiVariantStructurePart1;
    mpiFixStructurePart1 <<"}";
    //pragma2mpi.prepend(ASTmpiFixStructurePart1);
    AST_t ASTmpiFixStructurePart1 = mpiFixStructurePart1.parse_statement(function_body.get_ast(), function_body.get_scope_link());
    construct.get_ast().prepend(ASTmpiFixStructurePart1);
    constructASTS << construct.get_ast().prettyprint();
    Source mpiVariantStructurePart4, mpiVariantStructurePart5, mpiVariantStructurePart6;
    if(staticC!=0) {
        mpiVariantStructurePart4
                <<"if("<<_myidVar<<"!="<<_sizeVar<<"-1) {"
                << _partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1);";
        if(_inVars.size()!=0){
            mpiVariantStructurePart4 << ""<<_offsetVar<<" = "<<_partSizeVar<<" * ("<<_myidVar<<"-1);";
        }
        mpiVariantStructurePart4 <<" } else {"
                << _partSizeVar<<" = "<<maxS<<"/ ("<<_sizeVar<<"-1) + "<<maxS <<"%"<<"("<<_sizeVar<<"-1) ;";
        if(_inVars.size()!=0){
            mpiVariantStructurePart4 << ""<<_offsetVar<<" = " << maxS << "/ ("<<_sizeVar<<"-1) * ("<<_myidVar<<"-1);";
        }
        mpiVariantStructurePart4<< "}"
                << "while(1){";
        if(_inVars.size()==0){
            mpiVariantStructurePart4 << "MPI_Recv(&"<<_offsetVar<<", 1, MPI_INT,0,MPI_ANY_TAG,MPI_COMM_WORLD,&"<<_statVar<<");";
        }
        for(int i = 0; i<_inVars.size(); ++i){
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                varSent << std::string(_inVars[i].name)<<"["<<_offsetVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_inVars[i].name);
                stringstream ss;
                for(int x = 0;x<_inVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _inVars[i].size[x];
                    else
                        ss << "* "<<_inVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart4<<"MPI_Recv(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<", 0, MPI_ANY_TAG, MPI_COMM_WORLD,&"<<_statVar<<");";
            } else {
                mpiVariantStructurePart4<<"MPI_Recv(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<", 0, MPI_ANY_TAG, MPI_COMM_WORLD,&"<<_statVar<<");";
            }
        }
        for(int i = 0; i<_reducedVars.size(); ++i){
            string upperType = std::string(_reducedVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            mpiVariantStructurePart4 << "MPI_Recv(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<",MPI_ANY_SOURCE,MPI_ANY_TAG,MPI_COMM_WORLD,&"<<_statVar<<");";
        }
        // for(int i = 0; i<_reducedVars.size(); ++i){
        // string upperType = std::string(_reducedVars[i].type);
        // std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
        // mpiVariantStructurePart2<< "MPI_Send(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<", 0, 0, MPI_COMM_WORLD);";
        // }
    } else {
        mpiVariantStructurePart4<<"while(1){"
                "MPI_Recv(&"<<_offsetVar<<", 1, MPI_INT, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");";
        mpiVariantStructurePart6 << "MPI_Recv(&"<<_partSizeVar<<", 1, MPI_INT, 0, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");";
        for(int i = 0; i<_inVars.size(); ++i){
            string upperType = std::string(_inVars[i].type);
            std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
            stringstream varSent, size;
            if(iteratedVarCorrespondstoAnyVarIdx(initVar, _inVars[i].iterVar)) {
                varSent << std::string(_inVars[i].name)<<"["<<_offsetVar<<"]";
                size << _partSizeVar;
                for(int x=1; x<_inVars[i].size.size();++x) {
                    size<<" * " <<_inVars[i].size[x];
                }
            }
            else {
                varSent << std::string(_inVars[i].name);
                stringstream ss;
                for(int x = 0;x<_inVars[i].size.size();++x) {
                    if(x == 0)
                        ss << _inVars[i].size[x];
                    else
                        ss << "* "<<_inVars[i].size[x];
                }
                size << ss.str();
            }
            if(functionScope.get_symbol_from_name(_inVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
                mpiVariantStructurePart6<<"MPI_Recv(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<", 0, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");";
            } else {
                mpiVariantStructurePart6<<"MPI_Recv(&"<<_inVars[i].name<<", 1, MPI_"<<upperType<<", 0, MPI_ANY_TAG, MPI_COMM_WORLD, &"<<_statVar<<");";
            }
        }
        for(int i=0;i<_reducedVars.size();++i) {
            if(std::string(_reducedVars[i].operation).compare("+") == 0 || std::string(_reducedVars[i].operation).compare("-") == 0) {
                mpiVariantStructurePart6<<_reducedVars[i].name << " = "<< "0;";
            }else{
                mpiVariantStructurePart6<<_reducedVars[i].name << " = "<< "1;";
            }
        }
        // cout<<"V: "<<std::string(mpiVariantStructurePart6)<<endl;
        // cin.get();
        mpiVariantStructurePart2 << "MPI_Send(&"<<_offsetVar<<", 1, MPI_INT, 0, 0, MPI_COMM_WORLD);"
                "MPI_Send(&"<<_partSizeVar<<",1, MPI_INT, 0, 0, MPI_COMM_WORLD);";
    }
    mpiFixStructurePart2 << "if("<<_myidVar<<" !=0){ "
            <<mpiVariantStructurePart4
            <<"if("<<_statVar<<".MPI_TAG == ATAG) {"
            <<mpiVariantStructurePart6
            <<"for("<<initType<<" "<<initVar<<" = "<<_offsetVar<<"; "<<initVar<<"<"<<_offsetVar<<"+"<<_partSizeVar<<";++"<<initVar<<")"
            <<constructASTS<<mpiVariantStructurePart2;
    for(int i = 0; i<_ioVars.size(); ++i){
        string upperType = std::string(_ioVars[i].type);
        std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
        stringstream varSent, size;
        
        if(iteratedVarCorrespondstoAnyVarIdx(initVar, _ioVars[i].iterVar)) {
            varSent << std::string(_ioVars[i].name)<<"["<<_offsetVar<<"]";
            size << _partSizeVar;
            for(int x=1; x<_ioVars[i].size.size();++x) {
                size<<" * " <<_ioVars[i].size[x];
            }
        }
        else {
            varSent << std::string(_ioVars[i].name);
            stringstream ss;
            for(int x = 0;x<_ioVars[i].size.size();++x) {
                if(x == 0)
                    ss << _ioVars[i].size[x];
                else
                    ss << "* "<<_ioVars[i].size[x];
            }
            size << ss.str();
        }
        if(functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_array() || functionScope.get_symbol_from_name(_ioVars[i].name).get_type().is_pointer()) {
            mpiFixStructurePart2<<"MPI_Send(&"<<varSent.str()<<", "<<size.str()<<", MPI_"<<upperType<<", 0, 0, MPI_COMM_WORLD);";
        } else {
            mpiFixStructurePart2<<"MPI_Send(&"<<_ioVars[i].name<<", 1, MPI_"<<upperType<<", 0, 0, MPI_COMM_WORLD);";
        }
    }
    for(int i = 0; i<_reducedVars.size(); ++i){
        string upperType = std::string(_reducedVars[i].type);
        std::transform(upperType.begin(), upperType.end(),upperType.begin(), ::toupper);
        mpiFixStructurePart2<< "MPI_Send(&"<<_reducedVars[i].name<<", 1, MPI_"<<upperType<<", 0, 0, MPI_COMM_WORLD);";
        // constructASTS = modifyReductionOperation(_reducedVars[i], construct.get_ast(), construct);
    }
    mpiFixStructurePart2 <<"} else if("<<_statVar<<".MPI_TAG == FTAG) {";
    mpiFixStructurePart2<<mpiVariantStructurePart3<<"break;}"
            "} }";
    AST_t ASTmpiFixStructurePart2 = mpiFixStructurePart2.parse_statement(function_body.get_ast(), function_body.get_scope_link());
    construct.get_ast().replace_with(ASTmpiFixStructurePart2);
}
int TransPhase::isExistingVariable(string name, AST_t ast, ScopeLink sL) {
    ObjectList<Symbol> symbols;
    symbols = sL.get_scope(ast).get_all_symbols(false);
    for(int i = 0;i<symbols.size();++i){
        if(symbols[i].is_function()) {
            if(symbols[i].is_defined()) {
                FunctionDefinition fD(symbols[i].get_point_of_definition().get_enclosing_function_definition(),sL);
                // cout<<fD.get_function_body().prettyprint()<<endl;
                // cin.get();
                //                cout<<"Explore in function "<<symbols[i].get_name()<<endl;
                //                if(symbols[i].get_name().compare("main")==0) {
                //                    
                //                    cin.get();
                //                }
                //cin.get();
                if(isExistingVariable(name, fD.get_function_body().get_ast(), fD.get_scope_link()))
                    return 1;
            }
        } else {
            if(symbols[i].get_name().compare(name) == 0) {
                //                cout<<"finded existing symbol "<<name<<endl;
                //                cin.get();
                return 1;
            }
        }
    }
    
    return 0;
}
//*********************

EXPORT_PHASE(TransPhase);


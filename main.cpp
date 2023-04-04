#include <string>
#include <iostream>
#include <memory>
#include <algorithm>
#include <map>
#include <vector>
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "KaleidoscopeJIT.h"
using namespace llvm;
using namespace llvm::orc;
// using namespace std;
//  The lexer returns tokens [0-255] if it is an unknown character, otherwise one
//  of these for known things.
enum Token
{
    tok_eof = -1,

    // commands
    tok_def = -2,    // 关键字def
    tok_extern = -3, // 关键字extern

    // primary
    tok_identifier = -4, // 名字
    tok_number = -5,     // 数值
};

static std::string IdentifierStr; // Filled in if tok_identifier
static double NumVal;             // Filled in if tok_number

/// gettok - Return the next token from standard input.
static int gettok()
{
    static int LastChar = ' ';

    // Skip any whitespace.
    while (isspace(LastChar))
        LastChar = getchar();
    if (isalpha(LastChar))
    { // identifier: [a-zA-Z][a-zA-Z0-9]*
        IdentifierStr = LastChar;
        while (isalnum((LastChar = getchar())))
            IdentifierStr += LastChar;

        if (IdentifierStr == "def")
            return tok_def;
        if (IdentifierStr == "extern")
            return tok_extern;
        return tok_identifier;
    }
    if (isdigit(LastChar) || LastChar == '.')
    { // Number: [0-9.]+
        std::string NumStr;
        do
        {
            NumStr += LastChar;
            LastChar = getchar();
        } while (isdigit(LastChar) || LastChar == '.');

        NumVal = strtod(NumStr.c_str(), 0);
        return tok_number;
    }
    if (LastChar == '#')
    {
        // Comment until end of line.
        do
            LastChar = getchar();
        while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

        if (LastChar != EOF)
            return gettok();
    }
    // Check for end of file.  Don't eat the EOF.
    if (LastChar == EOF)
        return tok_eof;

    // Otherwise, just return the character as its ascii value.
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
}
/**
 * parser
 */
/// ExprAST - Base class for all expression nodes.
class ExprAST
{
public:
    virtual ~ExprAST() = default;
    virtual Value *codegen() = 0;
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST
{
    double Val;

public:
    NumberExprAST(double Val) : Val(Val) {}
    Value *codegen() override;
};

/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST
{
    std::string Name;

public:
    VariableExprAST(const std::string &Name) : Name(Name) {}
    Value *codegen() override;
};

/// BinaryExprAST,二元操作表达式- Expression class for a binary operator.
class BinaryExprAST : public ExprAST
{
    char Op;
    std::unique_ptr<ExprAST> LHS, RHS;

public:
    BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                  std::unique_ptr<ExprAST> RHS)
        : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
    Value *codegen() override;
};

/// CallExprAST 函数调用表达式- Expression class for function calls.
class CallExprAST : public ExprAST
{
    std::string Callee;
    std::vector<std::unique_ptr<ExprAST>> Args;

public:
    CallExprAST(const std::string &Callee,
                std::vector<std::unique_ptr<ExprAST>> Args)
        : Callee(Callee), Args(std::move(Args)) {}
    Value *codegen() override;
};

// 函数接口
/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST
{
    std::string Name;
    std::vector<std::string> Args;

public:
    PrototypeAST(const std::string &Name, std::vector<std::string> Args)
        : Name(Name), Args(std::move(Args)) {}

    const std::string &getName() const { return Name; }
    Function *codegen();
};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST
{
    std::unique_ptr<PrototypeAST> Proto;
    std::unique_ptr<ExprAST> Body;

public:
    FunctionAST(std::unique_ptr<PrototypeAST> Proto,
                std::unique_ptr<ExprAST> Body)
        : Proto(std::move(Proto)), Body(std::move(Body)) {}
    Function *codegen();
};

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok; //
static int getNextToken() { return CurTok = gettok(); }

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence()
{
    if (!isascii(CurTok))
        return -1;

    // Make sure it's a declared binop.
    int TokPrec = BinopPrecedence[CurTok];
    if (TokPrec <= 0)
        return -1;
    return TokPrec;
}

// error
std::unique_ptr<ExprAST> LogError(const char *Str)
{
    fprintf(stderr, "Error: %s\n", Str);
    return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str)
{
    LogError(Str);
    return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS);

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr()
{
    auto Result = std::make_unique<NumberExprAST>(NumVal);
    getNextToken(); // consume the number
    return std::move(Result);
}

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr()
{
    getNextToken(); // eat (.
    auto V = ParseExpression();
    if (!V)
        return nullptr;

    if (CurTok != ')')
        return LogError("expected ')'");
    getNextToken(); // eat ).
    return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr()
{
    std::string IdName = IdentifierStr;

    getNextToken(); // eat identifier.

    if (CurTok != '(') // Simple variable ref.
        return std::make_unique<VariableExprAST>(IdName);

    // Call.
    getNextToken(); // eat (
    std::vector<std::unique_ptr<ExprAST>> Args;
    if (CurTok != ')')
    {
        while (true)
        {
            if (auto Arg = ParseExpression())
                Args.push_back(std::move(Arg));
            else
                return nullptr;

            if (CurTok == ')')
                break;

            if (CurTok != ',')
                return LogError("Expected ')' or ',' in argument list");
            getNextToken();
        }
    }

    // Eat the ')'.
    getNextToken();

    return std::make_unique<CallExprAST>(IdName, std::move(Args));
}

// 我们将 NumberExpr、ParenExpr、IdentifierExpr
// 视为 PrimaryExpr, 封装 ParsePrimary 方便后续调用：
/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static std::unique_ptr<ExprAST> ParsePrimary()
{
    switch (CurTok)
    {
    default:
        return LogError("unknown token when expecting an expression");
    case tok_identifier:
        return ParseIdentifierExpr();
    case tok_number:
        return ParseNumberExpr();
    case '(':
        return ParseParenExpr();
    }
}

/// expression
///   ::= primary binoprhs
///
static std::unique_ptr<ExprAST> ParseExpression()
{
    auto LHS = ParsePrimary();
    if (!LHS)
        return nullptr;

    return ParseBinOpRHS(0, std::move(LHS));
}
// 把二元运算式分成a [+,b] [*,c]
/// binoprhs
///   ::= ('+' primary)*
//   lhs [binop primary] [binop primary] ...
// 如遇到优先级小于min_precedence的操作符，则停止
std::unique_ptr<ExprAST> ParseBinOpRHS(int min_precedence,
                                       std::unique_ptr<ExprAST> lhs)
{
    while (true)
    {
        int current_precedence = GetTokPrecedence();
        if (current_precedence < min_precedence)
        {
            // 如果当前token不是二元操作符，current_precedence为-1, 结束任务
            // 如果遇到优先级更低的操作符，也结束任务
            return lhs;
        }
        int binop = CurTok;
        getNextToken(); // eat binop
        auto rhs = ParsePrimary();
        // 现在我们有两种可能的解析方式
        //    * (lhs binop rhs) binop unparsed
        //    * lhs binop (rhs binop unparsed)
        int next_precedence = GetTokPrecedence();
        if (current_precedence < next_precedence)
        {
            // 将高于current_precedence的右边的操作符处理掉返回
            rhs = ParseBinOpRHS(current_precedence + 1, std::move(rhs));
        }
        lhs =
            std::make_unique<BinaryExprAST>(binop, std::move(lhs), std::move(rhs));
        // 继续循环
    }
}

/// prototype
///   ::= id '(' id* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype()
{
    if (CurTok != tok_identifier)
        return LogErrorP("Expected function name in prototype");

    std::string FnName = IdentifierStr;
    getNextToken();

    if (CurTok != '(')
        return LogErrorP("Expected '(' in prototype");

    // Read the list of argument names.
    std::vector<std::string> ArgNames;
    while (getNextToken() == tok_identifier)
        ArgNames.push_back(IdentifierStr);
    if (CurTok != ')')
        return LogErrorP("Expected ')' in prototype");

    // success.
    getNextToken(); // eat ')'.

    return std::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}
/// definition ::= 'def' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition()
{
    getNextToken(); // eat def.
    auto Proto = ParsePrototype();
    if (!Proto)
        return nullptr;

    if (auto E = ParseExpression())
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    return nullptr;
}
/// external ::= 'extern' prototype
static std::unique_ptr<PrototypeAST> ParseExtern()
{
    getNextToken(); // eat extern.
    return ParsePrototype();
}
/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseTopLevelExpr()
{
    if (auto E = ParseExpression())
    {
        // Make an anonymous proto.
        auto Proto = std::make_unique<PrototypeAST>("", std::vector<std::string>());
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<IRBuilder<>> Builder;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static ExitOnError ExitOnErr;

Function *getFunction(std::string Name)
{
    // First, see if the function has already been added to the current module.
    if (auto *F = TheModule->getFunction(Name))
        return F;

    // If not, check whether we can codegen the declaration from some existing
    // prototype.
    auto FI = FunctionProtos.find(Name);
    if (FI != FunctionProtos.end())
        return FI->second->codegen();

    // If no existing prototype exists, return null.
    return nullptr;
}

Value *LogErrorV(const char *Str)
{
    LogError(Str);
    return nullptr;
}

Value *NumberExprAST::codegen()
{
    return ConstantFP::get(*TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen()
{
    // Look this variable up in the function.
    Value *V = NamedValues[Name];
    if (!V)
        LogErrorV("Unknown variable name");
    return V;
}

Value *BinaryExprAST::codegen()
{
    Value *L = LHS->codegen();
    Value *R = RHS->codegen();
    if (!L || !R)
        return nullptr;

    switch (Op)
    {
    case '+':
        return Builder->CreateFAdd(L, R, "addtmp");
    case '-':
        return Builder->CreateFSub(L, R, "subtmp");
    case '*':
        return Builder->CreateFMul(L, R, "multmp");
    case '<':
        L = Builder->CreateFCmpULT(L, R, "cmptmp");
        // Convert bool 0/1 to double 0.0 or 1.0
        return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext),
                                     "booltmp");
    default:
        return LogErrorV("invalid binary operator");
    }
}
Value *CallExprAST::codegen()
{
    // Look up the name in the global module table.
    Function *CalleeF = getFunction(Callee);
    if (!CalleeF)
        return LogErrorV("Unknown function referenced");

    // If argument mismatch error.
    if (CalleeF->arg_size() != Args.size())
        return LogErrorV("Incorrect # arguments passed");

    std::vector<Value *> ArgsV;
    for (unsigned i = 0, e = Args.size(); i != e; ++i)
    {
        ArgsV.push_back(Args[i]->codegen());
        if (!ArgsV.back())
            return nullptr;
    }

    return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
}

Function *PrototypeAST::codegen()
{
    // Make the function type:  double(double,double) etc.
    std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
    FunctionType *FT =
        FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);

    Function *F =
        Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

    // Set names for all arguments.
    unsigned Idx = 0;
    for (auto &Arg : F->args())
        Arg.setName(Args[Idx++]);

    return F;
}

Function *FunctionAST::codegen()
{
    /*
    // First, check for an existing function from a previous 'extern' declaration.
    Function *TheFunction = TheModule->getFunction(Proto->getName());
*/

    // Transfer ownership of the prototype to the FunctionProtos map, but keep a
    // reference to it for use below.
    auto &P = *Proto;
    FunctionProtos[Proto->getName()] = std::move(Proto);
    Function *TheFunction = getFunction(P.getName());
    if (!TheFunction)
        TheFunction = Proto->codegen();

    if (!TheFunction)
        return nullptr;

    // Create a new basic block to start insertion into.
    BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);

    // Record the function arguments in the NamedValues map.
    NamedValues.clear();
    for (auto &Arg : TheFunction->args())
        NamedValues[std::string(Arg.getName())] = &Arg;

    if (Value *RetVal = Body->codegen())
    {
        // Finish off the function.
        Builder->CreateRet(RetVal);

        // Validate the generated code, checking for consistency.
        verifyFunction(*TheFunction);

        // Optimize the function.
        TheFPM->run(*TheFunction);
        return TheFunction;
    }

    // Error reading body, remove function.
    TheFunction->eraseFromParent();
    return nullptr;
}
//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//
static void InitializeModuleAndPassManager()
{
    // Open a new context and module.
    TheContext = std::make_unique<LLVMContext>();
    TheModule = std::make_unique<Module>("my cool jit", *TheContext);
    TheModule->setDataLayout(TheJIT->getDataLayout());

    // Create a new builder for the module.
    Builder = std::make_unique<IRBuilder<>>(*TheContext);

    // Create a new pass manager attached to it.
    TheFPM = std::make_unique<legacy::FunctionPassManager>(TheModule.get());

    // Do simple "peephole" optimizations and bit-twiddling optzns.
    TheFPM->add(createInstructionCombiningPass());
    // Reassociate expressions.
    TheFPM->add(createReassociatePass());
    // Eliminate Common SubExpressions.
    TheFPM->add(createGVNPass());
    // Simplify the control flow graph (deleting unreachable blocks, etc).
    TheFPM->add(createCFGSimplificationPass());

    TheFPM->doInitialization();
}
static void InitializeModule()
{
    // Open a new context and module.
    TheContext = std::make_unique<LLVMContext>();
    TheModule = std::make_unique<Module>("my cool jit", *TheContext);

    // Create a new builder for the module.
    Builder = std::make_unique<IRBuilder<>>(*TheContext);
}

static void HandleDefinition()
{
    if (auto FnAST = ParseDefinition())
    {
        if (auto *FnIR = FnAST->codegen())
        {
            fprintf(stderr, "Read function definition:");
            FnIR->print(errs());
            fprintf(stderr, "\n");
            ExitOnErr(TheJIT->addModule(ThreadSafeModule(std::move(TheModule), std::move(TheContext))));
            InitializeModuleAndPassManager(); // 为什么写这？
        }
    }
    else
    {
        // Skip token for error recovery.
        getNextToken();
    }
}

static void HandleExtern()
{
    if (auto ProtoAST = ParseExtern())
    {
        if (auto *FnIR = ProtoAST->codegen())
        {
            fprintf(stderr, "Read extern: ");
            FnIR->print(errs());
            fprintf(stderr, "\n");
            FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
        }
    }
    else
    {
        // Skip token for error recovery.
        getNextToken();
    }
}

static void HandleTopLevelExpression()
{
    // Evaluate a top-level expression into an anonymous function.
    if (auto FnAST = ParseTopLevelExpr())
    {
        if (FnAST->codegen())
        {
            // Create a ResourceTracker to track JIT'd memory allocated to our
            // anonymous expression -- that way we can free it after executing.
            auto RT = TheJIT->getMainJITDylib().createResourceTracker();

            auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
            ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
            InitializeModuleAndPassManager();

            // Search the JIT for the __anon_expr symbol.
            auto ExprSymbol = ExitOnErr(TheJIT->lookup("__anon_expr"));

            // Get the symbol's address and cast it to the right type (takes no
            // arguments, returns a double) so we can call it as a native function.
            double (*FP)() = (double (*)())(intptr_t)ExprSymbol.getAddress();
            fprintf(stderr, "Evaluated to %f\n", FP());

            // Delete the anonymous expression module from the JIT.
            ExitOnErr(RT->remove());
        }
    }
    else
    {
        // Skip token for error recovery.
        getNextToken();
    }
}
/// top ::= definition | external | expression | ';'
static void MainLoop()
{
    while (true)
    {
        fprintf(stderr, "ready> ");
        switch (CurTok)
        {
        case tok_eof:
            return;
        case ';': // ignore top-level semicolons.
            getNextToken();
            break;
        case tok_def:
            HandleDefinition();
            break;
        case tok_extern:
            HandleExtern();
            break;
        default:
            HandleTopLevelExpression();
            break;
        }
    }
}

//===----------------------------------------------------------------------===//
// "Library" functions that can be "extern'd" from user code.
//===----------------------------------------------------------------------===//

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double X)
{
    fputc((char)X, stderr);
    return 0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
extern "C" DLLEXPORT double printd(double X)
{
    fprintf(stderr, "%f\n", X);
    return 0;
}
// clang++ -g -O3 main.cpp `llvm-config --cxxflags`
// clang++ -g -O3 main.cpp `llvm-config --cxxflags --ldflags --system-libs --libs core` -o main
/*
clang++ -g main.cpp `llvm-config --cxxflags --ldflags --system-libs --libs core orcjit native -rdynamic` -O3 -o main
*/
int main()
{
    //获取目标机器的信息
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    // Install standard binary operators.
    // 1 is lowest precedence.
    BinopPrecedence['<'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40; // highest.

    // Prime the first token.
    fprintf(stderr, "ready> ");
    getNextToken();
    // Make the module, which holds all the code.
    // InitializeModule();
    //定义JIT
    TheJIT = ExitOnErr(KaleidoscopeJIT::Create());
    // 加上优化
    InitializeModuleAndPassManager();

    // Run the main "interpreter loop" now.
    MainLoop();

    return 0;

    /**
     test lexer
    */
    // while (true)
    // {
    //     int tok = gettok();
    //     std::cout << "The token :" << tok << std::endl;
    // }
}
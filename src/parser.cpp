/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 *
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    // Check if the first element is a symbol
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // Not a symbol, so this is a function application
        Expr rator = stxs[0]->parse(env);
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(rator, parameters));
    }

    string op = id->s;

    // Check if it's a variable in the environment (for closures)
    if (find(op, env).get() != nullptr) {
        Expr rator = stxs[0]->parse(env);
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(rator, parameters));
    }

    // Check if it's a primitive
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }

        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1]));
            } else {
                return Expr(new PlusVar(parameters));
            }
        } else if (op_type == E_MINUS) {
            if (parameters.size() == 2) {
                return Expr(new Minus(parameters[0], parameters[1]));
            } else {
                return Expr(new MinusVar(parameters));
            }
        } else if (op_type == E_MUL) {
            if (parameters.size() == 2) {
                return Expr(new Mult(parameters[0], parameters[1]));
            } else {
                return Expr(new MultVar(parameters));
            }
        } else if (op_type == E_DIV) {
            if (parameters.size() == 2) {
                return Expr(new Div(parameters[0], parameters[1]));
            } else {
                return Expr(new DivVar(parameters));
            }
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_EXPT) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for expt");
            }
            return Expr(new Expt(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) {
                return Expr(new Less(parameters[0], parameters[1]));
            } else {
                return Expr(new LessVar(parameters));
            }
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                return Expr(new LessEqVar(parameters));
            }
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                return Expr(new EqualVar(parameters));
            }
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterEqVar(parameters));
            }
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterVar(parameters));
            }
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for cons");
            }
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for car");
            }
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for cdr");
            }
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for not");
            }
            return Expr(new Not(parameters[0]));
        } else if (op_type == E_EQQ) {
            if (parameters.size() == 2) {
                return Expr(new IsEq(parameters[0], parameters[1]));
            } else {
                return Expr(new EqualVar(parameters));
            }
        } else if (op_type == E_BOOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for boolean?");
            }
            return Expr(new IsBoolean(parameters[0]));
        } else if (op_type == E_INTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for number?");
            }
            return Expr(new IsFixnum(parameters[0]));
        } else if (op_type == E_NULLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for null?");
            }
            return Expr(new IsNull(parameters[0]));
        } else if (op_type == E_PAIRQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for pair?");
            }
            return Expr(new IsPair(parameters[0]));
        } else if (op_type == E_PROCQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for procedure?");
            }
            return Expr(new IsProcedure(parameters[0]));
        } else if (op_type == E_SYMBOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for symbol?");
            }
            return Expr(new IsSymbol(parameters[0]));
        } else if (op_type == E_LISTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for list?");
            }
            return Expr(new IsList(parameters[0]));
        } else if (op_type == E_STRINGQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for string?");
            }
            return Expr(new IsString(parameters[0]));
        } else if (op_type == E_SETCAR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-car!");
            }
            return Expr(new SetCar(parameters[0], parameters[1]));
        } else if (op_type == E_SETCDR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-cdr!");
            }
            return Expr(new SetCdr(parameters[0], parameters[1]));
        } else if (op_type == E_DISPLAY) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for display");
            }
            return Expr(new Display(parameters[0]));
        } else if (op_type == E_VOID) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for void");
            }
            return Expr(new MakeVoid());
        } else if (op_type == E_EXIT) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for exit");
            }
            return Expr(new Exit());
        } else {
            throw RuntimeError("Unknown primitive: " + op);
        }
    }

    // Check if it's a reserved word
    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
            case E_QUOTE: {
                if (stxs.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for quote");
                }
                return Expr(new Quote(stxs[1]));
            }
            case E_BEGIN: {
                vector<Expr> exprs;
                for (size_t i = 1; i < stxs.size(); i++) {
                    exprs.push_back(stxs[i]->parse(env));
                }
                return Expr(new Begin(exprs));
            }
            case E_IF: {
                if (stxs.size() != 4) {
                    throw RuntimeError("Wrong number of arguments for if");
                }
                return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
            }
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List *clause_list = dynamic_cast<List*>(stxs[i].get());
                    if (!clause_list) {
                        throw RuntimeError("Invalid cond clause");
                    }
                    vector<Expr> clause;
                    for (size_t j = 0; j < clause_list->stxs.size(); j++) {
                        clause.push_back(clause_list->stxs[j]->parse(env));
                    }
                    clauses.push_back(clause);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for lambda");
                }

                // Parse parameters
                vector<string> params;
                List *param_list = dynamic_cast<List*>(stxs[1].get());
                if (!param_list) {
                    throw RuntimeError("Lambda parameters must be a list");
                }
                for (size_t i = 0; i < param_list->stxs.size(); i++) {
                    SymbolSyntax *param_sym = dynamic_cast<SymbolSyntax*>(param_list->stxs[i].get());
                    if (!param_sym) {
                        throw RuntimeError("Lambda parameter must be a symbol");
                    }
                    params.push_back(param_sym->s);
                }

                // Parse body (multiple expressions)
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(env));
                }

                if (body_exprs.size() == 1) {
                    return Expr(new Lambda(params, body_exprs[0]));
                } else {
                    return Expr(new Lambda(params, Expr(new Begin(body_exprs))));
                }
            }
            case E_DEFINE: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for define");
                }

                // Check if it's a function definition shorthand
                List *func_def = dynamic_cast<List*>(stxs[1].get());
                if (func_def) {
                    // (define (func-name params...) body...)
                    if (func_def->stxs.empty()) {
                        throw RuntimeError("Empty function definition");
                    }

                    SymbolSyntax *func_name = dynamic_cast<SymbolSyntax*>(func_def->stxs[0].get());
                    if (!func_name) {
                        throw RuntimeError("Function name must be a symbol");
                    }

                    vector<string> params;
                    for (size_t i = 1; i < func_def->stxs.size(); i++) {
                        SymbolSyntax *param_sym = dynamic_cast<SymbolSyntax*>(func_def->stxs[i].get());
                        if (!param_sym) {
                            throw RuntimeError("Function parameter must be a symbol");
                        }
                        params.push_back(param_sym->s);
                    }

                    // Parse body (multiple expressions)
                    vector<Expr> body_exprs;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        body_exprs.push_back(stxs[i]->parse(env));
                    }

                    if (body_exprs.size() == 1) {
                        return Expr(new Define(func_name->s, Expr(new Lambda(params, body_exprs[0]))));
                    } else {
                        return Expr(new Define(func_name->s, Expr(new Lambda(params, Expr(new Begin(body_exprs))))));
                    }
                } else {
                    // (define var value)
                    SymbolSyntax *var_name = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (!var_name) {
                        throw RuntimeError("Define variable name must be a symbol");
                    }

                    // Parse body (multiple expressions)
                    vector<Expr> body_exprs;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        body_exprs.push_back(stxs[i]->parse(env));
                    }

                    if (body_exprs.size() == 1) {
                        return Expr(new Define(var_name->s, body_exprs[0]));
                    } else {
                        return Expr(new Define(var_name->s, Expr(new Begin(body_exprs))));
                    }
                }
            }
            case E_LET: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for let");
                }

                // Parse bindings
                List *bindings = dynamic_cast<List*>(stxs[1].get());
                if (!bindings) {
                    throw RuntimeError("Let bindings must be a list");
                }

                vector<pair<string, Expr>> bind;
                for (size_t i = 0; i < bindings->stxs.size(); i++) {
                    List *binding = dynamic_cast<List*>(bindings->stxs[i].get());
                    if (!binding || binding->stxs.size() != 2) {
                        throw RuntimeError("Invalid let binding");
                    }

                    SymbolSyntax *var_name = dynamic_cast<SymbolSyntax*>(binding->stxs[0].get());
                    if (!var_name) {
                        throw RuntimeError("Let binding variable must be a symbol");
                    }

                    bind.push_back(mp(var_name->s, binding->stxs[1]->parse(env)));
                }

                // Parse body (multiple expressions)
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(env));
                }

                if (body_exprs.size() == 1) {
                    return Expr(new Let(bind, body_exprs[0]));
                } else {
                    return Expr(new Let(bind, Expr(new Begin(body_exprs))));
                }
            }
            case E_LETREC: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for letrec");
                }

                // Parse bindings
                List *bindings = dynamic_cast<List*>(stxs[1].get());
                if (!bindings) {
                    throw RuntimeError("Letrec bindings must be a list");
                }

                vector<pair<string, Expr>> bind;
                for (size_t i = 0; i < bindings->stxs.size(); i++) {
                    List *binding = dynamic_cast<List*>(bindings->stxs[i].get());
                    if (!binding || binding->stxs.size() != 2) {
                        throw RuntimeError("Invalid letrec binding");
                    }

                    SymbolSyntax *var_name = dynamic_cast<SymbolSyntax*>(binding->stxs[0].get());
                    if (!var_name) {
                        throw RuntimeError("Letrec binding variable must be a symbol");
                    }

                    bind.push_back(mp(var_name->s, binding->stxs[1]->parse(env)));
                }

                // Parse body (multiple expressions)
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(env));
                }

                if (body_exprs.size() == 1) {
                    return Expr(new Letrec(bind, body_exprs[0]));
                } else {
                    return Expr(new Letrec(bind, Expr(new Begin(body_exprs))));
                }
            }
            case E_SET: {
                if (stxs.size() != 3) {
                    throw RuntimeError("Wrong number of arguments for set!");
                }

                SymbolSyntax *var_name = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!var_name) {
                    throw RuntimeError("Set! variable name must be a symbol");
                }

                return Expr(new Set(var_name->s, stxs[2]->parse(env)));
            }
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    // Default: use Apply to be an expression (for higher-order functions)
    Expr rator = stxs[0]->parse(env);
    vector<Expr> parameters;
    for (size_t i = 1; i < stxs.size(); i++) {
        parameters.push_back(stxs[i]->parse(env));
    }
    return Expr(new Apply(rator, parameters));
}

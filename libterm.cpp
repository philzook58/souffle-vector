#include <cstdint>
#include "souffle/SouffleFunctor.h"
#include <cassert>
#include <vector>
#include <algorithm>
#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

#define APP 0
#define BVAR 1
#define LAM 2
#define NUM 3
#define SYM 4
#define VAR 5
#define ZFVAR 6

#define NTAGS 6

#define NIL 0

/*
Options:
2. use variant? use shared_ptr ref counted terms
3. use union. Need manual memory mangament / custom deconstrucotrs? Arena?
4. use classes and visitor pattern also shared_ptr
5. bite the bullet, add a constructor for nameless manipulation. It's not so bad.
*/

/*
struct app_node
{
    std::shared_ptr<term> f;
    std::shared_ptr<term> x;
};*/

/*
terms are going to be stored in a vector `recexpr`.
They exists very ephemerally during beta normalization.
*/

struct term;

using recexpr = std::vector<term>;

union uterm
{
    recexpr::size_type body;                               // Lam
    std::pair<recexpr::size_type, recexpr::size_type> app; // App
    souffle::RamDomain ramdom;                             // Everything else.
};

struct term
{
    souffle::RamDomain tag;
    uterm data;
};

// Helpers to make recexpr objects.
recexpr::size_type mk_bvar(recexpr &expr, souffle::RamDomain i)
{
    term t = {BVAR, 0};
    t.data.ramdom = i;
    expr.push_back(t);
    return expr.size() - 1;
}

recexpr::size_type mk_fvar(recexpr &expr, souffle::RamDomain i)
{
    term t = {ZFVAR, 0};
    t.data.ramdom = i;
    expr.push_back(t);
    return expr.size() - 1;
}

recexpr::size_type mk_lam(recexpr &expr, recexpr::size_type i)
{
    term t = {LAM, 0};
    t.data.body = i;
    expr.push_back(t);
    return expr.size() - 1;
}

recexpr::size_type mk_app(recexpr &expr, recexpr::size_type f, recexpr::size_type x)
{
    term t = {APP, 0};
    t.data.app = std::make_pair(f, x);
    expr.push_back(t);
    return expr.size() - 1;
}

// Helpers to make souffle ADTs
inline souffle::RamDomain mk_app(souffle::RecordTable *recordTable, souffle::RamDomain f, souffle::RamDomain x)
{
    souffle::RamDomain myTuple1[2] = {f, x};
    const souffle::RamDomain f_x0 = recordTable->pack(myTuple1, 2);
    souffle::RamDomain myTuple2[2] = {APP, f_x0};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_lam(souffle::RecordTable *recordTable, souffle::RamDomain b)
{
    souffle::RamDomain myTuple2[2] = {LAM, b};
    return recordTable->pack(myTuple2, 2);
}
inline souffle::RamDomain mk_bvar(souffle::RecordTable *recordTable, souffle::RamDomain i)
{
    souffle::RamDomain myTuple2[2] = {BVAR, i};
    return recordTable->pack(myTuple2, 2);
}


// Could do better recording of already seen stuff in Map. More memoization? Isn't clear the search is worth the effort.
recexpr::size_type from_souffle(souffle::RecordTable *recordTable, souffle::RamDomain t, recexpr &expr)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(t, 2);
    souffle::RamDomain tag = myTuple0[0];
    term myterm = {tag, 0};
    // myterm.tag = tag;
    switch (tag)
    {
    case APP:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        myterm.data.app.first = from_souffle(recordTable, f_x[0], expr);
        myterm.data.app.second = from_souffle(recordTable, f_x[1], expr);
        break;
    }
    case LAM:
    {
        myterm.data.body = from_souffle(recordTable, myTuple0[1], expr);
        break;
    }
    case BVAR:
    case NUM:
    case SYM:
    case VAR:
    {
        myterm.data.ramdom = myTuple0[1];
        break;
    }
    default:
        assert(false && "Missed Case in from_souffle");
    }
    expr.push_back(myterm); // maybe we could use emplace_back?
    return expr.size() - 1;
}

souffle::RamDomain to_souffle(souffle::RecordTable *recordTable, const recexpr &expr, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case LAM:
    {
        return mk_lam(recordTable, to_souffle(recordTable, expr, t.data.body));
    }
    case APP:
    {
        recexpr::size_type f = to_souffle(recordTable, expr, t.data.app.first);
        recexpr::size_type x = to_souffle(recordTable, expr, t.data.app.second);
        return mk_app(recordTable, f, x);
    }
    case NUM:
    case SYM:
    case VAR:
    case BVAR:
    {
        const souffle::RamDomain myTuple[2] = {t.tag, t.data.ramdom};
        return recordTable->pack(myTuple, 2);
    }
    default:
        assert(false && "Missing case in varopen");
    }
}

/*

Varopen takes a level and an expression id and replaces bvar(level) with that expression id. 
This is performing substitution basically.
Traversing a lambda binder increases the level

let rec varopen k e (t : ln) =
  match t with
  | FVar _ -> t
  | FVarI _ -> t
  | BVar i -> if Int.(i = k) then e else t
  | App (f, y) -> App (varopen k e f, varopen k e y)
  | Lam body -> Lam { scope = varopen (k + 1) e body.scope }

let instantiate (e : ln) (t : scope) : ln = varopen 0 e t.scope
*/

recexpr::size_type varopen(recexpr &expr, souffle::RamDomain level, recexpr::size_type e, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case BVAR:
    {
        if (t.data.ramdom == level)
        {
            return e;
        }
        else
        {
            return i;
        }
    }
    case LAM:
    {
        return mk_lam(expr, varopen(expr, level + 1, e, t.data.body));
    }
    case APP:
    {
        recexpr::size_type f = varopen(expr, level, e, t.data.app.first);
        recexpr::size_type x = varopen(expr, level, e, t.data.app.second);
        return mk_app(expr, f, x);
    }
    case NUM:
    case SYM:
    case VAR:
    case ZFVAR:
        return i;
    default:
        assert(false && "Missing case in varopen");
    }
}

/*
pretty_term
norm1
norm2
norm3

parse_term
a shadow tree with more annotations?
Go for full marking in the datatype?
pretty_termset

Boxed results [res1 , res2]. This is possible.
Two terms from separate relations with free vars. Hmm. The free vars can't clash from seperate relations.

-01 -g

*/

/*
varclose takes a free variable identifier and replaces it with bvar(level).
Traversing a lambda binder increases the level

let rec varclose k x (t : ln) : ln =
  match t with
  | FVar x' -> if String.(x = x') then BVar k else t
  | FVarI _ -> t
  | BVar _ -> t
  | App (f, y) -> App (varclose k x f, varclose k x y)
  | Lam body -> Lam { scope = varclose (k + 1) x body.scope }

let abstract (x : string) (t : ln) : scope = { scope = varclose 0 x t }
*/

recexpr::size_type varclose(recexpr &expr, souffle::RamDomain level, souffle::RamDomain fv, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case ZFVAR:
    {
        if (t.data.ramdom == fv)
        {
            return mk_bvar(expr, level);
        }
        else
        {
            return i;
        }
    }
    case LAM:
    {
        return mk_lam(expr, varclose(expr, level + 1, fv, t.data.body));
    }
    case APP:
    {
        recexpr::size_type f = varclose(expr, level, fv, t.data.app.first);
        recexpr::size_type x = varclose(expr, level, fv, t.data.app.second);
        return mk_app(expr, f, x);
    }
    case NUM:
    case SYM:
    case VAR:
    case BVAR:
        return i;
    default:
        assert(false && "Missing case in varclose");
    }
}


/*
beta_norm traverses and looks for shapes app(f,x). It normalizes f and x, if f is of the shape lam(b) then it performs
substitution [x/bvar(0)] b via varopen.
Whenever you go into a lambda, you need to replace that bvar(0) with a fresh variable. This is smart because substitution
messes with de bruijn indices.

let rec norm (t : ln) : ln =
  match t with
  | Lam t' ->
      let v = fresh () in
      let t'' = instantiate (FVarI v) t' in
      Lam (abstract' v (norm t''))
  | App (t, u) -> (
      let t' = norm t in
      let u' = norm u in
      match t' with Lam t'' -> norm (instantiate u' t'') | _ -> App (t', u'))
  | _ -> t
*/

recexpr::size_type beta_norm(recexpr &expr, souffle::RamDomain &fresh, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case LAM:
    {
        souffle::RamDomain curfresh = fresh;
        recexpr::size_type b = varopen(expr, 0, mk_fvar(expr, curfresh), t.data.body);
        fresh++;
        return mk_lam(expr, varclose(expr, 0, curfresh, beta_norm(expr, fresh, b)));
    }
    case APP:
    {
        recexpr::size_type f = beta_norm(expr, fresh, t.data.app.first);
        recexpr::size_type x = beta_norm(expr, fresh, t.data.app.second);
        if (expr[f].tag == LAM)
        {
            recexpr::size_type fx = varopen(expr, 0, x, expr[f].data.body);
            return beta_norm(expr, fresh, fx);
        }
        else
        {
            return mk_app(expr, f, x);
        }
    }
    case NUM:
    case SYM:
    case VAR:
    case BVAR:
    case ZFVAR:
        return i;
    default:
        assert(false && "Missing case in beta_norm");
    }
}

// Examples of functor usage:
// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{

    souffle::RamDomain beta_norm(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg)
    {
        recexpr expr;
        recexpr::size_type t = from_souffle(recordTable, arg, expr);
        souffle::RamDomain fresh = 0;
        recexpr::size_type t1 = beta_norm(expr, fresh, t);
        return to_souffle(recordTable, expr, t1);
    }

    souffle::RamDomain count_var(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        if (arg == 0)
        {
            return 0;
        }
        else
        {
            const souffle::RamDomain *myTuple0 = recordTable->unpack(arg, 2);
            souffle::RamDomain tag = myTuple0[0];
            assert(tag <= NTAGS && "Unexpected Tag in count_var");
            if (tag == VAR)
            {
                return 1;
            }
            else if (tag == APP)
            {
                const souffle::RamDomain *fargs = recordTable->unpack(myTuple0[1], 2);
                // Could do something smarter than recursion here.
                return count_var(symbolTable, recordTable, fargs[0]) + count_var(symbolTable, recordTable, fargs[1]);
            }
            else
            {
                return 0;
            }
        }
    }

    // Returns nil if failure to reabstract
    // Check for that on souffle side.
    // beta_zero?

    // The args are speicifed by the site at which the pattern occurs.
    souffle::RamDomain reabstract(
        souffle::RecordTable *recordTable,
        souffle::RamDomain term,
        int level,
        const std::vector<souffle::RamDomain> &args)
    {
        assert(recordTable && "NULL record table");
        assert(term != 0 && "reabstract of nil");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(term, 2);
        souffle::RamDomain tag = myTuple0[0];
        assert(tag <= 3 && "Unexpected Tag in count_var");
        switch (tag)
        {
        case APP:
        {
            const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
            const souffle::RamDomain f = reabstract(recordTable, f_x[0], level, args);
            // TODO early fail
            if (f == NIL)
            {
                return NIL;
            }
            const souffle::RamDomain x = reabstract(recordTable, f_x[1], level, args);
            if (x == NIL)
            {
                return NIL;
            }
            return mk_app(recordTable, f, x);
        }
        case BVAR: // reabstract var in in known
        {
            souffle::RamDomain i = myTuple0[1];
            if (i < level)
            {
                return term;
            }
            auto varind = std::find(args.begin(), args.end(), i - level); // search for bvar minus the extra lambdas we've traversed
            if (varind != args.end())                                     // Found bvar
            {
                return mk_bvar(recordTable, level + static_cast<souffle::RamDomain>(varind - args.begin()));
            }
            else
            {
                // std::cout << "did not find bvar" << i << level << i - level;
                //  Maybe I should just throw an exception to be caught. Eh.
                return NIL;
            }
        }
        case LAM:
        {
            // shift args? No. Reabstract is written in terms of the original position.
            // raise current level.
            const souffle::RamDomain b = reabstract(recordTable, myTuple0[1], level + 1, args);
            if (b == NIL)
            {
                return NIL;
            }
            return mk_lam(recordTable, b);
        }
        case NUM:
        case SYM:
        case VAR:
            return term;
        default:
            assert(false && "Missed Case in reabstract");
        }
    }

    souffle::RamDomain reabstract1(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable,
        souffle::RamDomain term,
        souffle::RamDomain x0)
    {
        std::vector<souffle::RamDomain> args{x0};
        souffle::RamDomain res = reabstract(recordTable, term, 0, args);
        if (res != NIL)
        {
            return mk_lam(recordTable, res);
        }
        else
        {
            return NIL;
        }
    }

    souffle::RamDomain reabstract2(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable,
        souffle::RamDomain term,
        souffle::RamDomain x0, souffle::RamDomain x1)
    {
        std::vector<souffle::RamDomain> args{x0, x1};
        souffle::RamDomain res = reabstract(recordTable, term, 0, args);
        if (res != NIL)
        {
            return mk_lam(recordTable, mk_lam(recordTable, res));
        }
        else
        {
            return NIL;
        }
    }
}
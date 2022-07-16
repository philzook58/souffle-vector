#include <cstdint>
#include "souffle/SouffleFunctor.h"
#include <cassert>
#include <vector>
#include <algorithm>
#include <unordered_map>
#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

/*
.type term =
| Bind {b : scope} // 0
| BVar {n : db_index} // 1
| FVar {n : freevar} // 2
| Num {n : number} // 3
| Sym {s : symbol} // 4
| T2 {f : term, x : term} // 5
*/

#define BIND 1
#define BVAR 0
#define FVAR 2
#define NUM 3
#define SYM 4
#define T2 5

#define NTAGS 5

#define NIL 0

// Helpers to make souffle ADTs
inline souffle::RamDomain mk_t2(souffle::RecordTable *recordTable, souffle::RamDomain f, souffle::RamDomain x)
{
    souffle::RamDomain myTuple1[2] = {f, x};
    const souffle::RamDomain f_x0 = recordTable->pack(myTuple1, 2);
    souffle::RamDomain myTuple2[2] = {T2, f_x0};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_bind(souffle::RecordTable *recordTable, souffle::RamDomain b)
{
    souffle::RamDomain myTuple2[2] = {BIND, b};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_bvar(souffle::RecordTable *recordTable, souffle::RamDomain i)
{
    souffle::RamDomain myTuple2[2] = {BVAR, i};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_fvar(souffle::RecordTable *recordTable, souffle::RamDomain i)
{
    souffle::RamDomain myTuple2[2] = {FVAR, i};
    return recordTable->pack(myTuple2, 2);
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

souffle::RamDomain varopen(souffle::RecordTable *recordTable, souffle::RamDomain level, souffle::RamDomain e, souffle::RamDomain i)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(i, 2);
    souffle::RamDomain tag = myTuple0[0];
    switch (tag)
    {
    case T2:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        const souffle::RamDomain f = varopen(recordTable, level, e, f_x[0]);
        const souffle::RamDomain x = varopen(recordTable, level, e, f_x[1]);
        return mk_t2(recordTable, f, x);
    }
    case BVAR:
    {
        if (myTuple0[1] == level)
        {
            return e;
        }
        else
        {
            return i;
        }
    }
    case BIND:
    {
        // could short circuit repacking here.
        return mk_bind(recordTable, varopen(recordTable, level + 1, e, myTuple0[1]));
    }
    case NUM:
    case SYM:
    case FVAR:
        return i;
    default:
        assert(false && "Missing case in varopen");
    }
}

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

souffle::RamDomain varclose(souffle::RecordTable *recordTable, souffle::RamDomain level, souffle::RamDomain fv, souffle::RamDomain i)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(i, 2);
    souffle::RamDomain tag = myTuple0[0];
    switch (tag)
    {
    case FVAR:
    {
        if (myTuple0[1] == fv)
        {
            return mk_bvar(recordTable, level);
        }
        else
        {
            return i;
        }
    }
    case BIND:
    {
        return mk_bind(recordTable, varclose(recordTable, level + 1, fv, myTuple0[1]));
    }
    case T2:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        souffle::RamDomain f = varclose(recordTable, level, fv, f_x[0]);
        souffle::RamDomain x = varclose(recordTable, level, fv, f_x[1]);
        return mk_t2(recordTable, f, x);
    }
    case NUM:
    case SYM:
    case BVAR:
        return i;
    default:
        assert(false && "Missing case in varclose");
    }
}

souffle::RamDomain norm_help(souffle::RecordTable *recordTable, std::unordered_map<souffle::RamDomain, souffle::RamDomain> &freemap, souffle::RamDomain t)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(t, 2);
    souffle::RamDomain tag = myTuple0[0];
    switch (tag)
    {
    case FVAR:
    {

        auto elem = freemap.find(myTuple0[1]);
        if (elem != freemap.end()) // if already seen freevar
        {
            return elem->second;
        }
        else
        {
            souffle::RamDomain nfvar = freemap.size();
            souffle::RamDomain fvar = mk_fvar(recordTable, nfvar);
            freemap[myTuple0[1]] = fvar;
            return fvar;
        }
    }
    case BIND:
    {
        return mk_bind(recordTable, norm_help(recordTable, freemap, myTuple0[1]));
    }
    case T2:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        souffle::RamDomain f = norm_help(recordTable, freemap, f_x[0]);
        souffle::RamDomain x = norm_help(recordTable, freemap, f_x[1]);
        return mk_t2(recordTable, f, x);
    }
    case NUM:
    case SYM:
    case BVAR:
        return t;
    default:
        assert(false && "Missing case in varclose");
    }
}

// Examples of functor usage:
// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{

    souffle::RamDomain norm(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain term)
    {
        std::unordered_map<souffle::RamDomain, souffle::RamDomain> freemap;
        return norm_help(recordTable, freemap, term);
    }

    souffle::RamDomain abstract(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain fv, souffle::RamDomain term)
    {
        assert(recordTable && "NULL record table");
        return varclose(recordTable, 0, fv, term);
    }

    souffle::RamDomain instantiate(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain e, souffle::RamDomain term)
    {
        assert(recordTable && "NULL record table");
        return varopen(recordTable, 0, e, term);
    }

    souffle::RamDomain max_var(souffle::RecordTable *recordTable, souffle::RamDomain i)
    {
        const souffle::RamDomain *myTuple0 = recordTable->unpack(i, 2);
        souffle::RamDomain tag = myTuple0[0];
        switch (tag)
        {
        case FVAR:
        {
            return myTuple0[1];
        }
        case BIND:
        {
            return max_var(recordTable, myTuple0[1]);
        }
        case T2:
        {
            const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
            souffle::RamDomain f = max_var(recordTable, f_x[0]);
            souffle::RamDomain x = max_var(recordTable, f_x[1]);
            return std::max(f, x);
        }
        case NUM:
        case SYM:
        case BVAR:
            return -100000;
        default:
            assert(false && "Missing case in max_var");
        }
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

norm1(){

}

norm3(){

}


subst(t,  i){

}
subst is like var close, except we're not rebinding to lambda, so we're not turning fvar into bvar, just a whole new
closed term.



norm2(t1,t2){
    beta_norm(t1);
    beta_norm(t2);
    var_seen()
    to_souffle( , 0, ); // we're traversing the term anyway. We might as well label freevars while we're at it.

}


foo(t), bar(t2). The free vars should actually not be related at all.

disjoint_vars(t1,t2){
    max_var(t1)
}
shift_fvars(t2, n){

}
Ok this is definable at souffle level.

But what about contexts?
The number of something in the set depends on the var lavelling but if we choose a traversal order to canonize var labelling
It's chcken and egg.
That's why seperate uf is good idea.
We could normalize according to this method in C++ and then build ordinary term system?
But then we need to sort terms without their' souffle hash cons id


We can
1. abandon set-like character. Require explicit contraction and stuff
2.
3. revert to th version wehre context can only refer to vars in head and linear vars.
    I mean, this might get us pretty darn far.


Context Lists?







*/
# souffle-vector




## Thoughts

Maybe I should just number the free vars
There is something very weird about traversing the terms to normalize, but then also traversing to numberify

No Lam. Just Bind. No App, just n-arity symbols.

.type scope = [t : term]
.type term = Bind {s : scope} | FVar {n : unsigned} | Sym | Num

Lambda has nothing to do with it. Beta_0 matching isn't beta at all.

Bound and free variables are the concepts.

A tighter term type. Steal some bits. This is a little silly.


#define ISNUM(x) ((x % 2) = 0)
#define ISSYM(x) ((x % 4) = 1)
#define ISBOX()  (() = )

#define NUM(x) (x bshl 1)
#define SYM(x) (as(x,number) bshl 1 + 1)
#define RECORD(x) (as(x,number) bshl 1 + 1)

#define UNSYM(n)  as(n-1 bshr 1, symbol)



.type scope <: number

Bind {s : scope}

abstract(freevar, s:term):term
instan(s:scope, e : term):term

fresh = $FVar(-1)

normalize fre variables
normterm <: term
freenorm(term):normterm



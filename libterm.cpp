#include <cstdint>
#include "souffle/SouffleFunctor.h"
#include <cassert>
#include <vector>
#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

#define VAR 3
#define SYM 2
#define APP 0
#define NUM 1

// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{
souffle::RamDomain count_var(
        souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable, souffle::RamDomain arg) {
    assert(symbolTable && "NULL symbol table");
    assert(recordTable && "NULL record table");
 
    if (arg == 0) {
        return 0;
    } else {
        const souffle::RamDomain* myTuple0 = recordTable->unpack(arg, 2);
        souffle::RamDomain tag = myTuple0[0];
        assert(tag <= 3 && "Unexpected Tag in count_var");
        if(tag == VAR){
            return 1;
        } else if (tag == APP){
            const souffle::RamDomain* fargs = recordTable->unpack(myTuple0[1], 2);
            // Could do something smarter than recursion here.
            return count_var(symbolTable, recordTable, fargs[0]) + count_var(symbolTable, recordTable, fargs[1]);
        } else {
            return 0;
        }
    }
}

}
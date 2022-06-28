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

// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{

    /*
    int32_t f(int32_t x) {
        return x + 1;
    }

    const char *g() {
        return "Hello world";
    }
    */

    souffle::RamDomain myappend(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        if (arg == 0)
        {
            // Argument is nil
            souffle::RamDomain myTuple[2] = {0, 0};
            // Return [0, nil]
            return recordTable->pack(myTuple, 2);
        }
        else
        {
            // Argument is a list element [x, l] where
            // x is a number and l is another list element
            const souffle::RamDomain *myTuple0 = recordTable->unpack(arg, 2);
            souffle::RamDomain myTuple1[2] = {myTuple0[0] + 1, myTuple0[0]};
            // Return [x+1, [x, l]]
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain mypush(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain x)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        if (vec0 == 0)
        { // nil
            assert(size == 0);
            // souffle::RamDomain vec[1] = {x};
            const souffle::RamDomain vec2 = recordTable->pack(&x, 1);
            souffle::RamDomain myTuple1[2] = {1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
        else
        {
            const souffle::RamDomain *data = recordTable->unpack(vec0, size);
            std::vector<souffle::RamDomain> vec;
            for (int i = 0; i < size; i++)
            {
                vec.push_back(data[i]);
            }
            vec.push_back(x);
            const souffle::RamDomain vec2 = recordTable->pack(vec.data(), size + 1);
            souffle::RamDomain myTuple1[2] = {size + 1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain myindex(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain i)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        assert(vec0 != 0 && "Index does not take nil");
        assert(i < size);
        const souffle::RamDomain *data = recordTable->unpack(vec0, size);
        return data[i];
    }

    souffle::RamDomain insort(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain x)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        if (vec0 == 0)
        { // nil
            assert(size == 0);
            // souffle::RamDomain vec[1] = {x};
            const souffle::RamDomain vec2 = recordTable->pack(&x, 1);
            souffle::RamDomain myTuple1[2] = {1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
        else
        {
            const souffle::RamDomain *data = recordTable->unpack(vec0, size);
            std::vector<souffle::RamDomain> vec;
            bool added = false;
            for (int i = 0; i < size; i++)
            {
                souffle::RamDomain q = data[i];
                if (q == x)
                { // already in set.
                    return v;
                }
                else if (!added && q > x)
                {
                    vec.push_back(x);
                    added = true;
                }
                vec.push_back(q);
            }
            if (!added)
            {
                vec.push_back(x);
            }
            const souffle::RamDomain vec2 = recordTable->pack(vec.data(), size + 1);
            souffle::RamDomain myTuple1[2] = {size + 1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain elem(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain x)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        if (vec0 == 0)
        { // nil
            return 0;
        }
        else
        {
            // Could do smarter binary search if sorted
            const souffle::RamDomain *data = recordTable->unpack(vec0, size);
            for (int i = 0; i < size; i++)
            {
                souffle::RamDomain q = data[i];
                if (q == x)
                { // already in set.
                    return 1;
                }
            }
            return 0;
        }
    }

    souffle::RamDomain is_subset(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple0[0];
        const souffle::RamDomain vec1 = myTuple0[1];
        if (vec1 == 0)
        {             // nil
            return 1; // true
        }
        else
        {
            const souffle::RamDomain *myTuple0 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple0[0];
            const souffle::RamDomain vec2 = myTuple0[1];
            if (vec2 == 0)
            {             // nil
                return 0; // true
            }
            if (size1 > size2)
            {
                return 0; // false. smaller set must be subset
            }
            if (vec2 == vec1 && size1 == size2)
            {
                return 1; // equal
            }

            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            for (int i2 = 0; i2 < size2; i2++)
            {
                // These are both early return optimizations
                if (i1 == size1)
                {
                    return 1;
                }
                if (data1[i1] < data2[i2]) // we passed where we should have found data1[i1]
                {
                    return 0;
                }
                // The only one that actually matters.
                else if (data1[i1] == data2[i2])
                {
                    i1++;
                }
                // else data1[i1] > data2[i2] hence we still need to seek
            }
            if (i1 == size1) // we saw all of vec1 in vec2
            {
                return 1;
            }
            else
            {
                return 0;
            }
        }
    }

    // Hmm. I could also have convention that nil = [0,nil]. That would make sense. Could get two nils then. Meh.
    souffle::RamDomain inter(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        if (v2 == v1)
        {
            return v2; // equal
        }
        const souffle::RamDomain *myTuple1 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple1[0];
        const souffle::RamDomain vec1 = myTuple1[1];
        if (vec1 == 0) // nil
        {
            return v1;
        }
        else
        {
            const souffle::RamDomain *myTuple2 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple2[0];
            const souffle::RamDomain vec2 = myTuple2[1];
            if (vec2 == 0) // nil
            {
                return v2; // nil
            }
            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            int i2 = 0;
            std::vector<souffle::RamDomain> vec3;
            while (i1 < size1 && i2 < size2)
            {

                if (data1[i1] < data2[i2])
                {
                    i1++;
                }
                else if (data1[i1] == data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                    i2++;
                }
                else if (data1[i1] > data2[i2])
                {
                    i2++;
                }
            }
            souffle::RamDomain size = vec3.size();
            const souffle::RamDomain vec4 = recordTable->pack(vec3.data(), size);
            souffle::RamDomain myTuple1[2] = {size, vec4};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain set_union(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        if (v1 == v2)
        {
            return v2; // equal
        }
        const souffle::RamDomain *myTuple1 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple1[0];
        const souffle::RamDomain vec1 = myTuple1[1];
        if (vec1 == 0) // nil
        {
            return v2;
        }
        else
        {
            const souffle::RamDomain *myTuple2 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple2[0];
            const souffle::RamDomain vec2 = myTuple2[1];
            if (vec2 == 0) // nil
            {
                return v1; // nil
            }

            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            int i2 = 0;
            std::vector<souffle::RamDomain> vec3;
            // merge of mergesort essentially
            while (i1 < size1 && i2 < size2)
            {
                if (data1[i1] < data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                }
                else if (data1[i1] == data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                    i2++;
                }
                else if (data1[i1] > data2[i2])
                {
                    vec3.push_back(data2[i2]);
                    i2++;
                }
            }
            // cleanup. Only one for loop can actually run.
            for (int i = i1; i < size1; i++)
            {
                vec3.push_back(data1[i]);
            }
            for (int i = i2; i < size2; i++)
            {
                vec3.push_back(data2[i]);
            }
            souffle::RamDomain size = vec3.size();
            const souffle::RamDomain vec4 = recordTable->pack(vec3.data(), size);
            souffle::RamDomain myTuple1[2] = {size, vec4};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain set_diff(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        if (v1 == v2) // return empty set
        {
            souffle::RamDomain myTuple1[2] = {0, 0};
            return recordTable->pack(myTuple1, 2);
        }
        const souffle::RamDomain *myTuple1 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple1[0];
        const souffle::RamDomain vec1 = myTuple1[1];
        if (vec1 == 0) // nil
        {
            return v1;
        }
        else
        {
            const souffle::RamDomain *myTuple2 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple2[0];
            const souffle::RamDomain vec2 = myTuple2[1];
            if (vec2 == 0) // nil
            {
                return v1; // return v1 unchanged
            }

            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            int i2 = 0;
            std::vector<souffle::RamDomain> vec3;
            while (i1 < size1 && i2 < size2)
            {
                if (data1[i1] < data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                }
                else if (data1[i1] == data2[i2])
                {
                    i1++;
                    i2++;
                }
                else if (data1[i1] > data2[i2])
                {
                    i2++;
                }
            }
            for (int i = i1; i < size1; i++)
            {
                vec3.push_back(data1[i]);
            }
            souffle::RamDomain size = vec3.size();
            const souffle::RamDomain vec4 = recordTable->pack(vec3.data(), size);
            souffle::RamDomain myTuple1[2] = {size, vec4};
            return recordTable->pack(myTuple1, 2);
        }
    }
}

/*
What other functions are useful?
Sort
An array based map.
Is it possible souffle garbage collects records?

elem
subset
union
inter


*/

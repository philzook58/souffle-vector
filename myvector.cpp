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

// pass by reference or whatever?
inline souffle::RamDomain mk_vec(souffle::RecordTable *recordTable, const std::vector<souffle::RamDomain> &vec)
{
    const souffle::RamDomain vec2 = recordTable->pack(vec.data(), vec.size());
    souffle::RamDomain myTuple1[2] = {vec.size(), vec2};
    return recordTable->pack(myTuple1, 2);
}

// Eh does this even make sense?
// what does returning a vector do?
inline std::vector<souffle::RamDomain> get_vec(souffle::RecordTable *recordTable, souffle::RamDomain vec_id)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(vec_id, 2);
    const souffle::RamDomain size = myTuple0[0];
    const souffle::RamDomain vec0 = myTuple0[1];
    const souffle::RamDomain *data = recordTable->unpack(vec0, size);
    std::vector<souffle::RamDomain> vec;
    for (int i = 0; i < size; i++)
    {
        vec.push_back(data[i]);
    }
    return vec;
}


// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{

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

    souffle::RamDomain uf_union(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain i, souffle::RamDomain j)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        assert(i < size && j < size && "Out of bounds indexing");
        assert(size != 0 && "UF can't be size 0 for union");
        const souffle::RamDomain *data = recordTable->unpack(vec0, size);
        if (data[i] == data[j])
        { // already in same eqclass
            return v;
        }
        std::vector<souffle::RamDomain> vec;
        souffle::RamDomain pmin = std::min(data[i], data[j]); // pi <= i
        souffle::RamDomain pmax = std::max(data[i], data[j]); //  pj <= j
        for (int k = 0; k < size; k++)
        {
            souffle::RamDomain p = data[k];
            if (p == pmax || p == i || p == j)
            {
                vec.push_back(pmin);
            }
            else
            {
                vec.push_back(data[i]);
            }
        }
        const souffle::RamDomain vec2 = recordTable->pack(vec.data(), size);
        souffle::RamDomain myTuple1[2] = {size, vec2};
        return recordTable->pack(myTuple1, 2);
    }

    // uf_find _is_ @myindex
    souffle::RamDomain norm_str_uf(souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable,
                                   souffle::RamDomain uf_id)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        const std::string &uf = symbolTable->decode(uf_id);
        int cmap[256];
        memset(cmap, -1, sizeof(cmap)); // careful here. Does not generalize
        std::string uf2;
        char fresh = '0';
        for (int i = 0; uf[i] != '\0'; i++)
        {
            int normed = cmap[uf[i]];
            if (normed < 0)
            { // This value has not been seen yet.
                assert(fresh <= 'z' && "You are using a scary size of local union find");
                // std::cout << "fresh" << fresh << std::endl;
                cmap[uf[i]] = fresh;
                uf2.push_back(fresh);
                fresh++;
            }
            else
            {
                // std::cout << "not fresh \n";
                uf2.push_back(static_cast<char>(normed));
            }
        }
        return symbolTable->encode(uf2);
    }

    souffle::RamDomain str_union(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain uf_id, souffle::RamDomain i, souffle::RamDomain j)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const std::string &uf = symbolTable->decode(uf_id);
        assert(i < uf.length() && j < uf.length() && "Out of bound union index.");
        if (uf[i] == uf[j])
        { // already in same eqclass
            return uf_id;
        }
        std::string uf2;
        souffle::RamDomain pmin = std::min(uf[i], uf[j]); // pi <= i
        souffle::RamDomain pmax = std::max(uf[i], uf[j]); //  pj <= j
        for (auto &ch : uf)
        {
            if (ch == pmax)
            {
                uf2.push_back(pmin);
            }
            else
            {
                uf2.push_back(ch);
            }
        }
        return symbolTable->encode(uf2);
    }

    // uf_union
    // uf_inter

    // uf_sub doesn't need normalization persay
    // but we need to know which keys have been seen and which haven't
    // https://en.wikipedia.org/wiki/Partition_of_a_set#Refinement_of_partitions
    souffle::RamDomain str_uf_sub(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain uf_id1, souffle::RamDomain uf_id2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        if (uf_id1 == uf_id2)
        { // Same ufs. Equality
            return 1;
        }

        const std::string &uf1 = symbolTable->decode(uf_id1);
        const std::string &uf2 = symbolTable->decode(uf_id2);
        assert(uf1.length() == uf2.length() && "I'm not sure you should be comparing unequal length union finds");
        if (uf1.length() != uf2.length())
        {
            return 0; // maybe. is 0123 different from 012?
        }

        char cmap[256]; // map from character in uf1 to uf2
        // 012 <= 000 is ok.  000 <= 012 is not.
        // ids in lesser should uniquely match to ids in the latter
        // char seen = '0' - 1;
        bool seen[256] = {false}; // This seems to be ok?
        // memset(cmap, false, sizeof(cmap));
        for (int i = 0; i < uf1.length(); i++)
        {
            if (!seen[uf1[i]]) // uf1[i] > seen) // first time seeing this id. hence cmap is not initialized yet at this position
            {
                // seen = uf1[i];
                seen[uf1[i]] = true;
                cmap[uf1[i]] = uf2[i]; // fill in cmap at this position
            }
            else
            {
                if (cmap[uf1[i]] != uf2[i]) // If two elements from 1 point to different elements from 2, not a finer relation.
                {
                    return 0;
                }
            }
        }
        return 1;
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

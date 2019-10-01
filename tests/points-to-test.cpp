#include <assert.h>
#include <cstdarg>
#include <cstdio>
#include <cstring>

#include "test-runner.h"
#include "test-dg.h"

#include "dg/analysis/PointsTo/PointerGraph.h"
#include "dg/analysis/PointsTo/PointerAnalysisFI.h"
#include "dg/analysis/PointsTo/PointerAnalysisFS.h"
#include "dg/analysis/PointsTo/InvalidatedAnalysis.h"

namespace dg {
namespace tests {

using namespace analysis::pta;
using analysis::Offset;

template <typename PTStoT>
class PointsToTest : public Test
{
public:
    PointsToTest(const char *n) : Test(n) {}

    void store_load()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *S = PS.create(PSNodeType::STORE, A, B);
        PSNode *L = PS.create(PSNodeType::LOAD, B);

        A->addSuccessor(B);
        B->addSuccessor(S);
        S->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L->doesPointsTo(A), "L do not points to A");
    }

    void store_load2()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *C = PS.create(PSNodeType::ALLOC);
        PSNode *S1 = PS.create(PSNodeType::STORE, A, B);
        PSNode *S2 = PS.create(PSNodeType::STORE, C, B);
        PSNode *L1 = PS.create(PSNodeType::LOAD, B);
        PSNode *L2 = PS.create(PSNodeType::LOAD, B);
        PSNode *L3 = PS.create(PSNodeType::LOAD, B);

        /*
         *        A
         *        |
         *        B
         *        |
         *        C
         *      /   \
         *     S1    S2
         *     |      |
         *     L1    L2
         *       \  /
         *        L3
         */
        A->addSuccessor(B);
        B->addSuccessor(C);
        C->addSuccessor(S1);
        C->addSuccessor(S2);
        S1->addSuccessor(L1);
        S2->addSuccessor(L2);
        L1->addSuccessor(L3);
        L2->addSuccessor(L3);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A), "not L1->A");
        check(L2->doesPointsTo(C), "not L2->C");
        check(L3->doesPointsTo(A), "not L3->A");
        check(L3->doesPointsTo(C), "not L3->C");
    }

    void store_load3()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *C = PS.create(PSNodeType::ALLOC);
        PSNode *S1 = PS.create(PSNodeType::STORE, A, B);
        PSNode *L1 = PS.create(PSNodeType::LOAD, B);
        PSNode *S2 = PS.create(PSNodeType::STORE, C, B);
        PSNode *L2 = PS.create(PSNodeType::LOAD, B);

        A->addSuccessor(B);
        B->addSuccessor(C);
        C->addSuccessor(S1);
        S1->addSuccessor(L1);
        L1->addSuccessor(S2);
        S2->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A), "L1 do not points to A");
        check(L2->doesPointsTo(C), "L2 do not points to C");
    }

    void store_load4()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(8);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *C = PS.create(PSNodeType::ALLOC);
        PSNode *GEP = PS.create(PSNodeType::GEP, A, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP, B);
        PSNode *L1 = PS.create(PSNodeType::LOAD, B);
        PSNode *S2 = PS.create(PSNodeType::STORE, C, B);
        PSNode *L2 = PS.create(PSNodeType::LOAD, B);

        A->addSuccessor(B);
        B->addSuccessor(C);
        C->addSuccessor(GEP);
        GEP->addSuccessor(S1);
        S1->addSuccessor(L1);
        L1->addSuccessor(S2);
        S2->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 4), "L1 do not points to A[4]");
        check(L2->doesPointsTo(C), "L2 do not points to C");
    }

    void store_load5()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(8);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        B->setSize(16);
        PSNode *C = PS.create(PSNodeType::ALLOC);
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 4);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, B, 8);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, GEP2);
        PSNode *GEP3 = PS.create(PSNodeType::GEP, B, 8);
        PSNode *L1 = PS.create(PSNodeType::LOAD, GEP3);
        PSNode *S2 = PS.create(PSNodeType::STORE, C, B);
        PSNode *L2 = PS.create(PSNodeType::LOAD, B);

        A->addSuccessor(B);
        B->addSuccessor(C);
        C->addSuccessor(GEP1);
        GEP1->addSuccessor(GEP2);
        GEP2->addSuccessor(S1);
        S1->addSuccessor(GEP3);
        GEP3->addSuccessor(L1);
        L1->addSuccessor(S2);
        S2->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 4), "L1 do not points to A[4]");
        check(L2->doesPointsTo(C), "L2 do not points to C");
    }

    void gep1()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        // we must set size, so that GEP won't
        // make the offset UNKNOWN
        A->setSize(8);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 4);
        PSNode *S = PS.create(PSNodeType::STORE, B, GEP1);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, A, 4);
        PSNode *L = PS.create(PSNodeType::LOAD, GEP2);

        A->addSuccessor(B);
        B->addSuccessor(GEP1);
        GEP1->addSuccessor(S);
        S->addSuccessor(GEP2);
        GEP2->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(GEP1->doesPointsTo(A, 4), "not GEP1 -> A + 4");
        check(GEP2->doesPointsTo(A, 4), "not GEP2 -> A + 4");
        check(L->doesPointsTo(B), "not L -> B + 0");
    }

    void gep2()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(16);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 4);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, GEP1, 4);
        PSNode *S = PS.create(PSNodeType::STORE, B, GEP2);
        PSNode *GEP3 = PS.create(PSNodeType::GEP, A, 8);
        PSNode *L = PS.create(PSNodeType::LOAD, GEP3);

        A->addSuccessor(B);
        B->addSuccessor(GEP1);
        GEP1->addSuccessor(GEP2);
        GEP2->addSuccessor(S);
        S->addSuccessor(GEP3);
        GEP3->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(GEP1->doesPointsTo(A, 4), "not GEP1 -> A + 4");
        // XXX whata??
        //check(GEP2.doesPointsTo(&A, 8), "not GEP2 -> A + 4");
        //check(L.doesPointsTo(&B), "not L -> B + 0");
        check(L->doesPointsTo(B), "not L -> B + 0");
    }

    void gep3()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *ARRAY = PS.create(PSNodeType::ALLOC);
        ARRAY->setSize(40);
        PSNode *GEP1 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, ARRAY, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, A, GEP1);
        PSNode *S2 = PS.create(PSNodeType::STORE, B, GEP2);
        PSNode *GEP3 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *GEP4 = PS.create(PSNodeType::GEP, ARRAY, 4);
        PSNode *L1 = PS.create(PSNodeType::LOAD, GEP3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, GEP4);

        A->addSuccessor(B);
        B->addSuccessor(ARRAY);
        ARRAY->addSuccessor(GEP1);
        GEP1->addSuccessor(GEP2);
        GEP2->addSuccessor(S1);
        S1->addSuccessor(S2);
        S2->addSuccessor(GEP3);
        GEP3->addSuccessor(GEP4);
        GEP4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A), "not L1->A");
        check(L2->doesPointsTo(B), "not L2->B");
    }

    void gep4()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNodeAlloc *ARRAY = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        ARRAY->setSize(40);
        PSNode *GEP1 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, ARRAY, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, A, GEP1);
        PSNode *S2 = PS.create(PSNodeType::STORE, B, GEP2);
        PSNode *GEP3 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *GEP4 = PS.create(PSNodeType::GEP, ARRAY, 4);
        PSNode *L1 = PS.create(PSNodeType::LOAD, GEP3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, GEP4);

        A->addSuccessor(B);
        B->addSuccessor(ARRAY);
        ARRAY->addSuccessor(GEP1);
        ARRAY->addSuccessor(GEP2);

        GEP1->addSuccessor(S1);
        S1->addSuccessor(GEP3);

        GEP2->addSuccessor(S2);
        S2->addSuccessor(GEP3);

        GEP3->addSuccessor(GEP4);
        GEP4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A), "not L1->A");
        check(L2->doesPointsTo(B), "not L2->B");
    }

    void gep5()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *ARRAY = PS.create(PSNodeType::ALLOC);
        ARRAY->setSize(20);
        PSNode *GEP1 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, ARRAY, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, A, GEP1);
        PSNode *S2 = PS.create(PSNodeType::STORE, B, GEP2);
        PSNode *GEP3 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *GEP4 = PS.create(PSNodeType::GEP, ARRAY, 4);
        PSNode *L1 = PS.create(PSNodeType::LOAD, GEP3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, GEP4);
        PSNode *GEP5 = PS.create(PSNodeType::GEP, ARRAY, 0);
        PSNode *S3 = PS.create(PSNodeType::STORE, B, GEP5);
        PSNode *L3 = PS.create(PSNodeType::LOAD, GEP5);

        A->addSuccessor(B);
        B->addSuccessor(ARRAY);
        ARRAY->addSuccessor(GEP1);
        ARRAY->addSuccessor(GEP2);

        GEP1->addSuccessor(S1);
        S1->addSuccessor(GEP3);

        GEP2->addSuccessor(S2);
        S2->addSuccessor(GEP5);
        GEP5->addSuccessor(S3);
        S3->addSuccessor(L3);
        L3->addSuccessor(GEP3);

        GEP3->addSuccessor(GEP4);
        GEP4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A), "not L1->A");
        check(L1->doesPointsTo(B), "not L1->B");
        check(L2->doesPointsTo(B), "not L2->B");
        check(L3->doesPointsTo(B), "not L2->B");
    }

    void nulltest()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *B = PS.create(PSNodeType::ALLOC);
        PSNode *S = PS.create(PSNodeType::STORE, pta::NULLPTR, B);
        PSNode *L = PS.create(PSNodeType::LOAD, B);

        B->addSuccessor(S);
        S->addSuccessor(L);

        auto subg = PS.createSubgraph(B);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L->doesPointsTo(NULLPTR), "L do not points to NULL");
    }

    void constant_store()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        B->setSize(16);
        PSNode *C = PS.create(PSNodeType::CONSTANT, B, 4);
        PSNode *S = PS.create(PSNodeType::STORE, A, C);
        PSNode *GEP = PS.create(PSNodeType::GEP, B, 4);
        PSNode *L = PS.create(PSNodeType::LOAD, GEP);

        A->addSuccessor(B);
        B->addSuccessor(S);
        S->addSuccessor(GEP);
        GEP->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L->doesPointsTo(A), "L do not points to A");
    }

    void load_from_zeroed()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNodeAlloc *B = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        B->setZeroInitialized();
        PSNode *L = PS.create(PSNodeType::LOAD, B);

        B->addSuccessor(L);

        auto subg = PS.createSubgraph(B);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L->doesPointsTo(NULLPTR), "L do not points to nullptr");
    }

    void load_from_unknown_offset()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        B->setSize(20);
        PSNode *GEP = PS.create(PSNodeType::GEP, B, Offset::UNKNOWN);
        PSNode *S = PS.create(PSNodeType::STORE, A, GEP);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, B, 4);
        PSNode *L = PS.create(PSNodeType::LOAD, GEP2); // load from B + 4

        A->addSuccessor(B);
        B->addSuccessor(GEP);
        GEP->addSuccessor(S);
        S->addSuccessor(GEP2);
        GEP2->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        // B points to A + 0 at unknown offset,
        // so load from B + 4 should be A + 0
        check(L->doesPointsTo(A), "L do not points to A");
    }

    void load_from_unknown_offset2()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        B->setSize(20);
        PSNode *GEP = PS.create(PSNodeType::GEP, B, 4);
        PSNode *S = PS.create(PSNodeType::STORE, A, GEP);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, B, Offset::UNKNOWN);
        PSNode *L = PS.create(PSNodeType::LOAD, GEP2); // load from B + Offset::UNKNOWN

        A->addSuccessor(B);
        B->addSuccessor(GEP);
        GEP->addSuccessor(S);
        S->addSuccessor(GEP2);
        GEP2->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        // B points to A + 0 at offset 4,
        // so load from B + UNKNOWN should be A + 0
        check(L->doesPointsTo(A), "L do not points to A");
    }

    void load_from_unknown_offset3()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        PSNode *B = PS.create(PSNodeType::ALLOC);
        B->setSize(20);
        PSNode *GEP = PS.create(PSNodeType::GEP, B, Offset::UNKNOWN);
        PSNode *S = PS.create(PSNodeType::STORE, A, GEP);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, B, Offset::UNKNOWN);
        PSNode *L = PS.create(PSNodeType::LOAD, GEP2);

        A->addSuccessor(B);
        B->addSuccessor(GEP);
        GEP->addSuccessor(S);
        S->addSuccessor(GEP2);
        GEP2->addSuccessor(L);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L->doesPointsTo(A), "L do not points to A");
    }

    void memcpy_test()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(20);
        PSNode *SRC = PS.create(PSNodeType::ALLOC);
        SRC->setSize(16);
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        /* initialize SRC, so that
         * it will point to A + 3 and A + 12
         * at offsets 4 and 8 */
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, A, 12);
        PSNode *G1 = PS.create(PSNodeType::GEP, SRC, 4);
        PSNode *G2 = PS.create(PSNodeType::GEP, SRC, 8);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, G1);
        PSNode *S2 = PS.create(PSNodeType::STORE, GEP2, G2);

        /* copy the memory,
         * after this node dest should point to
         * A + 3 and A + 12 at offsets 4 and 8 */
        PSNode *CPY = PS.create(PSNodeType::MEMCPY, SRC, DEST,
                                Offset::UNKNOWN /* len = all */);

        /* load from the dest memory */
        PSNode *G3 = PS.create(PSNodeType::GEP, DEST, 4);
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 8);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G4);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(GEP2);
        GEP2->addSuccessor(G1);
        G1->addSuccessor(G2);
        G2->addSuccessor(S1);
        S1->addSuccessor(S2);
        S2->addSuccessor(CPY);
        CPY->addSuccessor(G3);
        G3->addSuccessor(G4);
        G4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 3), "L do not points to A + 3");
        check(L2->doesPointsTo(A, 12), "L do not points to A + 12");
    }

    void memcpy_test2()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(20);
        PSNode *SRC = PS.create(PSNodeType::ALLOC);
        SRC->setSize(16);
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        /* initialize SRC, so that
         * it will point to A + 3 and A + 12
         * at offsets 4 and 8 */
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, A, 12);
        PSNode *G1 = PS.create(PSNodeType::GEP, SRC, 4);
        PSNode *G2 = PS.create(PSNodeType::GEP, SRC, 8);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, G1);
        PSNode *S2 = PS.create(PSNodeType::STORE, GEP2, G2);

        /* copy first 8 bytes from the memory,
         * after this node dest should point to
         * A + 3 at offset 4  = PS.create(8 is 9th byte,
         * so it should not be included) */
        PSNode *CPY = PS.create(PSNodeType::MEMCPY, SRC, DEST, 8 /* len*/);

        /* load from the dest memory */
        PSNode *G3 = PS.create(PSNodeType::GEP, DEST, 4);
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 8);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G4);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(GEP2);
        GEP2->addSuccessor(G1);
        G1->addSuccessor(G2);
        G2->addSuccessor(S1);
        S1->addSuccessor(S2);
        S2->addSuccessor(CPY);
        CPY->addSuccessor(G3);
        G3->addSuccessor(G4);
        G4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 3), "L1 do not points to A + 3");
        check(L2->pointsTo.empty(), "L2 is not empty");
    }

    void memcpy_test3()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(20);
        PSNode *SRC = PS.create(PSNodeType::ALLOC);
        SRC->setSize(16);
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        /* initialize SRC, so that
         * it will point to A + 3 and A + 12
         * at offsets 4 and 8 */
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *GEP2 = PS.create(PSNodeType::GEP, A, 12);
        PSNode *G1 = PS.create(PSNodeType::GEP, SRC, 4);
        PSNode *G2 = PS.create(PSNodeType::GEP, SRC, 8);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, G1);
        PSNode *S2 = PS.create(PSNodeType::STORE, GEP2, G2);

        /* copy memory from 8 bytes and further
         * after this node dest should point to
         * A + 12 at offset 0 */
        PSNode *CPY = PS.create(PSNodeType::MEMCPY, G2, DEST,
                                Offset::UNKNOWN /* len*/);

        /* load from the dest memory */
        PSNode *G3 = PS.create(PSNodeType::GEP, DEST, 4);
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 0);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G4);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(GEP2);
        GEP2->addSuccessor(G1);
        G1->addSuccessor(G2);
        G2->addSuccessor(S1);
        S1->addSuccessor(S2);
        S2->addSuccessor(CPY);
        CPY->addSuccessor(G3);
        G3->addSuccessor(G4);
        G4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L2->doesPointsTo(A, 12), "L2 do not points to A + 12");
        check(L1->pointsTo.empty(), "L1 is not empty");
    }

    void memcpy_test4()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNodeAlloc *A = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        A->setSize(20);
        PSNodeAlloc *SRC = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        SRC->setSize(16);
        SRC->setZeroInitialized();
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        /* initialize SRC, so that it will point to A + 3 at offset 4 */
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *G1 = PS.create(PSNodeType::GEP, SRC, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, G1);

        /* copy memory from 8 bytes and further after this node dest should
         * point to NULL */
        PSNode *G3 = PS.create(PSNodeType::GEP, SRC, 8);
        PSNode *CPY = PS.create(PSNodeType::MEMCPY, G3, DEST,
                                Offset::UNKNOWN /* len*/);

        /* load from the dest memory */
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 0);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G3);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G4);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(G1);
        G1->addSuccessor(S1);
        S1->addSuccessor(G3);
        G3->addSuccessor(CPY);
        CPY->addSuccessor(G4);
        G4->addSuccessor(L1);
        L1->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(NULLPTR), "L1 does not point to NULL");
        check(L2->doesPointsTo(NULLPTR), "L2 does not point to NULL");
    }

    void memcpy_test5()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(20);
        PSNode *SRC = PS.create(PSNodeType::ALLOC);
        SRC->setSize(16);
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *G1 = PS.create(PSNodeType::GEP, SRC, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, G1);

        // copy the only pointer to dest + 0
        PSNode *CPY = PS.create(PSNodeType::MEMCPY, G1, DEST, 1);

        /* load from the dest memory */
        PSNode *G3 = PS.create(PSNodeType::GEP, DEST, 0);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G3);
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 1);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G4);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(G1);
        G1->addSuccessor(S1);
        S1->addSuccessor(CPY);
        CPY->addSuccessor(G3);
        G3->addSuccessor(L1);
        L1->addSuccessor(G4);
        G4->addSuccessor(L2);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 3), "L2 do not points to A + 3");
        check(L2->pointsTo.empty(), "L2 does not have empty points-to");
    }

    void memcpy_test6()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNode *A = PS.create(PSNodeType::ALLOC);
        A->setSize(20);
        PSNode *SRC = PS.create(PSNodeType::ALLOC);
        SRC->setSize(16);
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *G1 = PS.create(PSNodeType::GEP, SRC, 4);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, G1);
        PSNode *G3 = PS.create(PSNodeType::GEP, DEST, 5);
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 1);

        PSNode *CPY = PS.create(PSNodeType::MEMCPY, SRC, G4, 8);

        /* load from the dest memory */
        PSNode *L1 = PS.create(PSNodeType::LOAD, G3);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(G1);
        G1->addSuccessor(S1);
        S1->addSuccessor(G3);
        G3->addSuccessor(G4);
        G4->addSuccessor(CPY);
        CPY->addSuccessor(L1);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 3), "L2 do not points to A + 3");
    }

    void memcpy_test7()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNodeAlloc *A = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        PSNodeAlloc *SRC = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        PSNode *DEST = PS.create(PSNodeType::ALLOC);

        A->setSize(20);
        SRC->setSize(16);
        SRC->setZeroInitialized();
        DEST->setSize(16);

        PSNode *CPY = PS.create(PSNodeType::MEMCPY, SRC, DEST,
                                Offset::UNKNOWN /* len*/);

        /* load from the dest memory */
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 0);
        PSNode *G5 = PS.create(PSNodeType::GEP, DEST, 4);
        PSNode *G6 = PS.create(PSNodeType::GEP, DEST, Offset::UNKNOWN);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G4);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G5);
        PSNode *L3 = PS.create(PSNodeType::LOAD, G6);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(CPY);
        CPY->addSuccessor(G4);
        G4->addSuccessor(G5);
        G5->addSuccessor(G6);
        G6->addSuccessor(L1);
        L1->addSuccessor(L2);
        L2->addSuccessor(L3);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(NULLPTR), "L1 does not point to NULL");
        check(L2->doesPointsTo(NULLPTR), "L2 does not point to NULL");
        check(L3->doesPointsTo(NULLPTR), "L2 does not point to NULL");
    }

    void memcpy_test8()
    {
        using namespace analysis;

        PointerGraph PS;
        PSNodeAlloc *A = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        A->setSize(20);
        PSNodeAlloc *SRC = PSNodeAlloc::get(PS.create(PSNodeType::ALLOC));
        SRC->setSize(16);
        SRC->setZeroInitialized();
        PSNode *DEST = PS.create(PSNodeType::ALLOC);
        DEST->setSize(16);

        /* initialize SRC, so that it will point to A + 3 at offset 0 */
        PSNode *GEP1 = PS.create(PSNodeType::GEP, A, 3);
        PSNode *S1 = PS.create(PSNodeType::STORE, GEP1, SRC);

        PSNode *CPY = PS.create(PSNodeType::MEMCPY, SRC, DEST, 10);

        /* load from the dest memory */
        PSNode *G1 = PS.create(PSNodeType::GEP, DEST, 0);
        PSNode *G3 = PS.create(PSNodeType::GEP, DEST, 4);
        PSNode *G4 = PS.create(PSNodeType::GEP, DEST, 8);
        PSNode *L1 = PS.create(PSNodeType::LOAD, G1);
        PSNode *L2 = PS.create(PSNodeType::LOAD, G3);
        PSNode *L3 = PS.create(PSNodeType::LOAD, G4);

        A->addSuccessor(SRC);
        SRC->addSuccessor(DEST);
        DEST->addSuccessor(GEP1);
        GEP1->addSuccessor(G1);
        G1->addSuccessor(S1);
        S1->addSuccessor(G3);
        G3->addSuccessor(CPY);
        CPY->addSuccessor(G4);
        G4->addSuccessor(L1);
        L1->addSuccessor(L2);
        L2->addSuccessor(L3);

        auto subg = PS.createSubgraph(A);
        PS.setEntry(subg);
        PTStoT PA(&PS);
        PA.run();

        check(L1->doesPointsTo(A, 3), "L1 does not point A + 3");
        check(L2->doesPointsTo(NULLPTR), "L2 does not point to NULL");
        check(L3->doesPointsTo(NULLPTR), "L3 does not point to NULL");
    }

    void test()
    {
        store_load();
        store_load2();
        store_load3();
        store_load4();
        store_load5();
        gep1();
        gep2();
        gep3();
        gep4();
        gep5();
        nulltest();
        constant_store();
        load_from_zeroed();
        load_from_unknown_offset();
        load_from_unknown_offset2();
        load_from_unknown_offset3();
        memcpy_test();
        memcpy_test2();
        memcpy_test3();
        memcpy_test4();
        memcpy_test5();
        memcpy_test6();
        memcpy_test7();
        memcpy_test8();
    }
};

class FlowInsensitivePointsToTest
    : public PointsToTest<analysis::pta::PointerAnalysisFI>
{
public:
    FlowInsensitivePointsToTest()
        : PointsToTest<analysis::pta::PointerAnalysisFI>
          ("flow-insensitive points-to test") {}
};

class FlowSensitivePointsToTest
    : public PointsToTest<analysis::pta::PointerAnalysisFS>
{
public:
    FlowSensitivePointsToTest()
        : PointsToTest<analysis::pta::PointerAnalysisFS>
          ("flow-sensitive points-to test") {}
};

class PSNodeTest : public Test
{

public:
    PSNodeTest()
          : Test("PSNode test") {}

    void unknown_offset1()
    {
        using namespace dg::analysis::pta;
        PointerGraph PS;
        PSNode *N1 = PS.create(PSNodeType::ALLOC);
        PSNode *N2 = PS.create(PSNodeType::LOAD, N1);

        N2->addPointsTo(N1, 1);
        N2->addPointsTo(N1, 2);
        N2->addPointsTo(N1, 3);
        check(N2->pointsTo.size() == 3);
        N2->addPointsTo(N1, Offset::UNKNOWN);
        check(N2->pointsTo.size() == 1);
        check(N2->addPointsTo(N1, 3) == false);
    }

    void test()
    {
        unknown_offset1();
    }
};

#define printState = false

class InvalidatedAnalysisTest : public Test {
public:
    InvalidatedAnalysisTest(const char* n) : Test(n) {}

    using St = InvalidatedAnalysis::State;

    std::string printPredsSuccs(const PSNode* node) const {
        std::stringstream ss;
        ss << PSNodeTypeToCString(node->getType()) << "[" << node->getID() << "] [preds:";
        for (auto* nd : node->getPredecessors()) {
            ss << " " << PSNodeTypeToCString(nd->getType());
        }
        ss << "] [succs:";
        for (auto* nd : node->getSuccessors()) {
            ss << " " << PSNodeTypeToCString(nd->getType());
        }
        ss << "]\n";
        return ss.str();
    }

    void memLeak_basic_must() {
        using namespace analysis;
        PointerGraph PS;
        /*
            [malloc]
               |
            [free]
               |
            [test_load] // must be invalidated
         */

        PSNodeAlloc* malloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        malloc->setIsHeap();

        PSNode* free = PS.create(PSNodeType::FREE, static_cast<PSNode*>(malloc));

        PSNode* test_load = PS.create(PSNodeType::LOAD, malloc);

        malloc->addSuccessor(free);
        free->addSuccessor(test_load);
        test_load->addPointsTo(static_cast<PSNode*>(malloc), 0);
//        auto sg = PS.createSubgraph(malloc); // TODO: what is this for?
//        PS.setEntry(sg);

        InvalidatedAnalysis IA (&PS);
        IA.run();

        St* frState = IA.getState(free);
        St* ldState = IA.getState(test_load);

//      for (auto* st : {mlState, frState, ldState})
//            std::cout << st->_tmpStateToString() << '\n';

        check(frState->mustContains(malloc), "[memLeak_basic_must] Free's mustBeInv doesn't contain 'malloc*'\n");
        check(!frState->mayContains(malloc), "[memLeak_basic_must] Free's mayBeInv cannot contain 'malloc*\n");
        check(ldState->mustContains(malloc), "[memLeak_basic_must] Load's mustBeInv cannot contain 'malloc*'\n");
        check(!ldState->mayContains(malloc), "[memLeak_basic_must] Load's mayBeInv cannot contain 'malloc*'\n");
        check(test_load->pointsTo.hasInvalidated(), "[memLeak_basic_must] Load does not point to INV\n");
    }

    void memLeak_basic_may() {
        using namespace analysis;
        PointerGraph PS;
        /*
                   [malloc]
                    /    \
              [load]     [free]
                    \    /
                  [test_load] // may be invalidated
         */

        PSNodeAlloc* malloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        malloc->setIsHeap();

        PSNode* free = PS.create(PSNodeType::FREE, static_cast<PSNode*>(malloc));

        PSNode* load = PS.create(PSNodeType::LOAD, malloc);
        PSNode* test_load = PS.create(PSNodeType::LOAD, malloc);

        malloc->addSuccessor(load);
        malloc->addSuccessor(free);
        free->addSuccessor(test_load);
        load->addSuccessor(test_load);
        load->addPointsTo(static_cast<PSNode*>(malloc), 0);
        test_load->addPointsTo(static_cast<PSNode*>(malloc), 0);

        InvalidatedAnalysis IA (&PS);
        IA.run();

        St* mlState = IA.getState(malloc);
        St* frState = IA.getState(free);
        St* ldState = IA.getState(load);
        St* test_loadState = IA.getState(test_load);

//        for (auto* st : {mlState, frState, ldState})
//            std::cout << st->_tmpStateToString() << '\n';

        check(!mlState->mustContains(malloc), "[memLeak_basic_may] Load's mustBeInv cannot contain 'malloc*'\n");
        check(!mlState->mayContains(malloc), "[memLeak_basic_may] Load's mayBeInv cannot contain 'malloc*'\n");

        check(!ldState->mustContains(malloc), "[memLeak_basic_may] Load's mustBeInv cannot contain 'malloc*'\n");
        check(!ldState->mayContains(malloc), "[memLeak_basic_may] Load's mayBeInv cannot contain 'malloc*'\n");

        check(frState->mustContains(malloc), "[memLeak_basic_may] Free's mustBeInv cannot contain 'malloc*'\n");
        check(!frState->mayContains(malloc), "[memLeak_basic_may] Free's mayBeInv doesn't contain 'malloc*'\n");

        check(!test_loadState->mustContains(malloc), "[memLeak_basic_may] Load's mustBeInv cannot contain 'malloc*'\n");
        check(test_loadState->mayContains(malloc), "[memLeak_basic_may] Load's mayBeInv doesnt contain 'malloc*'\n");

        check(test_load->pointsTo.hasInvalidated(), "[memLeak_basic_may] Load does not point to INV\n");
    }

    void memLeak_must1() {
        using namespace analysis;
        PointerGraph PS;
        /*
               [entryMain]
                  |
               [call]
                     \
                      [entryFoo]
                         |
                      [malloc]
                         |
                       [free]
                         |
                       [ret]
                      /
              [call_return]
                 |
              [test_load] // must be invalidated
         */

        PSNodeEntry* entryMain = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeCall* call = PSNodeCall::cast(PS.create(PSNodeType::CALL));
        PSNodeEntry* entryFoo = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeAlloc* malloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        PSNode* free = PS.create(PSNodeType::FREE, static_cast<PSNode*>(malloc));
        PSNodeRet* ret = PSNodeRet::get(PS.create(PSNodeType::RETURN, static_cast<PSNode*>(entryFoo)));
        PSNodeCallRet* callRet = PSNodeCallRet::cast(PS.create(PSNodeType::CALL_RETURN, static_cast<PSNode*>(call)));
        PSNode* test_load = PS.create(PSNodeType::LOAD, malloc);

        entryMain->addSuccessor(call);
        call->addSuccessor(callRet);
        callRet->addSuccessor(test_load);

        entryFoo->addSuccessor(malloc);
        malloc->addSuccessor(free);
        free->addSuccessor(ret);

        call->addOperand(callRet);
        malloc->setIsHeap();
        callRet->addOperand(ret);
        callRet->addReturn(ret);

        auto* mainSubGraph = PS.createSubgraph(entryMain);
        entryMain->setParent(mainSubGraph);
        call->setParent(mainSubGraph);
        callRet->setParent(mainSubGraph);
        test_load->setParent(mainSubGraph);

        auto* functionSubGraph = PS.createSubgraph(entryFoo);
        entryFoo->setParent(functionSubGraph);
        malloc->setParent(functionSubGraph);
        free->setParent(functionSubGraph);
        ret->setParent(functionSubGraph);

        test_load->addPointsTo(malloc, 0);

        InvalidatedAnalysis IA(&PS);
        IA.run();

        St* ldState = IA.getState(test_load);
        check(ldState->mustContains(malloc), "[memLeak_must1] Load's mustBeInv does not contain 'malloc*'\n");
        check(!ldState->mayContains(malloc), "[memLeak_must1] Load's mayBeInv cannot contain 'malloc*'\n");
        check(test_load->pointsTo.hasInvalidated(), "[memLeak_must1] Load does not point to INV\n");
    }

    void memLeak_may1() {
        using namespace analysis;
        PointerGraph PS;
        /*
               [entryMain]
                  |
               [call]
                     \
                      [entryFoo]
                         |
                      [malloc]
                         |   \
                         |    [free]
                         |   /
                        [load] // may be invalidated
                          |
                        [return]
                      /
              [call return]
                 |
              [test_load] // may be invalidated
         */


        PSNodeCall* call = PSNodeCall::cast(PS.create(PSNodeType::CALL));
        PSNodeEntry* entryFoo = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeAlloc* malloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        PSNode* free = PS.create(PSNodeType::FREE, malloc);
        PSNode* load = PS.create(PSNodeType::LOAD, malloc);
        PSNodeRet* ret = PSNodeRet::get(PS.create(PSNodeType::RETURN, entryFoo));
        PSNodeCallRet* callRet = PSNodeCallRet::cast(PS.create(PSNodeType::CALL_RETURN, call));
        PSNode* test_load = PS.create(PSNodeType::LOAD, malloc);

        call->addSuccessor(callRet);
        callRet->addSuccessor(test_load);

        entryFoo->addSuccessor(malloc);
        malloc->addSuccessor(load);
        malloc->addSuccessor(free);
        free->addSuccessor(load);
        load->addSuccessor(ret);

        call->addOperand(callRet);
        malloc->setIsHeap();
        callRet->addOperand(ret);
        callRet->addReturn(ret);

        auto* mainSubGraph = PS.createSubgraph(call);
        call->setParent(mainSubGraph);
        callRet->setParent(mainSubGraph);
        test_load->setParent(mainSubGraph);

        auto* functionSubGraph = PS.createSubgraph(entryFoo);
        entryFoo->setParent(functionSubGraph);
        malloc->setParent(functionSubGraph);
        free->setParent(functionSubGraph);
        load->setParent(functionSubGraph);
        ret->setParent(functionSubGraph);

        load->addPointsTo(malloc, 0);
        test_load->addPointsTo(malloc, 0);

        InvalidatedAnalysis IA(&PS);
        IA.run();

        St* ldState = IA.getState(load);
        St* test_ldState = IA.getState(test_load);

        check(!ldState->mustContains(malloc), "[memLeak_may1] Load's mustBeInv cannot contain 'malloc*'\n");
        check(ldState->mayContains(malloc), "[memLeak_may1] Load's mayBeInv does not contain 'malloc*'\n");
        check(!test_ldState->mustContains(malloc), "[memLeak_may1] Load's mustBeInv cannot contain 'malloc*'\n");
        check(test_ldState->mayContains(malloc), "[memLeak_may1] Load's mayBeInv does not contain 'malloc*'\n");

        check(load->pointsTo.hasInvalidated(), "[memLeak_may1] Load does not point to INV\n");
        check(test_load->pointsTo.hasInvalidated(), "[memLeak_may1] Load does not point to INV\n");
    }


    void locInv_basic_must() {
        using namespace analysis;
        PointerGraph PS;
        /*
                [entryMain]
                   |
                 [call]
                       \
                        [entryFoo]
                           |
                        [alloc]
                           |
                        [loadFoo (alloc)]
                           |
                        [return]
                       /
             [call_return]
                   |
              [loadMain (alloc)] // alloc must be inv
         */

        PSNodeEntry* entryMain = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeCall* call = PSNodeCall::cast(PS.create(PSNodeType::CALL));
        PSNodeEntry* entryFoo = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeAlloc* alloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        PSNode* loadFoo = PS.create(PSNodeType::LOAD, alloc);
        PSNodeRet* ret = PSNodeRet::get(PS.create(PSNodeType::RETURN, entryFoo));
        PSNodeCallRet* callRet = PSNodeCallRet::cast(PS.create(PSNodeType::CALL_RETURN, call));
        PSNode* loadMain = PS.create(PSNodeType::LOAD, alloc);

        entryMain->addSuccessor(call);
        call->addSuccessor(callRet);
        callRet->addSuccessor(loadMain);

        entryFoo->addSuccessor(alloc);
        alloc->addSuccessor(loadFoo);
        loadFoo->addSuccessor(ret);

        call->addOperand(callRet);
        callRet->addOperand(ret);
        callRet->addReturn(ret);

        auto* mainSubG = PS.createSubgraph(entryMain);
        entryMain->setParent(mainSubG);
        call->setParent(mainSubG);
        callRet->setParent(mainSubG);
        loadMain->setParent(mainSubG);
        auto* fooSubG = PS.createSubgraph(entryFoo);
        entryFoo->setParent(fooSubG);
        alloc->setParent(fooSubG);
        loadFoo->setParent(fooSubG);
        ret->setParent(fooSubG);

        loadFoo->addPointsTo(alloc, 0);
        loadMain->addPointsTo(alloc, 0);

        InvalidatedAnalysis IA(&PS);
        IA.run();

        St* ldFoo = IA.getState(loadFoo);
        St* ldMain = IA.getState(loadMain);

        check(!ldFoo->mustContains(alloc), "[locInv_basic_must] Load's mustBeInv cannot contain 'alloc*'\n");
        check(!ldFoo->mayContains(alloc), "[locInv_basic_must] Load's mayBeInv cannot contain 'alloc*'\n");
        check(ldMain->mustContains(alloc), "[locInv_basic_must] Load's mustBeInv does not contain 'alloc*'\n");
        check(!ldMain->mayContains(alloc), "[locInv_basic_must] Load's mayBeInv cannot contain 'alloc*'\n");

        check(!loadFoo->doesPointsTo(INVALIDATED), "[locInv_basic_must] Load cannot point to INV\n");
        check(loadMain->doesPointsTo(INVALIDATED), "[locInv_basic_must] Load does not point to INV\n");
        check(!loadMain->doesPointsTo(alloc), "[locInv_basic_must] Load cannot point to 'alloc'\n")
    }

    void locInv_basic_may() {
        using namespace analysis;
        PointerGraph PS;
        /*
               [entryMain]
                 |   \
                 |    [call]
                 |          \
                 |           [entryFoo]
                 |              |
                 |           [alloc]
                 |              |
                 |          [loadFoo]
                 |              |
                 |           [retFoo]
                 |          /
                 |  [call_return]
                  \    /
               [loadMain] // alloc may be inv
                    |
                 [retMain]
         */

        PSNodeEntry* entryMain = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeCall* call = PSNodeCall::cast(PS.create(PSNodeType::CALL));
        PSNodeEntry* entryFoo = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeAlloc* alloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        PSNode* loadFoo = PS.create(PSNodeType::LOAD, alloc);
        PSNodeRet* retFoo = PSNodeRet::get(PS.create(PSNodeType::RETURN, entryFoo));
        PSNodeCallRet* callRet = PSNodeCallRet::cast(PS.create(PSNodeType::CALL_RETURN, call));
        PSNode* loadMain = PS.create(PSNodeType::LOAD, alloc);
        PSNodeRet* retMain = PSNodeRet::get(PS.create(PSNodeType::RETURN, entryMain));

        entryMain->addSuccessor(call);
        entryMain->addSuccessor(loadMain);
        call->addSuccessor(callRet);
        callRet->addSuccessor(loadMain);
        loadMain->addSuccessor(retMain);

        entryFoo->addSuccessor(alloc);
        alloc->addSuccessor(loadFoo);
        loadFoo->addSuccessor(retFoo);
        retFoo->addSuccessor(callRet);

        call->addOperand(callRet);
        callRet->addOperand(retFoo);
        callRet->addReturn(retFoo);

        auto* mainSubG = PS.createSubgraph(entryMain);
        entryMain->setParent(mainSubG);
        call->setParent(mainSubG);
        loadMain->setParent(mainSubG);
        callRet->setParent(mainSubG);
        retMain->setParent(mainSubG);

        auto* fooSubG = PS.createSubgraph(entryFoo);
        entryFoo->setParent(fooSubG);
        alloc->setParent(fooSubG);
        loadFoo->setParent(fooSubG);
        retFoo->setParent(fooSubG);

        loadFoo->addPointsTo(alloc, 0);
        loadMain->addPointsTo(alloc, 0);

        InvalidatedAnalysis IA(&PS);
        IA.run();

        St* ldFoo = IA.getState(loadFoo);
        St* ldMain = IA.getState(loadMain);

        check(!ldFoo->mustContains(alloc), "[locInv_basic_may] Load's mustBeInv cannot contain 'alloc*'\n");
        check(!ldFoo->mayContains(alloc), "[locInv_basic_may] Load's mayBeInv cannot contain 'alloc*'\n");
        check(!ldMain->mustContains(alloc), "[locInv_basic_may] Load's mustBeInv cannot contain 'alloc*'\n");
        check(ldMain->mayContains(alloc), "[locInv_basic_may] Load's mayBeInv cannot contain 'alloc*'\n");

        check(loadFoo->doesPointsTo(alloc), "[locInv_basic_may] Load does not point to 'alloc'\n");
        check(!loadFoo->doesPointsTo(INVALIDATED), "[locInv_basic_may] Load cannot point to INV\n");
        check(loadMain->doesPointsTo(alloc), "[locInv_basic_may] Load does not point to alloc\n");
        check(loadMain->doesPointsTo(INVALIDATED), "[locInv_basic_may] Load does not point to INV\n");

    }


    void glob_valid() {
        /*
                 [entryMain]                   [glob X = 42]
                      |
                   [call]
                         \
                         [entryFoo]
                             |
                          [alloc]
                             |
                          [store]
                             |
                          [retFoo]
                           /
                 [callRet]
                     |
                  [load]
                     |
                 [retMain]
         */
    }

    void glob_basic_inv() {
        using namespace analysis;
        PointerGraph PS;
        /*
                 [entryMain]                   [global PTR*]
                      |
                   [call]
                         \
                         [entryFoo]
                             |
                          [alloc int] // int x;
                             |
                          [store]     // PTR = &x;
                             |
                          [retFoo]
                           /
                 [callRet]
                     |
                  [load]              // load *PTR
                     |
                 [retMain]

         */

        PSNodeAlloc* global = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        global->setIsGlobal();
        global->setParent(nullptr);
        global->addPointsTo(global, 0);

        PSNodeEntry* entryMain = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeCall* call = PSNodeCall::cast(PS.create(PSNodeType::CALL));
        PSNodeEntry* entryFoo = PSNodeEntry::cast(PS.create(PSNodeType::ENTRY));
        PSNodeAlloc* alloc = PSNodeAlloc::cast(PS.create(PSNodeType::ALLOC));
        PSNode* store = PS.create(PSNodeType::STORE, alloc, global);
        PSNode* loadFoo = PS.create(PSNodeType::LOAD, global);
        PSNodeRet* retFoo = PSNodeRet::get(PS.create(PSNodeType::RETURN, entryFoo));
        PSNodeCallRet* callRet = PSNodeCallRet::cast(PS.create(PSNodeType::CALL_RETURN, call));
        PSNode* loadMain = PS.create(PSNodeType::LOAD, global);
        PSNode* retMain = PSNodeRet::get(PS.create(PSNodeType::RETURN, entryMain));

        entryMain->addSuccessor(call);
        call->addSuccessor(callRet);
        callRet->addSuccessor(retMain);

        entryFoo->addSuccessor(alloc);
        alloc->addSuccessor(store);
        store->addSuccessor(loadFoo);
        loadFoo->addSuccessor(retFoo);

        call->addOperand(callRet);
        callRet->addOperand(retFoo);
        callRet->addReturn(retFoo);

        auto* mainSubG = PS.createSubgraph(entryMain);
        auto* fooSubG = PS.createSubgraph(entryFoo);

        entryMain->setParent(mainSubG);
        call->setParent(mainSubG);
        callRet->setParent(mainSubG);
        loadMain->setParent(mainSubG);
        retMain->setParent(mainSubG);

        entryFoo->setParent(fooSubG);
        alloc->setParent(fooSubG);
        store->setParent(fooSubG);
        loadFoo->setParent(fooSubG);
        retFoo->setParent(fooSubG);

        loadFoo->addPointsTo(global, 0);
        loadMain->addPointsTo(global, 0);

        global->addOperand(alloc);

        InvalidatedAnalysis IA(&PS);
        IA.run();

        St* ldFoo = IA.getState(loadFoo);
        St* ldMain = IA.getState(loadMain);

        // TODO: find out / ask: how to store an address to pointer variable?

        check(!ldFoo->mustContains(global), "[glob_basic_inv] load cannot contain global in must set\n");
        check(!ldFoo->mayContains(global), "[glob_basic_inv] load cannot contain global in may set\n");
        check(ldMain->mustContains(alloc), "[glob_basic_inv] load must contain global in must set\n");
        check(!ldMain->mustContains(global), "[glob_basic_inv] load cannot contain global in may set\n");

        check(!loadFoo->doesPointsTo(INVALIDATED), "[glob_basic_inv] loadFoo cannot point to INV\n");
        check(loadMain->doesPointsTo(INVALIDATED), "[glob_basic_inv] loadMain must point to INV\n");

    }


    void test() {
        memLeak_basic_must();
        memLeak_basic_may();

        memLeak_must1();
        memLeak_may1();

        locInv_basic_must();
        locInv_basic_may();

        glob_basic_inv();
    }
};

}; // namespace tests
}; // namespace dg

int main(void)
{
    using namespace dg::tests;
    TestRunner Runner;

    //Runner.add(new FlowInsensitivePointsToTest());
    //Runner.add(new FlowSensitivePointsToTest());
    //Runner.add(new PSNodeTest());
    Runner.add(new InvalidatedAnalysisTest("Invalidated analysis test"));
    return Runner();
}

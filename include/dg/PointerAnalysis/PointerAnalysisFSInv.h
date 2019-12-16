#ifndef DG_ANALYSIS_POINTS_TO_WITH_INVALIDATE_H_
#define DG_ANALYSIS_POINTS_TO_WITH_INVALIDATE_H_

#include <cassert>
#include "PointerAnalysisFS.h"
#include "InvalidatedAnalysis.h"

namespace dg {
namespace pta {

class PointerAnalysisFSInv : public PointerAnalysisFS
{
public:
    using MemoryMapT = PointerAnalysisFS::MemoryMapT;

    // this is an easy but not very efficient implementation,
    // works for testing
    PointerAnalysisFSInv(PointerGraph *ps,
                           PointerAnalysisOptions opts)
    : PointerAnalysisFS(ps, opts.setInvalidateNodes(true)) {}

    // default options
    PointerAnalysisFSInv(PointerGraph *ps) : PointerAnalysisFSInv(ps, {}) {}

    bool run() override {
        PointerAnalysisFS::run();
        InvalidatedAnalysis IA(getPG());
        return IA.run();
    }
};

} // namespace pta
} // namespace dg

#endif


#ifndef _DG_ANALYSIS_POINTS_TO_WITH_INVALIDATE_H_
#define _DG_ANALYSIS_POINTS_TO_WITH_INVALIDATE_H_

#include <cassert>
#include "PointerAnalysisFS.h"
#include "InvalidatedAnalysis.h"

namespace dg {
namespace analysis {
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

    void run() override {
        PointerAnalysisFS::run();
        InvalidatedAnalysis IA(getPS());
        IA.run();
    }
};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_ANALYSIS_POINTS_TO_WITH_INVALIDATE_H_


#ifndef _DG_INVALIDATED_ANALYSIS_H_
#define _DG_INVALIDATED_ANALYSIS_H_

#include <set>
#include "PointerSubgraph.h"
#include "PSNode.h"

namespace dg {
namespace analysis {
namespace pta {

class InvalidatedAnalysis {
    using PSNodePtrSet = std::set<PSNode *>;

    struct State {
        PSNodePtrSet mustBeInv{};
        PSNodePtrSet mayBeInv{};
        /*
        std::set<PSNode *> mustBeNull;
        std::set<PSNode *> cannotBeNull;
        */

        // node is changed when its State has been updated
        bool update(State* predState) {
            unsigned mustSizeBefore = mustBeInv.size();
            unsigned maySizeBefore = mayBeInv.size();

            // MUST: intersection
            PSNodePtrSet tmp;
            std::set_intersection(mustBeInv.begin(), mustBeInv.end(),
                    predState->mustBeInv.begin(), predState->mustBeInv.end(),
                    std::inserter(tmp, tmp.end()));
            std::swap(tmp, mustBeInv);

            // MAY: union
            mayBeInv.insert(predState->mayBeInv.begin(), predState->mayBeInv.end());

            return mustSizeBefore != mustBeInv.size() || maySizeBefore != mayBeInv.size();
        }
    };

    PointerSubgraph* PS { nullptr };

    // mapping from PSNode's ID to States
    std::vector<State *> _mapping;
    std::vector<std::unique_ptr<State>> _states;

    static inline bool isRelevantNode(PSNode *node) {
        return node->getType() == PSNodeType::STORE ||
               node->getType() == PSNodeType::ALLOC ||
               node->getType() == PSNodeType::DYN_ALLOC ||
               node->getType() == PSNodeType::FREE;
               /* || node->getType() == PSNodeType::INVALIDATE_LOCALS ||
               node->getType() == PSNodeType::INVALIDATE_OBJECT;*/
    }

    // Added temporarily. ( Currently I am focused only on FREE instruction. )
    static inline bool isFreeType(PSNode *node) {
        return node->getType() == PSNodeType::FREE;
    }

    static inline bool noChange(PSNode *node) {
        return node->predecessorsNum() == 1 &&
                !isRelevantNode(node);
    }

    // crates new State in _states and creates a pointer to it in _mapping
    State *newState(PSNode *nd) {
        assert(nd->getID() < _mapping.size());

        _states.emplace_back(new State());
        auto state = _states.back().get();
        _mapping[nd->getID()] = state;

        return state;
    }

    State *getState(PSNode *nd) {
        assert(nd->getID() < _mapping.size());
        return _mapping[nd->getID()];
    }

    static inline bool changesState(PSNode *node) {
        return node->predecessorsNum() == 0 ||
               node->predecessorsNum() > 1 ||
               isRelevantNode(node);
    }

    // at the moment this method is not optimal. It will be useful later.
    bool decideMustOrMay(PSNode* node, PSNode* target) {
        size_t pointsToSize = node->pointsTo.size();
        bool changed = false;
        if (pointsToSize == 1) {
            // must
            getState(node)->mustBeInv.insert(target);
        } else if (pointsToSize > 1) {
            // may
            getState(node)->mayBeInv.insert(target);
        }
        return changed;
    }

    bool processNode(PSNode *node) {
        assert(node);
        assert(node->getID() < _states.size());
        // if node has not changed -> node now shares a state with its predecessor
        if (noChange(node)) {
            auto pred = node->getSinglePredecessor();
            assert(pred->getID() <_states.size());

            _mapping[node->getID()] = getState(pred);
            return false;
        }

        // no need to create new states when we initialize states, mapping in constructor
        // if (changesState(node) && !getState(node)) { newState(node); }
        bool changed = false;

        for (PSNode* pred : node->getPredecessors()) {
            changed |= getState(node)->update(getState(pred));
        }

        if (isFreeType(node)) {
            for (const auto& ptrStruct : node->pointsTo) {
                changed |= decideMustOrMay(node, ptrStruct.target);
            }
        }
        return changed;
    }

public:

    explicit InvalidatedAnalysis(PointerSubgraph *ps)
    : PS(ps), _mapping(ps->size()), _states(ps->size()) {
        for (size_t i = 0; i < ps->size(); ++i) {
            _mapping[i] = _states[i].get();
        }
    }

    void run() {
        std::vector<PSNode *> to_process;
        std::vector<PSNode *> changed;

        // node[0] is null so indices of nodes correspond to their IDs
        for (auto& nd : PS->getNodes()) {
            to_process.push_back(nd.get());
        }

        while(!to_process.empty()) {
            for (auto* nd : to_process) {
                if (nd && processNode(nd))
                    changed.push_back(nd);
            }
            to_process.swap(changed);
            changed.clear();
        }
    }

};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_INVALIDATED_ANALYSIS_H_
        

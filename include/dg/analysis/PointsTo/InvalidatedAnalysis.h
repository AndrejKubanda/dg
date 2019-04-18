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
    // each set includes all nodes that point to target node on ID-index
    std::vector<std::set<PSNode*>> _targetOrigins;

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

    bool decideMustOrMay(PSNode* node, PSNode* target) {
        // TODO: target decide whether it MUST or MAY be INV
        /*
         * if node is the only node pointing to target -> must be inv
         * if multiple nodes are pointing to target -> may be inv
         * wouldn't it be convenient to get a set of nodes that point to target node for each target node?
         */

        // simplified example :
        if (_targetOrigins[target->getID()].size() == 1) {
            // MUST
        } else {
            // MAY
        }

        return false;
    }

    bool processNode(PSNode *node) {
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

    // initializes a vector of sets of origin nodes that point to a target node on index node.id;
    // TODO: A --> B; B --> C. Are the pointers transitive? Does A --> C now?
    void initializeTargetOrigins() {
        for (auto& ndUptr : PS->getNodes()) {
            for (const auto& ptrStruct : ndUptr->pointsTo) {
                _targetOrigins[ptrStruct.target->getID()].insert(ndUptr.get());
            }
        }
    }

public:

    /// Pointer subGraph with computed pointers
    InvalidatedAnalysis(PointerSubgraph *ps)
    : PS(ps), _states(ps->size()), _mapping(ps->size()) {
        for (size_t i = 0; i < ps->size(); ++i) {
            _mapping[i] = _states[i].get();
        }
        initializeTargetOrigins();

    }

    void run() {
        std::vector<PSNode *> to_process;
        std::vector<PSNode *> changed;
        to_process.resize(PS->size());

        for (auto& nd : PS->getNodes())
            to_process.push_back(nd.get());

        while(!to_process.empty()) {
            for (auto nd : to_process) {
                if (processNode(nd))
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
        

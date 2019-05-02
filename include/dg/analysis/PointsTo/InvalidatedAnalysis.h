#ifndef _DG_INVALIDATED_ANALYSIS_H_
#define _DG_INVALIDATED_ANALYSIS_H_

#include <set>
#include "PointerSubgraph.h"
#include "PSNode.h"
#include <algorithm>
#include <memory>
#include <sstream>

namespace dg {
namespace analysis {
namespace pta {

class InvalidatedAnalysis {
#define debugPrint 0

    using PSNodePtrSet = std::set<PSNode *>;

    struct State {
        PSNodePtrSet mustBeInv{};
        PSNodePtrSet mayBeInv{};
        /*
        std::set<PSNode *> mustBeNull;
        std::set<PSNode *> cannotBeNull;
        */

        State() = default;

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

        std::string _tmpStateToString() {
            std::stringstream ss;

            ss << "MUST: { ";
            bool delim = false;
            for (auto& item : mustBeInv) {
                if (delim) { ss << ", "; }
                ss << '<' << item->getID() << '>';
                delim = true;
            }
            ss << " }\n";

            ss << "MAY : { ";
            delim = false;
            for (auto& item : mayBeInv) {
                if (delim) { ss << ", "; }
                ss << '<' << item->getID() << '>';
                delim = true;
            }
            ss << " }";
            return ss.str();
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
        assert(nd && nd->getID() < _mapping.size());
        return _mapping[nd->getID()];
    }

    static inline bool changesState(PSNode *node) {
        return node->predecessorsNum() == 0 ||
               node->predecessorsNum() > 1 ||
               isRelevantNode(node);
    }

    // at the moment this method is not optimal. It will be useful later.
    bool decideMustOrMay(PSNode* node, PSNode* target) {
#if debugPrint
        std::cout << "[DECIDE]\n";
#endif
        size_t pointsToSize = node->pointsTo.size();
        bool changed = false;
        if (pointsToSize == 1) {
            // must
            getState(node)->mustBeInv.insert(target);
        } else if (pointsToSize > 1) {
            // may
            getState(node)->mayBeInv.insert(target);
        }
#if debugPrint
        std::cout << "[inserted target " << target->getID() << "]\n";
#endif
        return changed;
    }

    bool processNode(PSNode *node) {
        assert(node && node->getID() < _states.size());

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
            if (pred)
                changed |= getState(node)->update(getState(pred));
        }

        if (isFreeType(node)) {
#if debugPrint
            std::cout << "[" << node->getID() <<" is FREE]\n";
#endif
            for (const auto& ptrStruct : node->pointsTo) {
#if debugPrint
                std::cout << "[points to: " << ptrStruct.target->getID() << "]\n";
#endif
                changed |= decideMustOrMay(node, ptrStruct.target);
            }
        }
        return changed;
    }

    std::string _tmpStatesToString() {
        std::stringstream ss;
        for (auto& nd : PS->getNodes()) {
            if (!nd) { continue; }
            State* st = getState(nd.get());
            ss << '<' << nd->getID() << ">\n"
                << st->_tmpStateToString() << "\n\n";
        }
        return ss.str();
    }

public:

    explicit InvalidatedAnalysis(PointerSubgraph *ps)
    : PS(ps), _mapping(ps->size()), _states(ps->size()) {
        for (size_t i = 1; i < ps->size(); ++i) {
            _states[i] = llvm::make_unique<State>(); // why llvm:: instead of std:: ???
            _mapping[i] = _states[i].get();
        }
        for (size_t i = 1; i < ps->size(); ++i) {
            assert(_states[i] != nullptr);
            assert(_mapping[i] != nullptr);
        }
    }

    void run() {
        std::vector<PSNode *> to_process;
        std::vector<PSNode *> changed;

        // at [0] is uptr to nullptr
        for (auto& nd : PS->getNodes()) {
            if (nd)
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
#if debugPrint
        std::cout << _tmpStatesToString() << '\n';
#endif
    }

};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_INVALIDATED_ANALYSIS_H_
        

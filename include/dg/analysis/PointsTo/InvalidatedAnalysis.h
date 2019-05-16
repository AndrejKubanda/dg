#ifndef _DG_INVALIDATED_ANALYSIS_H_
#define _DG_INVALIDATED_ANALYSIS_H_

#include <set>
#include "PointerSubgraph.h"
#include "PSNode.h"
#include <algorithm>
#include <memory>
#include <sstream>
#include <fstream>

namespace dg {
namespace analysis {
namespace pta {

class InvalidatedAnalysis {
#define debugPrint 1

    std::ofstream ofs = std::ofstream("invOutput");

    using PSNodePtrSet = std::set<PSNode *>;

    struct State {
        PSNodePtrSet mustBeInv{};
        PSNodePtrSet mayBeInv{};
        /*
        std::set<PSNode *> mustBeNull;
        std::set<PSNode *> cannotBeNull;
        */

        State() = default;
        State(PSNodePtrSet must, PSNodePtrSet may) : mustBeInv(std::move(must)), mayBeInv(std::move(may)) {}

        bool empty() {
            return mustBeInv.empty() && mayBeInv.empty();
        }

        bool update(State* predState) {
            unsigned mustSizeBefore = mustBeInv.size();
            unsigned maySizeBefore = mayBeInv.size();

            // 1.) copy sets to a new tmp node
            State copy (mustBeInv, mayBeInv);

            // 2.) update node's state
            // MUST: intersection
            PSNodePtrSet tmp;
            std::set_intersection(mustBeInv.begin(), mustBeInv.end(),
                    predState->mustBeInv.begin(), predState->mustBeInv.end(),
                    std::inserter(tmp, tmp.end()));
            std::swap(tmp, mustBeInv);

            // MAY: union
            mayBeInv.insert(predState->mayBeInv.begin(), predState->mayBeInv.end());

            // 3.) add (union) copy sets to node's state's set
            mustBeInv.insert(copy.mustBeInv.begin(), copy.mustBeInv.end());
            mayBeInv.insert(copy.mayBeInv.begin(), copy.mayBeInv.end());

            // return true if sizes of sets have changed
            return mustSizeBefore != mustBeInv.size() || maySizeBefore != mayBeInv.size();
        }

        std::string _tmpStateToString() const {
            std::stringstream ss;

            ss << "MUST: { ";
            bool delim = false;
            for (auto& item : mustBeInv) {
                if (delim) { ss << ", "; }
                ss << item->getID();
                delim = true;
            }
            ss << " }\n";

            ss << "MAY : { ";
            delim = false;
            for (auto& item : mayBeInv) {
                if (delim) { ss << ", "; }
                ss << item->getID();
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
        return /*node->getType() == PSNodeType::STORE ||*/
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

    const State *getState(PSNode *nd) const {
        assert(nd && nd->getID() < _mapping.size());
        return _mapping[nd->getID()];
    }

    static inline bool changesState(PSNode *node) {
        return node->predecessorsNum() == 0 ||
               node->predecessorsNum() > 1 ||
               isRelevantNode(node);
    }


    bool decideMustOrMay(PSNode* node, PSNode* target) {

        if (debugPrint) ofs << "[must or may]\n";

        State* state = getState(node);
        size_t mustSize = state->mustBeInv.size();
        size_t maySize = state->mayBeInv.size();
        size_t pointsToSize = node->getOperand(0)->pointsTo.size();

        if (pointsToSize == 1) {
            state->mustBeInv.insert(target);
        } else if (pointsToSize > 1) {
            state->mayBeInv.insert(target);
        }
        if (debugPrint) ofs << "[inserted target " << target->getID() << "]\n";

        return mustSize != state->mustBeInv.size() || maySize != state->mayBeInv.size();
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

        bool changed = false;

        if (isFreeType(node)) {
            if (debugPrint) ofs << "[" << node->getID() <<" is FREE]\n";
            for (const auto& ptrStruct : node->getOperand(0)->pointsTo) { // we want .getOperand(0) - zero-th operand's points to set
                if (debugPrint) ofs << "[points to: " << ptrStruct.target->getID() << "]\n";
                changed |= decideMustOrMay(node, ptrStruct.target);
            }
        }

        for (PSNode* pred : node->getPredecessors()) {
            if (pred)
                changed |= getState(node)->update(getState(pred));
        }

        return changed;
    }

    std::string _tmpPointsToString(const PSNode* node) const {
        std::stringstream ss;
        bool delim = false;

        ss << "  pointsTo: { ";
        for (const auto& item : node->pointsTo) {
            if (delim) { ss << ", "; }
            ss << item.target->getID();
            delim = true;
        }
        ss << " }\n";

        for (size_t i = 0; i < node->getOperandsNum(); ++i) {
            ss << "  op[" << i << "] ptsTo: { ";
            delim = false;
            for (const auto& item : node->getOperand(i)->pointsTo) {
                if (delim) { ss << ", "; }
                ss << item.target->getID();
                delim = true;
            }
            ss << " }\n";
        }
        return ss.str();
    }

    std::string _tmpStatesToString() const {
        std::stringstream ss;
        for (auto& nd : PS->getNodes()) {
            if (!nd) { continue; }
            const State* st = getState(nd.get());
            ss << '<' << nd->getID() << ">\n"
                << st->_tmpStateToString() << "\n"
                << _tmpPointsToString(nd.get()) << "\n";
        }
        return ss.str();
    }

    bool fixMust(PSNode* nd) {
        if (getState(nd)->empty())
            return false;

        bool changed = false;

        auto* pointsTo = &nd->pointsTo;

        if (isFreeType(nd))
            pointsTo = &nd->getOperand(0)->pointsTo;

        for (PSNode* target : getState(nd)->mustBeInv) {
            ofs << "(must)<" << nd->getID() << ">:fixing pointsTo for target<" << target->getID() << ">\n";
            if (pointsTo->pointsToTarget(target)) {
                changed |= pointsTo->removeAny(target);
                ofs << "<" << target->getID() << "> removed from pointsTo set\n";
            }
        }

        return changed;
    }

    bool fixMay(PSNode* nd) {
        if (getState(nd)->empty())
            return false;

        auto* pointsTo = &nd->pointsTo;
        if (isFreeType(nd))
            pointsTo = &nd->getOperand(0)->pointsTo;

        for (PSNode* target : getState(nd)->mayBeInv) {
            ofs << "(may)<" << nd->getID() << ">:fixing pointsTo for target<" << target->getID() << ">\n";
            if (pointsTo->pointsToTarget(target)) {
                ofs << "(may)<" << nd->getID() << ">: target<" << target->getID() << "> found\n";
                return true;
            }
        }
        return false;
    };

    void fixPointsTo(PSNode* nd) {
        if (fixMust(nd) || fixMay(nd)) {
            ofs << "[ INV inserted into <" << nd->getID() << ">'s pointsTo set]\n";
            nd->pointsTo.add(INVALIDATED);
        }
    }

public:

    explicit InvalidatedAnalysis(PointerSubgraph *ps)
    : PS(ps), _mapping(ps->size()), _states(ps->size()) {
        for (size_t i = 1; i < ps->size(); ++i) {
            _states[i] = llvm::make_unique<State>();
            _mapping[i] = _states[i].get();
        }
    }

    void run() {
        std::vector<PSNode *> to_process;
        std::vector<PSNode *> changed;

        // [0] is nullptr
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
        if (debugPrint) ofs << _tmpStatesToString() << '\n';
        /*for (auto& nd : PS->getNodes()) {
            if (nd) fixPointsTo(nd.get());
        }*/
    }

};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_INVALIDATED_ANALYSIS_H_
        
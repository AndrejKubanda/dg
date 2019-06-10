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
        //friend class InvalidatedAnalysis;
        PSNodePtrSet mustBeInv{};
        PSNodePtrSet mayBeInv{};
        /*
        std::set<PSNode *> mustBeNull;
        std::set<PSNode *> cannotBeNull;
        */

        State() = default;
        State(PSNodePtrSet must, PSNodePtrSet may) : mustBeInv(std::move(must)), mayBeInv(std::move(may)) {}

        bool operator==(const State& other) {
            return mustBeInv == other.mustBeInv && mayBeInv == other.mayBeInv;
        }

        bool operator!=(const State& other) {
            return !(*this == other);
        }

        bool empty() {
            return mustBeInv.empty() && mayBeInv.empty();
        }

        /*
        bool update(State* predState) {
            unsigned mustSizeBefore = mustBeInv.size();
            unsigned maySizeBefore = mayBeInv.size();
            // 1.) copy sets to a new tmp State
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
        */

        bool insertIntoSets(const PSNodePtrSet& mustSet, const PSNodePtrSet& maySet) {
            unsigned mustSize = mustBeInv.size();
            unsigned maySize = mayBeInv.size();
            mustBeInv.insert(mustSet.begin(), mustSet.end());
            mayBeInv.insert(maySet.begin(), maySet.end());
            return mustSize != mustBeInv.size() || maySize != mayBeInv.size();
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

        /**
         *  Returns wheter State sets have changed.
         */
        bool updateState(const std::vector<PSNode*>& predecessors, InvalidatedAnalysis* invAn) {
            State stateBefore = *this;
            PSNodePtrSet predMust = absIntersection(predecessors, invAn);
            mustBeInv.insert(predMust.begin(), predMust.end()); // MUST OK

            PSNodePtrSet predAbsUnion = absUnion(predecessors, invAn);
            predAbsUnion.insert(mayBeInv.begin(), mayBeInv.end()); // predUnion + mayBeInv
            PSNodePtrSet tmp;
            std::set_difference(predAbsUnion.begin(), predAbsUnion.end(), mustBeInv.begin(), mustBeInv.end(),
                    std::inserter(tmp, tmp.begin())); // {predUnion + mayBeInv} - {mustBeInv}
            std::swap(tmp, mayBeInv);
            return *this != stateBefore;
        }

    private:
        static PSNodePtrSet absUnion(const std::vector<PSNode*>& predecessors, InvalidatedAnalysis* invAn) {
            PSNodePtrSet result;
            if (predecessors.empty())
                return result;

            PSNodePtrSet* mustSet;
            PSNodePtrSet* maySet;

            for (auto* pred : predecessors) {
                mustSet = &invAn->getState(pred)->mustBeInv;
                maySet = &invAn->getState(pred)->mayBeInv;
                result.insert(mustSet->begin(), mustSet->end());
                result.insert(maySet->begin(), maySet->end());
            }
            return result;
        }

        static PSNodePtrSet absIntersection(const std::vector<PSNode*>& predecessors, InvalidatedAnalysis* invAn) {
            PSNodePtrSet result;
            if (predecessors.empty())
                return result;

            State* st = invAn->getState(predecessors.at(0));
            result.insert(st->mustBeInv.begin(), st->mustBeInv.end());
            PSNodePtrSet tmp;

            for (auto it = ++(predecessors.begin()); it != predecessors.end(); ++it) {
                st = invAn->getState(*it);
                std::set_intersection(result.begin(), result.end(), st->mustBeInv.begin(), st->mustBeInv.end(), std::inserter(tmp, tmp.begin()));
                std::swap(result, tmp);
                tmp.clear();
            }

            return result;
        }
    };

    PointerSubgraph* PS { nullptr };

    // mapping from PSNode's ID to States
    std::vector<State *> _mapping;
    std::vector<std::unique_ptr<State>> _states;

    static inline bool isRelevantNode(PSNode *node) {
        return node->getType() == PSNodeType::ALLOC ||
               node->getType() == PSNodeType::DYN_ALLOC ||
               node->getType() == PSNodeType::FREE;
               /* || node->getType() == PSNodeType::INVALIDATE_LOCALS ||
               node->getType() == PSNodeType::INVALIDATE_OBJECT;*/
    }

    static inline bool isFreeType(const PSNode *node) {
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
        // if (debugPrint) ofs << "[must or may]\n";
        State* state = getState(node);
        size_t mustSize = state->mustBeInv.size();
        size_t maySize = state->mayBeInv.size();
        size_t pointsToSize = node->getOperand(0)->pointsTo.size();

        if (pointsToSize == 1) {
            state->mustBeInv.insert(target);
        } else if (pointsToSize > 1) {
            state->mayBeInv.insert(target);
        }
        // if (debugPrint) ofs << "[inserted target " << target->getID() << "]\n";

        return mustSize != state->mustBeInv.size() || maySize != state->mayBeInv.size();
    }

    bool processNode(PSNode *node) {
        assert(node && node->getID() < _states.size());

        if (noChange(node)) {
            auto pred = node->getSinglePredecessor();
            assert(pred->getID() <_states.size());

            _mapping[node->getID()] = getState(pred);
            return false;
        }

        bool changed = false;

        if (isFreeType(node)) {
            for (const auto& ptrStruct : node->getOperand(0)->pointsTo) {
                changed |= decideMustOrMay(node, ptrStruct.target);
            }
        }

        changed |= getState(node)->updateState(node->getPredecessors(), this);

        if (changed) ofs << "changed: " << node->getID() << "\n";
        return changed;
    }

    std::string _tmpPointsToToString(const PSNode *node) const {
        std::stringstream ss;
        bool delim = false;
        if (isFreeType(node))
            ss << "[FREE] ";
        ss << "pointsTo: { ";
        for (const auto& item : node->pointsTo) {
            if (delim) { ss << ", "; }
            ss << item.target->getID();
            delim = true;
        }
        ss << " }\n";
        return ss.str();
    }

    std::string _tmpStatesToString() const {
        std::stringstream ss;
        for (auto& nd : PS->getNodes()) {
            if (!nd)
                continue;
            const State* st = getState(nd.get());
            ss << '<' << nd->getID() << "> " << _tmpPointsToToString(nd.get()) << '\n'
                << st->_tmpStateToString() << "\n\n";
        }
        return ss.str();
    }

    bool fixMust(PSNode* nd) {
        bool changed = false;
        auto& pointsTo = nd->pointsTo;

        for (PSNode* target : getState(nd)->mustBeInv) {
            ofs << "(must)<" << nd->getID() << ">:fixing pointsTo for target<" << target->getID() << ">\n";
            if (pointsTo.pointsToTarget(target)) {
                changed |= pointsTo.removeAny(target);
                ofs << "<" << target->getID() << "> removed from pointsTo set\n";
            }
        }

        return changed;
    }

    bool fixMay(PSNode* nd) {
        auto& pointsTo = nd->pointsTo;

        for (PSNode* target : getState(nd)->mayBeInv) {
            ofs << "(may)<" << nd->getID() << ">:fixing pointsTo for target<" << target->getID() << ">\n";
            if (pointsTo.pointsToTarget(target)) {
                ofs << "(may)<" << nd->getID() << ">: target<" << target->getID() << "> found\n";
                return true;
            }
        }
        return false;
    };

    void fixPointsTo(PSNode* nd) {
        if (getState(nd)->empty()) {
            //ofs << "<" << nd->getID() << "> has empty State\n";
            return;
        }

        // multiple steps to avoid lazy evaluation.
        bool insertINV = fixMust(nd);
        insertINV |= fixMay(nd);
        if (insertINV) {
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
        /*
         * new way. To solve the situation when nd 33 with preds 32, 39 doesnt receive correct MUST set intersection
         * of predecessors because 39 has not been processed yet.
         */
        /*
        bool hasChanged = true;
        // major change to algorithm, much less efficient.
        // Is there a way how to keep the efficience of the previous approach
        while (hasChanged) {
            hasChanged = false;
            for (auto& uptrNd : PS->getNodes()) {
                if (uptrNd)
                    hasChanged |= processNode(uptrNd.get());
            }
        }
        */

        // /*
        // old way
        std::vector<PSNode *> to_process;
        std::vector<PSNode *> changed;

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
        // */

        if (debugPrint) ofs << _tmpStatesToString() << '\n';
        for (auto& nd : PS->getNodes()) {
            if (nd) fixPointsTo(nd.get());
        }
    }
};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_INVALIDATED_ANALYSIS_H_
        

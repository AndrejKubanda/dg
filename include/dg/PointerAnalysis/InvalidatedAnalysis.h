#ifndef _DG_INVALIDATED_ANALYSIS_H_
#define _DG_INVALIDATED_ANALYSIS_H_

#include <set>
#include "PointerGraph.h"
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

    //TODO: invalidate locals: nd->getParent() - returns parent function, porovnam vsetky allocy s RETURN node-om a zistim
    //TODO: simple testing: points-to-test.cpp
    //TODO: fix cycling in updateStateTest.c
    //TODO: fix: local inv is not yet implemented, though somehow it works in some cases, without printing that INV has been inserted into PointsTo

    std::ofstream ofs = std::ofstream("invOutput");

    size_t numOfProcessedNodes = 0;

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

        bool operator==(const State& other) {
            return mustBeInv == other.mustBeInv && mayBeInv == other.mayBeInv;
        }

        bool operator!=(const State& other) {
            return !(*this == other);
        }

        bool empty() {
            return mustBeInv.empty() && mayBeInv.empty();
        }

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
         *  Returns whether State sets have changed.
         */
        bool updateState(const std::vector<PSNode*>& predecessors, InvalidatedAnalysis* IA) {
            //std::cout << "(updating state) ";
            State stateBefore = *this;
            PSNodePtrSet predMust = absIntersection(predecessors, IA);
            mustBeInv.insert(predMust.begin(), predMust.end());

            PSNodePtrSet predAbsUnion = absUnion(predecessors, IA);
            predAbsUnion.insert(mayBeInv.begin(), mayBeInv.end());
            PSNodePtrSet tmp;
            std::set_difference(predAbsUnion.begin(), predAbsUnion.end(), mustBeInv.begin(), mustBeInv.end(),
                    std::inserter(tmp, tmp.begin())); // {predUnion + mayBeInv} - {mustBeInv}
            std::swap(tmp, mayBeInv);
            return *this != stateBefore;
        }

    private:
        static PSNodePtrSet absUnion(const std::vector<PSNode*>& predecessors, InvalidatedAnalysis* IA) {
            PSNodePtrSet result;
            if (predecessors.empty())
                return result;

            PSNodePtrSet* mustSet;
            PSNodePtrSet* maySet;

            for (auto* pred : predecessors) {
                mustSet = &IA->getState(pred)->mustBeInv;
                maySet = &IA->getState(pred)->mayBeInv;
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

    PointerGraph* PS { nullptr };

    // mapping from PSNode's ID to States
    std::vector<State *> _mapping;
    std::vector<std::unique_ptr<State>> _states;

    static inline bool isRelevantNode(PSNode *node) {
        return node->getType() == PSNodeType::ALLOC ||
               node->getType() == PSNodeType::FREE ||
               node->getType() == PSNodeType::INVALIDATE_LOCALS; /* ||
               node->getType() == PSNodeType::INVALIDATE_OBJECT;*/
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
        numOfProcessedNodes++;

        if (noChange(node)) {
            auto pred = node->getSinglePredecessor();
            assert(pred->getID() <_states.size());

            _mapping[node->getID()] = getState(pred);
            return false;
        }

        bool changed = false;

        if (isa<PSNodeType::FREE>(node)) {
            for (const auto& ptrStruct : node->getOperand(0)->pointsTo) {
                changed |= decideMustOrMay(node, ptrStruct.target);
            }
        }

        //std::cout << "node: " << node->getID();
        changed |= getState(node)->updateState(node->getPredecessors(), this);
        //std::cout << "  " << changed << '\n';
        return changed;
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
        if (getState(nd)->empty())
            return;

        // multiple steps to avoid lazy evaluation.
        bool insertINV = fixMust(nd);
        insertINV |= fixMay(nd);
        if (insertINV) {
            ofs << "[ INV inserted into <" << nd->getID() << ">'s pointsTo set]\n";
            nd->addPointsTo(INVALIDATED, 0);
        }
    }

    std::string _tmpPointsToToString(const PSNode *node) const {
        std::stringstream ss;
        bool delim = false;
        if (isa<PSNodeType::FREE>(const_cast<PSNode*>(node)))
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

public:

    explicit InvalidatedAnalysis(PointerGraph *ps)
    : PS(ps), _mapping(ps->size()), _states(ps->size()) {
        for (size_t i = 1; i < ps->size(); ++i) {
            _states[i] = llvm::make_unique<State>();
            _mapping[i] = _states[i].get();
        }
    }

    bool run() {
        std::vector<PSNode *> to_process;
        std::vector<PSNode *> changed;

        for (auto& nd : PS->getNodes()) {
            if (nd)
                to_process.push_back(nd.get());
        }

        while(!to_process.empty()) {
            for (auto* nd : to_process) {
                if (nd && processNode(nd)) {
                    auto reachable = PS->getNodes(nd);
                    if (debugPrint) {
                        ofs << "changed: " << nd->getID() << " (reachables ";
                        for (auto node : reachable) {
                            ofs << node->getID() << " ";
                        }
                        ofs << ")\n";
                    }
                    if (nd->getID() == /*38*/41 || nd->getID() == /*84*/42) {
                        //std::cout << " " << nd->getID() << " " << reachable.size() << '\n';
                    }
                    changed.insert(changed.end(), reachable.begin(), reachable.end());
                }
            }
            to_process.swap(changed);
            changed.clear();
        }

        if (debugPrint) ofs << "processed: " << numOfProcessedNodes << "\n\n" << _tmpStatesToString() << '\n';

        for (auto& nd : PS->getNodes()) {
            if (nd) fixPointsTo(nd.get());
        }
	return true;
    }
};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_INVALIDATED_ANALYSIS_H_
        

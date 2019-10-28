#ifndef _DG_INVALIDATED_ANALYSIS_H_
#define _DG_INVALIDATED_ANALYSIS_H_

#include <set>
#include "PointerGraph.h"
#include "PSNode.h"
#include <algorithm>
#include <memory>
#include <sstream>
#include <fstream>
#include <llvm/ADT/STLExtras.h>

namespace dg {
namespace analysis {
namespace pta {

#define debugPrint 1
#define testing 1

#if testing
struct InvalidatedAnalysis {
#else
class InvalidatedAnalysis {
#endif

    std::ofstream ofs = std::ofstream("invOutput");

    size_t numOfProcessedNodes = 0;

    using PSNodePtrSet = std::set<PSNode *>;
    using parentsMap = std::map<unsigned, std::set<PSNode*>>;

    struct CallstackNode {
                PSNode* callNode{nullptr};
                CallstackNode* parent{nullptr};
                std::vector<std::unique_ptr<CallstackNode>> children;

                CallstackNode() = default;

                CallstackNode(PSNode* callNd) : callNode(callNd) {}

                CallstackNode(PSNode* callNd, CallstackNode* parentNd) : callNode(callNd), parent(parentNd) {}


                bool empty() const {
                    return callNode == nullptr;
                }

                bool isLeaf() const {
                    return children.empty();
                };

                CallstackNode* hasChild(PSNode* call) const {
                    for (auto& nd : children) {
                        if (call == nd->callNode)
                            return nd.get();
                    }
                    return nullptr;
                }

                // called upon a top node
                // either returns a new pointer or creates new child and returns new top pointer
                CallstackNode* push(PSNode* call) {
                    auto child = hasChild(call);
                    if (!child) {
                        children.emplace_back(llvm::make_unique<CallstackNode>(call, this));
                        return (--children.end())->get();
                    }
                    return child;
                }

                CallstackNode* pop() {
                    if (parent)
                        return parent;
                    return this;
                }

                std::string toString() {
                    std::vector<PSNode*> cont;
                    auto* nd = this;
                    while (nd->callNode) {
                        cont.push_back(nd->callNode);
                        nd = nd->pop();
                    }

                    std::stringstream ss;
                    ss << "callStack {";
                    for (auto n : cont) {
                        ss << n->getID() << ' ';
                    }
                    ss << "-|}";

                    return ss.str();
                }
            };

    using NodeStackPair = std::pair<PSNode*, CallstackNode*>;

    struct State {
        // TODO: [hard] State has info about callStack -> differentiate between local variables
        // sets need to contain pairs <PSNode*, callStack*>
        PSNodePtrSet mustBeInv{};
        PSNodePtrSet mayBeInv{};
        /*
        std::set<PSNode *> mustBeNull;
        std::set<PSNode *> cannotBeNull;
        */

        State() = default;
        State(PSNodePtrSet must, PSNodePtrSet may) : mustBeInv(std::move(must)), mayBeInv(std::move(may)) {}

        bool mustContains(PSNode* target) const {
            auto search = mustBeInv.find(target);
            return search != mustBeInv.end();
        }

        bool mayContains(PSNode* target) const {
            auto search = mayBeInv.find(target);
            return search != mayBeInv.end();
        }

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

        std::string _tmpMustToString() const {
            std::stringstream ss;
            ss << "MUST: { ";
            bool delim = false;
            for (auto& item : mustBeInv) {
                if (delim) { ss << ", "; }
                ss << item->getID();
                delim = true;
            }
            ss << " }";
            return ss.str();
        }

        std::string _tmpMayToString() const {
            std::stringstream ss;
            ss << "MAY: { ";
            bool delim = false;
            for (auto& item : mayBeInv) {
                if (delim) { ss << ", "; }
                ss << item->getID();
                delim = true;
            }
            ss << " }";
            return ss.str();
        }

        std::string _tmpStateToString() const {
            std::stringstream ss;
            ss << "    " << _tmpMustToString() << '\n'
            << "    " << _tmpMayToString() << '\n';
            return ss.str();
        }

        /**
         *  Returns whether State sets have changed.
         */
        bool updateState(const std::vector<PSNode*>& predecessors, InvalidatedAnalysis* IA) {
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

    PointerGraph* PG { nullptr };

    // mapping from PSNode's ID to States
    std::vector<State *> _mapping;
    std::vector<std::unique_ptr<State>> _states;

    static inline bool isRelevantNode(PSNode *node) {
        return node->getType() == PSNodeType::ALLOC ||
               node->getType() == PSNodeType::FREE ||
               node->getType() == PSNodeType::ENTRY ||
               node->getType() == PSNodeType::RETURN;
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

    std::vector<NodeStackPair> initStacks(CallstackNode* stackTop) {
        assert(PG->size() >= 2 && "Why are you even testing a program with (<= 2) nodes?");

        std::vector<NodeStackPair> to_process;
        std::vector<bool> visitTracker(PG->size(), true);
        initNodeStack(PG->getEntry()->getRoot(), stackTop, to_process, visitTracker);
        return to_process;
    }

    void initNodeStack(PSNode* nd, CallstackNode* stackTop, std::vector<NodeStackPair>& to_process, std::vector<bool>& visitTracker) {
        assert(visitTracker.at(nd->getID()) && "Visiting already visited node\n");
        ofs << _tmpNodeStackPairToString({ nd, stackTop }) << '\n';

        to_process.emplace_back(nd, stackTop);
        visitTracker.at(nd->getID()) = false;

        CallstackNode* newTop;

        if (nd->getType() == PSNodeType::CALL /*|| nd->getType() == PSNodeType::CALL_FUNCPTR*/) {
            newTop = stackTop->push(nd);
            for (auto *subG : PSNodeCall::cast(nd)->getCallees()) {
                resetVisitsOfSubG(visitTracker, subG);
                if (visitTracker.at(subG->getRoot()->getID()))
                    initNodeStack(subG->getRoot(), newTop, to_process, visitTracker);
            }
        } else if (nd->getType() == PSNodeType::RETURN) {
            // callStack of main() is empty therefore we cannot pop
            if (nd->getParent()->getID() == 1)
                return;

            PSNode* callee = stackTop->callNode;
            newTop = stackTop->pop();

            for (auto* callRet : PSNodeRet::get(nd)->getReturnSites()) {
                if (callRet == callee->getPairedNode() && visitTracker.at(callRet->getID()))
                    initNodeStack(callRet, newTop, to_process, visitTracker);
            }

        } else {
            for (auto* suc : nd->getSuccessors()) {
                if (visitTracker.at(suc->getID()))
                    initNodeStack(suc, stackTop, to_process, visitTracker);
            }
        }
    }

    bool decideMustOrMay(PSNode* node, PSNode* target) {
        State* state = getState(node);
        size_t mustSize = state->mustBeInv.size();
        size_t maySize = state->mayBeInv.size();
        size_t pointsToSize = node->getOperand(0)->pointsTo.size();

        if (pointsToSize == 1)
            state->mustBeInv.insert(target);
        else if (pointsToSize > 1)
            state->mayBeInv.insert(target);

        return mustSize != state->mustBeInv.size() || maySize != state->mayBeInv.size();
    }

    bool processNode(PSNode *node, parentsMap& parentToLocalsMap) {
        assert(node && node->getID() < _states.size());
        numOfProcessedNodes++;
        ofs << "<" << node->getID() << "> "<< PSNodeTypeToCString(node->getType()) << '\n';
        PSNode _nodeBefore = *node; // debug
        State _stateBefore = *getState(node); // debug

        if (noChange(node)) {
            // TODO: [easy] put outside noChange
            // has to be outside noChange if multiple returns can progress into single CALL_RETURN
            // if more than 1 callRet are possible, then we cannot store the route in stack with single CALL*s
            if (isa<PSNodeType::CALL_RETURN>(node)) {
                auto& returns = PSNodeCallRet::cast(node)->getReturns();
                // TODO: [easy] use only possible call-returns. EDIT: it seems I want this default behavior
                getState(node)->updateState(returns, this);
                return false;
            }

            auto pred = node->getSinglePredecessor();
            assert(pred->getID() <_states.size());
            _mapping[node->getID()] = getState(pred);
            return false;
        }

        bool changed = false;
        auto preds = node->getPredecessors();
        State* st = getState(node);

        if ( auto* alloc = PSNodeAlloc::get(node)) {
            if (!alloc->isHeap() && !alloc->isGlobal()) // not alloc but store node has info about Global var (?)
                parentToLocalsMap.at(node->getParent()->getID()).emplace(node);

        } else if (isa<PSNodeType::FREE>(node)) {
            for (const auto& ptrStruct : node->getOperand(0)->pointsTo)
                changed |= decideMustOrMay(node, ptrStruct.target);

        } else if (auto* entry = PSNodeEntry::get(node)) {
            // TODO: [easy] take predecessors only from the CALL from the top of callstack
            auto& callers = entry->getCallers();
            preds.insert(preds.end(), callers.begin(), callers.end());
            auto search = parentToLocalsMap.find(node->getParent()->getID());
            if (search == parentToLocalsMap.end())
                parentToLocalsMap.emplace(std::pair<unsigned, std::set<PSNode*>>(node->getParent()->getID(), {}));

        } else if (isa<PSNodeType::RETURN>(node)) {
            for (auto& nd : parentToLocalsMap.at(node->getParent()->getID()))
                changed |= st->mustBeInv.emplace(nd).second;
        }

        changed |= getState(node)->updateState(preds, this);

        if (changed)
            ofs << "  hanged: <" << node->getID() << "> " <<  PSNodeTypeToCString(node->getType()) << '\n'
            << _tmpCompareChanges(&_stateBefore, getState(node));

        return changed;
    }

    /*
     * Returns true if pointsToSet points to any target in node's state's mustBeInv.
     * Also removes these targets from node's pointsToSet
     */
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

    /*
     * Returns true if nodes's PointsToSet points to any target in node's mayBeInv
     */
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
        // if pointsToSet already contains INV we dont want to add another one
        if (insertINV && !nd->pointsTo.hasInvalidated()) {
            ofs << "[ INV inserted into <" << nd->getID() << ">'s pointsTo set]\n";
            nd->addPointsTo(INVALIDATED, 0);
        }
    }

    void resetVisitsOfSubG(std::vector<bool>& visitTracker, PointerSubgraph* subG) const {
        auto nodes = getReachableNodes(subG->getRoot(), nullptr, false);
        for (auto* nd : nodes)
            visitTracker.at(nd->getID()) = true;
    }

    std::vector<NodeStackPair> getReachables(NodeStackPair *start) const {
        QueueFIFO<NodeStackPair> fifo;
        std::vector<NodeStackPair> cont;
        std::vector<bool> visitTracker(PG->size(), true);

        auto visit = [&visitTracker](PSNode* nd){ visitTracker.at(nd->getID()) = false; };
        auto visited = [&visitTracker](PSNode* nd){ return !visitTracker.at(nd->getID()); };

        fifo.push(*start);

        while (!fifo.empty()) {
            NodeStackPair cur = fifo.pop();
            if (visited(cur.first))
                continue;

            visit(cur.first);
            cont.push_back(cur);

            if (PSNodeCall* C = PSNodeCall::get(cur.first)) {
                CallstackNode* pushed = cur.second->push(C);
                for (auto subg : C->getCallees()) {
                    resetVisitsOfSubG(visitTracker, subg);
                    // Is this if useles??
                    if (!visited(subg->getRoot()))
                        fifo.push(std::make_pair(subg->getRoot(), pushed));
                }
            } else if (PSNodeRet* R = PSNodeRet::get(cur.first)) {
                if (cur.first->getParent()->getID() == 1)
                    continue;
                PSNode* callee = cur.second->callNode;
                for (auto* callRet : PSNodeRet::get(cur.first)->getReturnSites()) {
                    if (callRet == callee->getPairedNode() && !visited(callee->getPairedNode()))
                        fifo.push(std::make_pair(callRet, cur.second->pop()));
                }
            } else {
                for (auto suc : cur.first->getSuccessors()) {
                    if (!visited(suc)) {
                        fifo.push(std::make_pair(suc, cur.second));
                    }
                }
            }
        }

        return cont;
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
        ss << " }";
        return ss.str();
    }

    std::string _tmpStatesToString() const {
        std::stringstream ss;
        for (auto& nd : PG->getNodes()) {
            if (!nd)
                continue;
            const State* st = getState(nd.get());
            ss << '<' << nd->getID() << "> " << _tmpPointsToToString(nd.get()) << '\n'
               << st->_tmpStateToString() << "\n\n";
        }
        return ss.str();
    }

    std::string _tmpCompareChanges(const State* beforeSt, const State* afterSt) const {
        std::stringstream ss;
        std::string tab = "    ";
        ss << tab << "BEFORE: " << beforeSt->_tmpMustToString() << '\n'
           << tab << "AFTER: " << afterSt->_tmpMustToString() << '\n'
           << tab << "BEFORE: " << beforeSt->_tmpMayToString() << '\n'
           << tab << "AFTER: " << afterSt->_tmpMayToString() << '\n';
        return ss.str();
    }

    std::string _tmpNodeStackPairToString(NodeStackPair pair) const {
        std::stringstream ss;
        ss << '<' << pair.first->getID() << "> " << PSNodeTypeToCString(pair.first->getType())
           << " " << pair.second->toString();
        return ss.str();
    }

public:
    explicit InvalidatedAnalysis(PointerGraph *pg)
    : PG(pg), _mapping(pg->size()), _states(pg->size()) {
        for (size_t i = 1; i < pg->size(); ++i) {
            _states[i] = llvm::make_unique<State>();
            _mapping[i] = _states[i].get();
        }
    }

    void run() {
        CallstackNode root;
        std::vector<NodeStackPair> to_process = initStacks(&root);
        std::vector<NodeStackPair> changed;

        // I could use CallStack to differentiate between local vars in different calls of a function.
        // It wouldn't help with calls from a loop or recursion
        std::map<unsigned, std::set<PSNode*>> parentToLocalsMap;

        /*{
            int i = 0;
            for (auto item : to_process) {
                std::cout << "[i=" << i++ << "] <" << item.first->getID() << "> "
                          << PSNodeTypeToCString(item.first->getType()) << ") "
                          << item.second->toString() << '\n';
            }
            std::cout << '\n';

            unsigned to_processsIdx = 26;
            auto interprocTrueSize = PG->getNodes(to_process.at(to_processsIdx).first);
            auto getReach = getReachables(&to_process.at(to_processsIdx));
            std::vector<unsigned> ids;
            std::cout << to_process.at(to_processsIdx).first->getID() << ' '
                      << to_process.at(to_processsIdx).second->toString() << "\n";
            std::cout << "getNodes (size=" << interprocTrueSize.size() << ")\n";
            for (auto item : interprocTrueSize)
                ids.push_back(item->getID());
            //std::sort(ids.begin(), ids.end());
            for (auto x : ids)
                std::cout << x << ' ';

            ids.clear();
            std::cout << "\n\ngetReachables (size=" << getReach.size() << ")\n";
            for (auto item : getReach)
                ids.push_back(item.first->getID());
            //std::sort(ids.begin(), ids.end());
            for (auto x : ids)
                std::cout << x << ' ';

            std::cout << '\n';
        }*/

        while(!to_process.empty()) {
            for (auto& nodeStackPair : to_process) {
                if (processNode(nodeStackPair.first, parentToLocalsMap)) {
                    auto reachables = getReachables(&nodeStackPair);
                    if (debugPrint) {
                        ofs << "    (reachables ";
                        for (auto& ndStack : reachables) {
                            ofs << ndStack.first->getID() << " ";
                        }
                        ofs << ")\n\n";
                    }
                    changed.insert(changed.end(), reachables.begin(), reachables.end());

                }
            }
            to_process.swap(changed);
            changed.clear();
        }

        if (debugPrint) ofs << "processed: " << numOfProcessedNodes << "\n\n" << _tmpStatesToString() << '\n';

        for (auto& nd : PG->getNodes()) {
            if (nd)
                fixPointsTo(nd.get());
        }
    }
};

} // namespace pta
} // namespace analysis
} // namespace dg

#endif // _DG_INVALIDATED_ANALYSIS_H_
        

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
    using CallStack = std::stack<PSNode*>;
    using NodeStackPair = std::pair<PSNode*, CallStack>;

    struct State {
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

    // TODO: prepare for recursive functions
    static std::vector<unsigned> initVisited(const PointerGraph* PG) {
        std::vector<unsigned> visited (PG->size(), 1u);
        for (auto& subG : PG->getSubgraphs()) {
            unsigned calleesSize = PSNodeEntry::cast(subG->getRoot())->getCallers().size();
            if (calleesSize >= 2)
                for (auto* nd : getReachableNodes(subG->getRoot(), nullptr, false)) {
                    visited.at(nd->getID()) = calleesSize;
                }
        }
        return visited;
    }

    std::vector<NodeStackPair> initStacks(std::vector<unsigned> remainingVisits) {
        assert(PG->size() >= 2 && "Why are you even testing a program with (<= 2) nodes?");

        CallStack callStack;
        std::vector<NodeStackPair> to_process;
        auto visited = std::move(remainingVisits);

        if (debugPrint) {
            ofs << "visited { ";
            for (auto u : visited)
                ofs << u << ' ';
            ofs << "}\n";
        }

        initNodeStack(PG->getEntry()->getRoot(), callStack, to_process, visited);
        return to_process;
    }

    void initNodeStack(PSNode* nd, CallStack stack, std::vector<NodeStackPair>& to_process, std::vector<unsigned>& remainingVisits) {
        assert(remainingVisits.at(nd->getID()) && "Visiting already visited node\n");
        ofs << _tmpNodeStackPairToString({ nd, stack }) << '\n';

        to_process.emplace_back(nd, stack);
        --remainingVisits.at(nd->getID());

        if (nd->getType() == PSNodeType::CALL /*|| nd->getType() == PSNodeType::CALL_FUNCPTR*/) {
            stack.push(nd);
            for (auto *subG : PSNodeCall::cast(nd)->getCallees()) {
                if (remainingVisits.at(subG->getRoot()->getID()))
                    initNodeStack(subG->getRoot(), stack, to_process, remainingVisits);

                // to fix this situation: CALL is visited (2x), ENTRY is visited(2x), therefore we dont progress
                // into 3rd visit so the nodes past last CALL_RETURN are not visited 2x but only 1x eg. unsorted/recCycle.c
                else if (PSNodeCall::cast(nd)->getPairedNode() && remainingVisits.at(PSNodeCall::cast(nd)->getPairedNode()->getID())) {
                    stack.pop();
                    initNodeStack(PSNodeCall::cast(nd)->getPairedNode(), stack, to_process, remainingVisits);
                }
            }
        } else if (nd->getType() == PSNodeType::RETURN) {
            // callStack of main() is empty therefore we cannot pop
            if (nd->getParent()->getID() == 1)
                return;

            PSNode* callee = stack.top();
            stack.pop();

            for (auto* callRet : PSNodeRet::get(nd)->getReturnSites()) {
                if (callRet == callee->getPairedNode() && remainingVisits.at(callRet->getID()))
                    initNodeStack(callRet, stack, to_process, remainingVisits);
            }

        } else {
            for (auto* suc : nd->getSuccessors()) {
                if (remainingVisits.at(suc->getID()))
                    initNodeStack(suc, stack, to_process, remainingVisits);
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
            // TODO: has to be outside noChange if multiple returns can progress into single CALL_RETURN
            // TODO: if more than 1 callRet are possible, then we cannot store the route in stack with single CALL*s
            if (isa<PSNodeType::CALL_RETURN>(node)) {
                auto& returns = PSNodeCallRet::cast(node)->getReturns();
                // TODO: use only possible call-returns
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
    };

    class WalkCS {
        struct IdTrackerIA {
            std::vector<unsigned> remainingVisits;

            IdTrackerIA(std::vector<unsigned> visits) : remainingVisits(std::move(visits)) {}

            void visit(NodeStackPair* pair) {
                --remainingVisits.at(pair->first->getID());
            }

            bool visited(NodeStackPair* pair) {
                return remainingVisits.at(pair->first->getID()) == 0;
            }
        };

        struct EdgeChooser {
            EdgeChooser() = default;

            NodeStackPair getSuccs(NodeStackPair* current) {

            }

            void foreach(NodeStackPair *cur, std::function<void(NodeStackPair*)> Dispatch) {
//                NodeStackPair copy = *cur;
                if (PSNodeCall *C = PSNodeCall::get(cur->first)) {
//                    copy.second.push(cur->first);
                    for (auto subg : C->getCallees()) {
//                        copy.first = subg->getRoot();
//                        Dispatch(&copy);
                    }
                    // we do not need to iterate over succesors
                    // if we dive into the procedure (as we will
                    // return via call return)
                    // NOTE: we must iterate over successors if the
                    // function is undefined
                    if (!C->getCallees().empty())
                        return;
                } else if (PSNodeRet *R = PSNodeRet::get(cur->first)) {
                    for (auto ret : R->getReturnSites()) {
                        // TODO: if there is unknown return site, we have to Dispatch all returns
                        // atm there is no unknown call in call stacks
                        if (ret == cur->second.top()) {
//                            copy.first = ret;
//                            copy.second.pop();
//                            Dispatch(&copy);
                        }
                    }
                    if (!R->getReturnSites().empty())
                        return;
                }

                for (auto s : cur->first->getSuccessors()) {
//                    copy.first = s;
//                    Dispatch(&copy);
                }
            }
        };

        QueueFIFO<NodeStackPair*> _queue;
        IdTrackerIA _visits;
        EdgeChooser _chooser;

        template <typename T>
        void _enqueue(T *n) {
            _queue.push(n);
            _visits.visit(n);
        }

    public:
        WalkCS(std::vector<unsigned> visits) : _visits(IdTrackerIA(std::move(visits))), _chooser(EdgeChooser{}) {}

        std::vector<NodeStackPair> run(NodeStackPair& start) {
            _queue = {};
            auto visitTracker = _visits;
            std::vector<NodeStackPair> cont;
            auto append = [&cont](NodeStackPair* curr){ cont.push_back(*curr); };

            _enqueue(&start);

            while (!_queue.empty()) {
                NodeStackPair* current = _queue.pop();

                append(current);

                _chooser.foreach(current,
                                 [&](NodeStackPair *n) {
                                     if (!_visits.visited(n)) {
                                         _enqueue(n);
                                     }
                                 });
            }


            return cont;
        }
    };

    /*
    std::vector<NodeStackPair> getReachables(NodeStackPair* start, std::vector<unsigned> remainingVisits) const {
        QueueFIFO<NodeStackPair *> fifo;
        std::vector<NodeStackPair> cont;

        auto visit = [&remainingVisits](NodeStackPair* pair){ --remainingVisits.at(pair->first->getID()); };
        auto visited = [&remainingVisits](NodeStackPair* pair){ return remainingVisits.at(pair->first->getID()) == 0; };

        fifo.push(start);

        while (!fifo.empty()) {
            NodeStackPair* cur = fifo.pop();
            visit(cur);

            if (PSNodeCall* C = PSNodeCall::get(cur->first)) {

                for (auto subg : C->getCallees()) {

                }
            }
        }
    }*/

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
        ss << '<' << pair.first->getID() << "> " << PSNodeTypeToCString(pair.first->getType()) << " callStack["
        << pair.second.size() << "]: { ";
        bool delim = false;
        while (!pair.second.empty()) {
            if (delim)
                ss << ", ";
            delim = true;
            ss << pair.second.top()->getID();
            pair.second.pop();
        }
        ss << " ] }";
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
        auto visited = initVisited(PG);
        std::vector<NodeStackPair> to_process = initStacks(visited);
        std::vector<NodeStackPair> changed;

        // I could use CallStack to differentiate between local vars in different calls of a function.
        // It wouldn't help with calls from a loop or recursion
        std::map<unsigned, std::set<PSNode*>> parentToLocalsMap;

        WalkCS walk(visited);

        CallstackNode root;

/*
        while(!to_process.empty()) {
            for (auto& nodeStackPair : to_process) {
                if (processNode(nodeStackPair.first, parentToLocalsMap)) {
                    auto reachables = walk.run(nodeStackPair);
                    //auto reachables = PG->getNodesContexSensitive(&nodeStackPair, visited);
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
*/
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
        

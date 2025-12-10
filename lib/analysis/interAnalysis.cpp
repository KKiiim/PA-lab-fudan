#include "interAnalysis.h"
#include "IR/IR.h"
#include "analysis/intervalAnalysis.h"
#include <iostream>
#include <queue>

using namespace fdlang;
using namespace fdlang::analysis;

/****************************************************************
********************* Your code starts here *********************
*****************************************************************/
void InterAnalysis::fixedPoint() {
    // Initialize function worklist with root functions
    for (auto f : funcs) {
        if (f->isRoot()) {
            funcWorklist.push_back(f);
        }
    }

    while (!funcWorklist.empty()) {
        IR::Function *f = funcWorklist.front();
        funcWorklist.pop_front();
        interFixedPoint(f);
    }
}

void InterAnalysis::intraFixedPoint(IR::Function *function) {
    while (!worklist.empty()) {
        size_t label = worklist.front();
        worklist.pop();
        inlist.erase(label);

        if (!function->label2Inst.count(label)) {
            continue;
        }
        IR::Inst *inst = function->label2Inst[label];
        States &inputState = inputStates[label];
        States outputState = transfer(inst, inputState);

        // Handle call by directly analyzing the callee with mapped entry state
        if (inst->getInstType() == IR::InstType::CallInst) {
            auto callInst = static_cast<IR::CallInst *>(inst);
            IR::Function *callee = callInst->getCallee();
            if (callee == nullptr) {
                std::string name = callInst->getCalleeName();
                for (auto f : funcs) {
                    if (f->funcName == name) {
                        callee = f;
                        break;
                    }
                }
            }
            if (callee) {
                size_t calleeEntry = 0;
                if (!callee->getInsts().empty()) {
                    calleeEntry = callee->getInsts().front()->getLabel();
                } else {
                    calleeEntry = callee->getBeginLabel();
                }
                // Push call context so iniStates can initialize callee params precisely
                CallContext ctx(function, callInst, inputState);
                ctx.callee = callee;
                callcontextStack.push(ctx);
                States mapped = iniStates(callee);
                auto callArgs = callInst->getArgs();
                auto calleeArgs = callee->getArgs();
                for (size_t i = 0; i < callArgs.size() && i < calleeArgs.size();
                     ++i) {
                    auto ca = callArgs[i];
                    auto pa = calleeArgs[i];
                    if (pa->isVariable()) {
                        if (ca->isVariable())
                            mapped[pa->getAsVariable()] =
                                inputState[ca->getAsVariable()];
                        else if (ca->isNumber()) {
                            long long v = ca->getAsNumber();
                            mapped[pa->getAsVariable()] = Interval{v, v, false};
                        }
                    }
                }
                if (joinInto(mapped, inputStates[calleeEntry])) {
                    // Run callee to fixed point immediately to ensure its checks are analyzed
                    interFixedPoint(callee);
                }
                callcontextStack.pop();
            }
        }

        addSuccessors(inst, outputState);
    }
}

void InterAnalysis::interFixedPoint(IR::Function *function) {
    // ini States and worklist
    resetIntra();

    // Initialize entry states (use first real instruction label)
    size_t entryLabel = 0;
    if (!function->getInsts().empty()) {
        entryLabel = function->getInsts().front()->getLabel();
    } else {
        entryLabel = function->getBeginLabel();
    }
    if (inputStates.find(entryLabel) == inputStates.end()) {
        States s = iniStates(function);
        inputStates[entryLabel] = s;
    }
    // Seed worklist with any labels already having input states for this function
    for (auto &kv : inputStates) {
        if (function->label2Inst.count(kv.first)) {
            if (!inlist.count(kv.first)) {
                worklist.push(kv.first);
                inlist.insert(kv.first);
            }
        }
    }
    // Always ensure entry label is in worklist to start traversal
    if (!inlist.count(entryLabel)) {
        worklist.push(entryLabel);
        inlist.insert(entryLabel);
    }

    intraFixedPoint(function);
}

void InterAnalysis::resetIntra() {
    while (!worklist.empty())
        worklist.pop();
    inlist.clear();
}

void InterAnalysis::checkInstsStates() {
    for (auto func : funcs) {
        for (auto inst : func->getInsts()) {
            if (inst->getInstType() != IR::InstType::CheckIntervalInst)
                continue;

            IR::CheckIntervalInst *checkInst = (IR::CheckIntervalInst *)inst;
            std::string variable = checkInst->getOperand(0)->getAsVariable();
            long long l = checkInst->getOperand(1)->getAsNumber();
            long long r = checkInst->getOperand(2)->getAsNumber();
            auto it = inputStates.find(inst->getLabel());
            if (it == inputStates.end()) {
                results[checkInst] = ResultType::NO;
            } else if (it->second[variable].isBottom) {
                results[checkInst] = ResultType::UNREACHABLE;
            } else {
                auto interval = it->second[variable];
                if (!interval.isBottom && interval.l >= l && interval.r <= r)
                    results[checkInst] = ResultType::YES;
                else
                    results[checkInst] = ResultType::NO;
            }
        }
    }
}

States InterAnalysis::iniStates(IR::Function *function) {
    States s;
    // collect variables appearing in function
    std::set<std::string> vars;
    for (auto inst : function->getInsts()) {
        for (size_t i = 0; i < inst->getOperandSize(); ++i) {
            auto op = inst->getOperand(i);
            if (op->isVariable())
                vars.insert(op->getAsVariable());
        }
    }
    for (auto &v : vars) {
        s[v] = {0, 0, true};
    }
    // initialize params if under a call context
    if (!callcontextStack.empty() &&
        callcontextStack.top().callee == function) {
        for (auto &[var, interval] : callcontextStack.top().params) {
            s[var] = interval;
        }
    }
    return s;
}

States InterAnalysis::transfer(IR::Inst *inst, States &input) {
    States out = input;
    auto getInterval = [&](const std::string &var) -> Interval {
        auto it = input.find(var);
        if (it == input.end())
            return Interval{0, 0, true};
        return it->second;
    };

    auto joinInterval = [&](const Interval &a, const Interval &b) -> Interval {
        if (a.isBottom)
            return b;
        if (b.isBottom)
            return a;
        return Interval{std::min(a.l, b.l), std::max(a.r, b.r), false};
    };
    auto meetInterval = [&](const Interval &a, long long l,
                            long long r) -> Interval {
        if (a.isBottom)
            return a;
        long long nl = std::max(a.l, l);
        long long nr = std::min(a.r, r);
        if (nl > nr)
            return Interval{0, 0, true};
        return Interval{nl, nr, false};
    };
    auto addInterval = [&](const Interval &a, const Interval &b) -> Interval {
        if (a.isBottom || b.isBottom)
            return Interval{0, 0, true};
        long long l = std::min(a.l + b.l, 255LL);
        long long r = std::min(a.r + b.r, 255LL);
        return Interval{l, r, false};
    };
    auto subInterval = [&](const Interval &a, const Interval &b) -> Interval {
        if (a.isBottom || b.isBottom)
            return Interval{0, 0, true};
        long long l = std::max(a.l - b.r, 0LL);
        long long r = std::max(a.r - b.l, 0LL);
        return Interval{l, r, false};
    };

    switch (inst->getInstType()) {
    case IR::InstType::AddInst: {
        std::string lhs = inst->getOperand(0)->getAsVariable();
        Interval a = inst->getOperand(1)->isVariable()
                         ? getInterval(inst->getOperand(1)->getAsVariable())
                         : Interval{inst->getOperand(1)->getAsNumber(),
                                    inst->getOperand(1)->getAsNumber(), false};
        Interval b = inst->getOperand(2)->isVariable()
                         ? getInterval(inst->getOperand(2)->getAsVariable())
                         : Interval{inst->getOperand(2)->getAsNumber(),
                                    inst->getOperand(2)->getAsNumber(), false};
        out[lhs] = addInterval(a, b);
        break;
    }
    case IR::InstType::SubInst: {
        std::string lhs = inst->getOperand(0)->getAsVariable();
        Interval a = inst->getOperand(1)->isVariable()
                         ? getInterval(inst->getOperand(1)->getAsVariable())
                         : Interval{inst->getOperand(1)->getAsNumber(),
                                    inst->getOperand(1)->getAsNumber(), false};
        Interval b = inst->getOperand(2)->isVariable()
                         ? getInterval(inst->getOperand(2)->getAsVariable())
                         : Interval{inst->getOperand(2)->getAsNumber(),
                                    inst->getOperand(2)->getAsNumber(), false};
        out[lhs] = subInterval(a, b);
        break;
    }
    case IR::InstType::InputInst: {
        std::string lhs = inst->getOperand(0)->getAsVariable();
        out[lhs] = {0, 255, false};
        break;
    }
    case IR::InstType::AssignInst: {
        std::string lhs = inst->getOperand(0)->getAsVariable();
        auto op1 = inst->getOperand(1);
        if (op1->isVariable())
            out[lhs] = getInterval(op1->getAsVariable());
        else
            out[lhs] = {op1->getAsNumber(), op1->getAsNumber(), false};
        break;
    }
    case IR::InstType::CheckIntervalInst:
    case IR::InstType::IfInst:
    case IR::InstType::GotoInst:
    case IR::InstType::LabelInst:
    case IR::InstType::CallInst:
        break;
    }
    return out;
}

bool InterAnalysis::joinInto(const States &x, States &y) {
    bool changed = false;
    auto joinInterval = [&](const Interval &a, const Interval &b) -> Interval {
        if (a.isBottom)
            return b;
        if (b.isBottom)
            return a;
        return Interval{std::min(a.l, b.l), std::max(a.r, b.r), false};
    };
    for (auto const &kv : x) {
        auto it = y.find(kv.first);
        if (it == y.end()) {
            y[kv.first] = kv.second;
            changed = true;
        } else {
            Interval j = joinInterval(it->second, kv.second);
            if (!(j == it->second)) {
                y[kv.first] = j;
                changed = true;
            }
        }
    }
    return changed;
}

void InterAnalysis::addSuccessors(IR::Inst *nowInst, States outputState) {
    auto meetInterval = [&](const Interval &a, long long l,
                            long long r) -> Interval {
        if (a.isBottom)
            return a;
        long long nl = std::max(a.l, l);
        long long nr = std::min(a.r, r);
        if (nl > nr)
            return Interval{0, 0, true};
        return Interval{nl, nr, false};
    };

    for (auto suc : nowInst->getSuccessors()) {
        size_t sucLabel = suc->getLabel();
        States newInput = outputState;
        // Propagate actuals to formals for call edges
        if (nowInst->getInstType() == IR::InstType::CallInst) {
            auto callInst = static_cast<IR::CallInst *>(nowInst);
            IR::Function *callee = callInst->getCallee();
            if (callee == nullptr) {
                std::string name = callInst->getCalleeName();
                for (auto f : funcs) {
                    if (f->funcName == name) {
                        callee = f;
                        break;
                    }
                }
            }
            if (callee) {
                auto callArgs = callInst->getArgs();
                auto calleeArgs = callee->getArgs();
                for (size_t i = 0; i < callArgs.size() && i < calleeArgs.size();
                     ++i) {
                    auto ca = callArgs[i];
                    auto pa = calleeArgs[i];
                    if (pa->isVariable()) {
                        if (ca->isVariable())
                            newInput[pa->getAsVariable()] =
                                outputState[ca->getAsVariable()];
                        else if (ca->isNumber()) {
                            long long v = ca->getAsNumber();
                            newInput[pa->getAsVariable()] =
                                Interval{v, v, false};
                        }
                    }
                }
            }
        }
        if (nowInst->getInstType() == IR::InstType::IfInst) {
            auto ifInst = static_cast<IR::IfInst *>(nowInst);
            auto cmp = ifInst->getCmpOperator();
            auto var = ifInst->getOperand(0)->getAsVariable();
            auto val = ifInst->getOperand(1)->getAsNumber();
            if (suc == ifInst->getDestInst()) {
                switch (cmp) {
                case IR::CmpOperator::EQ:
                    newInput[var] = meetInterval(newInput[var], val, val);
                    break;
                case IR::CmpOperator::GEQ:
                    newInput[var] = meetInterval(newInput[var], val, 255);
                    break;
                case IR::CmpOperator::GT:
                    newInput[var] = meetInterval(newInput[var], val + 1, 255);
                    break;
                case IR::CmpOperator::LEQ:
                    newInput[var] = meetInterval(newInput[var], 0, val);
                    break;
                case IR::CmpOperator::LT:
                    newInput[var] = meetInterval(newInput[var], 0, val - 1);
                    break;
                }
            } else {
                switch (cmp) {
                case IR::CmpOperator::EQ: {
                    auto cur = newInput[var];
                    if (!cur.isBottom) {
                        if (cur.l == cur.r && cur.l == val)
                            newInput[var] = {0, 0, true};
                        else if (val == cur.l)
                            newInput[var] = meetInterval(cur, val + 1, cur.r);
                        else if (val == cur.r)
                            newInput[var] = meetInterval(cur, cur.l, val - 1);
                        else if (val > cur.l && val < cur.r) {
                            Interval left = meetInterval(cur, cur.l, val - 1);
                            Interval right = meetInterval(cur, val + 1, cur.r);
                            newInput[var] =
                                Interval{std::min(left.l, right.l),
                                         std::max(left.r, right.r),
                                         left.isBottom && right.isBottom};
                        }
                    }
                    break;
                }
                case IR::CmpOperator::GEQ:
                    newInput[var] = meetInterval(newInput[var], 0, val - 1);
                    break;
                case IR::CmpOperator::GT:
                    newInput[var] = meetInterval(newInput[var], 0, val);
                    break;
                case IR::CmpOperator::LEQ:
                    newInput[var] = meetInterval(newInput[var], val + 1, 255);
                    break;
                case IR::CmpOperator::LT:
                    newInput[var] = meetInterval(newInput[var], val, 255);
                    break;
                }
            }
        }
        if (joinInto(newInput, inputStates[sucLabel])) {
            // If successor belongs to another function, schedule it
            // Determine if successor label belongs to current function
            bool inCurrent = false;
            for (auto &kv : functionEntryStates) {
                (void)kv;
            }
            // current function context is not directly available here; infer by label presence
            bool sucInCaller = false;
            // Try to see if sucLabel exists in any function; pick owner
            IR::Function *owner = nullptr;
            for (auto f : funcs) {
                if (f->label2Inst.count(sucLabel)) {
                    owner = f;
                    break;
                }
            }
            // If owner is different from the function currently being processed in intra, we can't know here.
            // Assume cross-function if owner exists and caller doesn't own it.
            if (owner) {
                // We don't have the caller function pointer here; schedule owner and do not push label locally
                if (!inlist.count(sucLabel)) {
                    funcWorklist.push_back(owner);
                }
            } else {
                if (!inlist.count(sucLabel)) {
                    worklist.push(sucLabel);
                    inlist.insert(sucLabel);
                }
            }
        }
    }
}

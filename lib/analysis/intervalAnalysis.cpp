#include "intervalAnalysis.h"
#include <queue>
#include <set>
#include <string>
#include <unordered_map>

namespace fdlang::analysis {

void IntervalAnalysis::fixedPoint() {
    size_t entryLabel = insts.front()->getLabel();
    inputStates[entryLabel] = iniStates();
    worklist.push(entryLabel);
    while (!worklist.empty()) {
        auto const label = worklist.front();
        worklist.pop();
        auto inst = label2Inst[label];
        States &inputState = inputStates[label];
        States outputState = transfer(inst, inputState);
        addSuccessors(label, outputState);
    }
}

// Helper: join two intervals
static Interval joinInterval(const Interval &a, const Interval &b) {
    if (a.isBottom)
        return b;
    if (b.isBottom)
        return a;
    return {std::min(a.l, b.l), std::max(a.r, b.r), false};
}

// Helper: meet interval with [l, r]
static Interval meetInterval(const Interval &a, long long l, long long r) {
    if (a.isBottom)
        return a;
    long long const nl = std::max(a.l, l);
    long long const nr = std::min(a.r, r);
    if (nl > nr)
        return {0, 0, true};
    return {nl, nr, false};
}

// Helper: add two intervals, clamp to [0,255]
static Interval addInterval(const Interval &a, const Interval &b) {
    if (a.isBottom || b.isBottom)
        return {0, 0, true};
    long long const l = std::min(a.l + b.l, 255LL);
    long long const r = std::min(a.r + b.r, 255LL);
    return {l, r, false};
}

// Helper: sub two intervals, clamp to [0,255]
static Interval subInterval(const Interval &a, const Interval &b) {
    if (a.isBottom || b.isBottom)
        return {0, 0, true};
    long long const l = std::max(a.l - b.r, 0LL);
    long long const r = std::max(a.r - b.l, 0LL);
    return {l, r, false};
}

// Helper: get all variables in the function
static std::set<std::string> collectVariables(const fdlang::IR::Insts &insts) {
    std::set<std::string> vars;
    for (auto const inst : insts) {
        for (size_t i = 0; i < inst->getOperandSize(); ++i) {
            auto const op = inst->getOperand(i);
            if (op->isVariable())
                vars.insert(op->getAsVariable());
        }
    }
    return vars;
}

States IntervalAnalysis::iniStates() {
    States s;
    auto vars = collectVariables(insts);
    for (auto &v : vars)
        s[v] = {0, 0, true}; // bottom
    return s;
}

States IntervalAnalysis::transfer(fdlang::IR::Inst *inst, States &input) {
    States out = input;
    auto getInterval = [&](const std::string &var) -> Interval {
        auto it = input.find(var);
        if (it == input.end())
            return {0, 0, true};
        return it->second;
    };
    switch (inst->getInstType()) {
    case fdlang::IR::InstType::AddInst: {
        std::string const lhs = inst->getOperand(0)->getAsVariable();
        std::string const v1 = inst->getOperand(1)->isVariable()
                                   ? inst->getOperand(1)->getAsVariable()
                                   : "";
        std::string const v2 = inst->getOperand(2)->isVariable()
                                   ? inst->getOperand(2)->getAsVariable()
                                   : "";
        Interval a = inst->getOperand(1)->isVariable()
                         ? getInterval(v1)
                         : Interval{inst->getOperand(1)->getAsNumber(),
                                    inst->getOperand(1)->getAsNumber(), false};
        Interval b = inst->getOperand(2)->isVariable()
                         ? getInterval(v2)
                         : Interval{inst->getOperand(2)->getAsNumber(),
                                    inst->getOperand(2)->getAsNumber(), false};
        out[lhs] = addInterval(a, b);
        break;
    }
    case fdlang::IR::InstType::SubInst: {
        std::string const lhs = inst->getOperand(0)->getAsVariable();
        std::string const v1 = inst->getOperand(1)->isVariable()
                                   ? inst->getOperand(1)->getAsVariable()
                                   : "";
        std::string const v2 = inst->getOperand(2)->isVariable()
                                   ? inst->getOperand(2)->getAsVariable()
                                   : "";
        Interval a = inst->getOperand(1)->isVariable()
                         ? getInterval(v1)
                         : Interval{inst->getOperand(1)->getAsNumber(),
                                    inst->getOperand(1)->getAsNumber(), false};
        Interval b = inst->getOperand(2)->isVariable()
                         ? getInterval(v2)
                         : Interval{inst->getOperand(2)->getAsNumber(),
                                    inst->getOperand(2)->getAsNumber(), false};
        out[lhs] = subInterval(a, b);
        break;
    }
    case fdlang::IR::InstType::InputInst: {
        std::string const lhs = inst->getOperand(0)->getAsVariable();
        out[lhs] = {0, 255, false};
        break;
    }
    case fdlang::IR::InstType::AssignInst: {
        std::string const lhs = inst->getOperand(0)->getAsVariable();
        auto const op1 = inst->getOperand(1);
        if (op1->isVariable())
            out[lhs] = getInterval(op1->getAsVariable());
        else
            out[lhs] = {op1->getAsNumber(), op1->getAsNumber(), false};
        break;
    }
    case fdlang::IR::InstType::CheckIntervalInst:
        // No state change
        break;
    case fdlang::IR::InstType::IfInst: {
        // No state change here; handled in addSuccessors
        break;
    }
    case fdlang::IR::InstType::GotoInst:
    case fdlang::IR::InstType::LabelInst:
    case fdlang::IR::InstType::CallInst:
        // No state change
        break;
    }
    return out;
}

bool IntervalAnalysis::joinInto(const States &x, States &y) {
    bool changed = false;
    for (auto &[var, interval] : x) {
        auto const it = y.find(var);
        if (it == y.end()) {
            y[var] = interval;
            changed = true;
        } else {
            auto joined = joinInterval(it->second, interval);
            if (!(joined == it->second)) {
                y[var] = joined;
                changed = true;
            }
        }
    }
    return changed;
}

void IntervalAnalysis::addSuccessors(size_t nowLabel, States outputState) {
    auto const inst = label2Inst[nowLabel];
    for (auto suc : inst->getSuccessors()) {
        size_t const sucLabel = suc->getLabel();
        States newInput = outputState;
        // If this is an IfInst, restrict according to the branch
        if (inst->getInstType() == fdlang::IR::InstType::IfInst) {
            auto const ifInst = static_cast<fdlang::IR::IfInst *>(inst);
            auto const cmp = ifInst->getCmpOperator();
            auto const var = ifInst->getOperand(0)->getAsVariable();
            auto const val = ifInst->getOperand(1)->getAsNumber();
            // True branch
            if (suc == ifInst->getDestInst()) {
                switch (cmp) {
                case fdlang::IR::CmpOperator::EQ:
                    newInput[var] = meetInterval(newInput[var], val, val);
                    break;
                case fdlang::IR::CmpOperator::GEQ:
                    newInput[var] = meetInterval(newInput[var], val, 255);
                    break;
                case fdlang::IR::CmpOperator::GT:
                    newInput[var] = meetInterval(newInput[var], val + 1, 255);
                    break;
                case fdlang::IR::CmpOperator::LEQ:
                    newInput[var] = meetInterval(newInput[var], 0, val);
                    break;
                case fdlang::IR::CmpOperator::LT:
                    newInput[var] = meetInterval(newInput[var], 0, val - 1);
                    break;
                }
            } else {
                // False branch
                switch (cmp) {
                case fdlang::IR::CmpOperator::EQ:
                    if (!newInput[var].isBottom) {
                        if (newInput[var].l == newInput[var].r &&
                            newInput[var].l == val)
                            newInput[var] = {0, 0, true};
                        else if (val == newInput[var].l)
                            newInput[var] = meetInterval(newInput[var], val + 1,
                                                         newInput[var].r);
                        else if (val == newInput[var].r)
                            newInput[var] = meetInterval(
                                newInput[var], newInput[var].l, val - 1);
                        else if (val > newInput[var].l && val < newInput[var].r)
                            newInput[var] = joinInterval(
                                meetInterval(newInput[var], newInput[var].l,
                                             val - 1),
                                meetInterval(newInput[var], val + 1,
                                             newInput[var].r));
                    }
                    break;
                case fdlang::IR::CmpOperator::GEQ:
                    newInput[var] = meetInterval(newInput[var], 0, val - 1);
                    break;
                case fdlang::IR::CmpOperator::GT:
                    newInput[var] = meetInterval(newInput[var], 0, val);
                    break;
                case fdlang::IR::CmpOperator::LEQ:
                    newInput[var] = meetInterval(newInput[var], val + 1, 255);
                    break;
                case fdlang::IR::CmpOperator::LT:
                    newInput[var] = meetInterval(newInput[var], val, 255);
                    break;
                }
            }
        }
        if (joinInto(newInput, inputStates[sucLabel])) {
            worklist.push(sucLabel);
        }
    }
}

void IntervalAnalysis::checkInstsStates() {
    for (auto inst : insts) {
        if (inst->getInstType() != fdlang::IR::InstType::CheckIntervalInst)
            continue;
        auto const checkInst =
            static_cast<fdlang::IR::CheckIntervalInst *>(inst);
        std::string const variable = checkInst->getOperand(0)->getAsVariable();
        long long const l = checkInst->getOperand(1)->getAsNumber();
        long long const r = checkInst->getOperand(2)->getAsNumber();
        auto const it = inputStates.find(inst->getLabel());
        if (it == inputStates.end() || it->second[variable].isBottom) {
            results[checkInst] = ResultType::UNREACHABLE;
            continue;
        }
        auto const interval = it->second[variable];
        if (!interval.isBottom && interval.l >= l && interval.r <= r) {
            results[checkInst] = ResultType::YES;
        } else if (!interval.isBottom) {
            results[checkInst] = ResultType::NO;
        } else {
            results[checkInst] = ResultType::UNREACHABLE;
        }
    }
}

} // namespace fdlang::analysis
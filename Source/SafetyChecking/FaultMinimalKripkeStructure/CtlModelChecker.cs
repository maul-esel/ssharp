// The MIT License (MIT)
// 
// Copyright (c) 2014-2017, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace ISSE.SafetyChecking.FaultMinimalKripkeStructure
{
    using AnalysisModel;
    using ExecutableModel;
    using Formula;
    using StateGraphModel;
    using Utilities;

    using System;
    using System.Collections.Generic;
    using System.Linq;

    public class CtlModelChecker<TExecutableModel> where TExecutableModel : ExecutableModel<TExecutableModel>
    {
        private readonly StateGraph<TExecutableModel> _stateGraph;
        private readonly Formula[] _stateFormulas;

        private readonly Dictionary<Formula, bool[]> _checkedFormulas = new Dictionary<Formula, bool[]>();
        private readonly Dictionary<int, int> _stateNumbers = new Dictionary<int, int>();
        private int _maxState = -1;
 
        public CtlModelChecker(ExecutableModelCreator<TExecutableModel> createModel, Formula[] stateFormulas)
        {
            Requires.NotNull(createModel, nameof(createModel));
            Requires.NotNull(stateFormulas, nameof(stateFormulas));
            Requires.That(stateFormulas.Length > 0, nameof(stateFormulas), "Expected at least one state formula.");

            var modelGenerator = createModel.Create(stateFormulas);

            var checker = new QualitativeChecker<TExecutableModel> { Configuration = { ProgressReportsOnly = false } };
            _stateGraph = checker.GenerateStateGraph(modelGenerator);
            _stateFormulas = stateFormulas;
        }

        public AnalysisResult<TExecutableModel> Check(Formula formula)
        {
            var satisfyingStates = CheckInternal(formula);

            return new AnalysisResult<TExecutableModel>
            {
                FormulaHolds = HoldsInAllInitialStates(satisfyingStates),
                StateCount = _stateGraph.StateCount,
                TransitionCount = _stateGraph.TransitionCount
            };
        }

        private int GetState(int index)
        {
            if (_stateNumbers.ContainsKey(index))
                return _stateNumbers[index];
            return _stateNumbers[index] = ++_maxState;
        }

        private bool HoldsInAllInitialStates(bool[] satisfyingStates)
        {
            foreach (var initialTransition in _stateGraph.GetInitialTransitions())
                unsafe
                {
                    if (!satisfyingStates[GetState(initialTransition->TargetStateIndex)])
                        return false;
                }
            return true;
        }

        private bool[] CheckInternal(Formula formula)
        {
            if (_checkedFormulas.ContainsKey(formula))
                return _checkedFormulas[formula];

            var stateFormulaIndex = Array.IndexOf(_stateFormulas, formula);
            if (stateFormulaIndex != -1)
                return _checkedFormulas[formula] = CheckStateFormula(stateFormulaIndex);

            var unaryFormula = formula as UnaryFormula;
            if (unaryFormula != null)
            {
                if (unaryFormula.Operator == UnaryOperator.Not)
                    return _checkedFormulas[formula] = BoolVectorHelper.Not(CheckInternal(unaryFormula.Operand));

                if (unaryFormula.Operator == UnaryOperator.Exists)
                    return _checkedFormulas[formula] = CheckTemporalFormula(unaryFormula.Operand);
            }

            var binaryFormula = formula as BinaryFormula;
            if (binaryFormula != null && binaryFormula.Operator != BinaryOperator.Until)
                return _checkedFormulas[formula] = CheckBinaryFormula(binaryFormula);

            throw new InvalidOperationException("Can only check normalized CTL formulae");
        }

        private bool[] CheckTemporalFormula(Formula formula)
        {
            var unaryFormula = formula as UnaryFormula;
            if (unaryFormula != null)
            {
                if (unaryFormula.Operator == UnaryOperator.Next)
                    return ImmediatePredecessors(CheckInternal(unaryFormula.Operand));

                if (unaryFormula.Operator == UnaryOperator.Globally)
                {
                    var formulaResult = CheckInternal(unaryFormula.Operand);
                    return PredecessorsWhile(NonTrivialStronglyConnectedWhere(formulaResult), formulaResult);
                }
            }

            var binaryFormula = formula as BinaryFormula;
            if (binaryFormula != null && binaryFormula.Operator == BinaryOperator.Until)
            {
                var leftResult = CheckInternal(binaryFormula.LeftOperand);
                var rightResult = CheckInternal(binaryFormula.RightOperand);
                return PredecessorsWhile(rightResult, leftResult);
            }

            throw new InvalidOperationException("Can only check normalized CTL formulae");
        }

        private bool[] CheckBinaryFormula(BinaryFormula formula)
        {
            var left = CheckInternal(formula.LeftOperand);
            var right = CheckInternal(formula.RightOperand);

            switch (formula.Operator)
            {
                case BinaryOperator.And: return BoolVectorHelper.And(left, right);
                case BinaryOperator.Or: return BoolVectorHelper.Or(left, right);
                case BinaryOperator.Implication: return BoolVectorHelper.Implies(left, right);
                case BinaryOperator.Equivalence: return BoolVectorHelper.Equivalent(left, right);
                default:
                    throw new InvalidOperationException("Can only check normalized CTL formulae");
            }
        }

        private bool[] CheckStateFormula(int index)
        {
            var result = new bool[_stateGraph.StateCount];

            unsafe
            {
                var stack = new StateTransitionStack(_stateGraph.StateCount);
                foreach (var initialTransition in _stateGraph.GetInitialTransitions())
                    stack.Push(initialTransition, GetState(initialTransition->TargetStateIndex));

                while (stack.Size > 0)
                {
                    var current = stack.Pop();

                    result[GetState(current->TargetStateIndex)] = current->Formulas[index];
                    foreach (var outgoingTransition in _stateGraph.GetTransitions(current->TargetStateIndex))
                        stack.Push(outgoingTransition, GetState(outgoingTransition->TargetStateIndex));
                }
            }
            return result;
        }

        private bool[] ImmediatePredecessors(bool[] source)
        {
            var result = new bool[_stateGraph.StateCount];

            unsafe
            {
                var stack = new StateTransitionStack(_stateGraph.StateCount);
                foreach (var initialTransition in _stateGraph.GetInitialTransitions())
                    stack.Push(initialTransition, GetState(initialTransition->TargetStateIndex));

                while (stack.Size > 0)
                {
                    var current = stack.Pop();

                    foreach (var outgoingTransition in _stateGraph.GetTransitions(current->TargetStateIndex))
                    {
                        var successor = GetState(outgoingTransition->TargetStateIndex);
                        stack.Push(outgoingTransition, successor);
                        result[GetState(current->TargetStateIndex)] |= source[successor];
                    }
                }
            }
            return result;
        }

        // Returns the elements in source as well as all their transitive predecessors that are linked to source by a chain in condition.
        private bool[] PredecessorsWhile(bool[] source, bool[] condition)
        {
            var result = new bool[_stateGraph.StateCount];
            var seen = new bool[_stateGraph.StateCount];

            foreach (var initialTransition in _stateGraph.GetInitialTransitions())
                unsafe
                {
                    PredecessorsWhile(initialTransition->TargetStateIndex, source, condition, result, seen);
                }

            return result;
        }

        private void PredecessorsWhile(int current, bool[] source, bool[] condition, bool[] result, bool[] seen)
        {
            var currentState = GetState(current);
            seen[currentState] = true;
            result[currentState] = source[currentState]; // elements in source are reflexive-transitive predecessors of elements in source

            foreach (var outgoingTransition in _stateGraph.GetTransitions(current))
                unsafe
                {
                    if (!seen[GetState(outgoingTransition->TargetStateIndex)])
                        PredecessorsWhile(outgoingTransition->TargetStateIndex, source, condition, result, seen);

                    // if a successor is a valid predecessor of source, and condition holds in current, then current is a valid predecessor:
                    result[currentState] |= condition[currentState] && result[GetState(outgoingTransition->TargetStateIndex)];
                }
        }

        private bool[] NonTrivialStronglyConnectedWhere(bool[] condition)
        {
            var result = new bool[_stateGraph.StateCount];
            var inComp = new bool[_stateGraph.StateCount];
            var root = new int[_stateGraph.StateCount];
            var count = new int[_stateGraph.StateCount];
            var maxCount = 0;
            var stack = new StateTransitionStack(_stateGraph.StateCount);

            foreach (var initialTransition in _stateGraph.GetInitialTransitions())
                unsafe
                {
                    var initialState = GetState(initialTransition->TargetStateIndex);
                    if (count[initialState] == 0 && condition[initialState])
                        NonTrivialStronglyConnectedWhere(initialTransition, condition, result, inComp, root, count, ref maxCount, stack);
                }

            return result;
        }

        private unsafe void NonTrivialStronglyConnectedWhere(Transition* current, bool[] condition, bool[] result, bool[] inComp, int[] root, int[] count, ref int maxCount, StateTransitionStack stack)
        {
            var currentState = GetState(current->TargetStateIndex);
            root[currentState] = currentState;
            count[currentState] = ++maxCount;
            stack.Push(current, currentState);

            var hasSelfLoop = false;
            foreach (var outgoingTransition in _stateGraph.GetTransitions(current->TargetStateIndex))
            {
                var successorState = GetState(outgoingTransition->TargetStateIndex);
                hasSelfLoop |= successorState == currentState;
                if (!condition[successorState])
                    continue;

                if (count[successorState] == 0)
                    NonTrivialStronglyConnectedWhere(outgoingTransition, condition, result, inComp, root, count, ref maxCount, stack);
                if (!inComp[successorState] && count[root[successorState]] < count[root[currentState]])
                    root[currentState] = root[successorState];
            }

            if (root[currentState] == currentState)
            {
                var isNonTrivial = stack.Peek() != current || hasSelfLoop;
                int x;
                do
                {
                    x = GetState(stack.Pop()->TargetStateIndex);
                    inComp[x] = true;
                    result[x] = isNonTrivial;
                } while (x != currentState);
            }
        }

        private unsafe class StateTransitionStack
        {
            private readonly Transition*[] _stack;
            private readonly bool[] _seen;

            private int _top = -1;

            public int Size => _top + 1;

            public StateTransitionStack(int capacity)
            {
                _stack = new Transition*[capacity];
                _seen = new bool[capacity];
            }

            public void Push(Transition* element, int state)
            {
                if (_seen[state])
                    return;

                _stack[++_top] = element;
                _seen[state] = true;
            }

            public Transition* Pop()
            {
                return _stack[_top--];
            }

            public Transition* Peek()
            {
                return _stack[_top];
            }
        }

        private static class BoolVectorHelper
        {
            public static bool[] Not(bool[] input)
            {
                return input.Select(b => !b).ToArray();
            }

            public static bool[] And(bool[] left, bool[] right)
            {
                return left.Select((l, i) => l && right[i]).ToArray();
            }

            public static bool[] Or(bool[] left, bool[] right)
            {
                return left.Select((l, i) => l || right[i]).ToArray();
            }

            public static bool[] Implies(bool[] left, bool[] right)
            {
                return left.Select((l, i) => !l || right[i]).ToArray();
            }

            public static bool[] Equivalent(bool[] left, bool[] right)
            {
                return left.Select((l, i) => l == right[i]).ToArray();
            }
        }
    }
}

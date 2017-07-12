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

namespace ISSE.SafetyChecking.Formula
{
    using System;

    /// <summary>
    /// Produces an equivalent formula that only uses the temporal operators EX, EG and EU.
    /// </summary>
    class CtlNormalizerVisitor : FormulaVisitor
    {
        private Formula _result;
        private UnaryOperator? _parentOperator = null;

        public Formula NormalizedFormula => _result;

        private Formula Negate(Formula formula)
        {
            var unaryFormula = (formula as UnaryFormula);
            if (unaryFormula != null && unaryFormula.Operator == UnaryOperator.Not)
                return unaryFormula.Operand;
            return !formula;
        }

        public override void VisitUnaryFormula(UnaryFormula formula)
        {
            if (_parentOperator == null)
            {
                if (formula.Operator == UnaryOperator.All || formula.Operator == UnaryOperator.Exists)
                {
                    _parentOperator = formula.Operator;
                    Visit(formula.Operand);
                    return;
                }
                else if (formula.Operator == UnaryOperator.Not)
                {
                    Visit(formula.Operand);
                    _result = Negate(_result);
                    return;
                }
            }
            else if (_parentOperator == UnaryOperator.Exists)
            {
                _parentOperator = null;
                if (formula.Operator == UnaryOperator.Next || formula.Operator == UnaryOperator.Globally)
                {
                    Visit(formula.Operand);
                    _result = new UnaryFormula(new UnaryFormula(_result, formula.Operator), UnaryOperator.Exists);
                    return;
                }
                if (formula.Operator == UnaryOperator.Finally)
                {
                    Visit(formula.Operand);
                    _result = new UnaryFormula(new BinaryFormula(true, BinaryOperator.Until, _result), UnaryOperator.Exists); // (EF \phi) <=> (true EU \phi)
                    return;
                }
            }
            else if (_parentOperator == UnaryOperator.All)
            {
                _parentOperator = null;
                switch (formula.Operator)
                {
                    case UnaryOperator.Next: // (AX \phi) <=> (! EX ! \phi)
                        Visit(formula.Operand);
                        _result = new UnaryFormula(new UnaryFormula(new UnaryFormula(Negate(_result), UnaryOperator.Next), UnaryOperator.Exists), UnaryOperator.Not);
                        return;
                    case UnaryOperator.Finally: // (AF \phi) <=> (! EG ! \phi)
                        Visit(formula.Operand);
                        _result = new UnaryFormula(new UnaryFormula(new UnaryFormula(Negate(_result), UnaryOperator.Globally), UnaryOperator.Exists), UnaryOperator.Not);
                        return;
                    case UnaryOperator.Globally: // (AG \phi) <=> (! EF ! \phi) <=> (! (true EU ! \phi))
                        Visit(formula.Operand);
                        _result = new UnaryFormula(new UnaryFormula(new BinaryFormula(true, BinaryOperator.Until, Negate(_result)), UnaryOperator.Exists), UnaryOperator.Not);
                        return;
                }
            }
            throw new InvalidOperationException("Only CTL formulas can be normalized.");
        }

        public override void VisitBinaryFormula(BinaryFormula formula)
        {
            var temporalOperatorExpected = (_parentOperator != null);
            if (temporalOperatorExpected != (formula.Operator == BinaryOperator.Until))
                throw new InvalidOperationException("Only CTL formulas can be normalized.");

            _parentOperator = null;
            Visit(formula.LeftOperand);
            var left = _result;
            Visit(formula.RightOperand);
            var right = _result;

            if (_parentOperator == null)
                _result = new BinaryFormula(left, formula.Operator, right);
            else if (_parentOperator == UnaryOperator.Exists)
                _result = new UnaryFormula(new BinaryFormula(left, BinaryOperator.Until, right), UnaryOperator.Exists);
            else if (_parentOperator == UnaryOperator.All)
                _result = new UnaryFormula(
                    ExistsWeakUntil(
                        Negate(right),
                        new BinaryFormula(
                            Negate(left),
                            BinaryOperator.And,
                            Negate(right)
                        )
                    ),
                    UnaryOperator.Not
                );
        }

        private static Formula ExistsWeakUntil(Formula left, Formula right)
        {
            return new BinaryFormula(
                new UnaryFormula(new BinaryFormula(left, BinaryOperator.Until, right), UnaryOperator.Exists),
                BinaryOperator.Or,
                new UnaryFormula(new UnaryFormula(left, UnaryOperator.Globally), UnaryOperator.Exists)
            );
        }

        public override void VisitAtomarPropositionFormula(AtomarPropositionFormula formula)
        {
            if (_parentOperator != null)
                throw new InvalidOperationException("Only CTL formulas can be normalized.");
            _result = formula;
        }

        public override void VisitBoundedUnaryFormula(BoundedUnaryFormula formula)
        {
            throw new InvalidOperationException("Only CTL formulas can be normalized.");
        }

        public override void VisitBoundedBinaryFormula(BoundedBinaryFormula formula)
        {
            throw new InvalidOperationException("Only CTL formulas can be normalized.");
        }

        public override void VisitRewardFormula(RewardFormula formula)
        {
            throw new InvalidOperationException("Only CTL formulas can be normalized.");
        }

        public override void VisitProbabilisticFormula(ProbabilitisticFormula formula)
        {
            throw new InvalidOperationException("Only CTL formulas can be normalized.");
        }
    }
}

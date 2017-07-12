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
    class IsCtlFormulaVisitor : FormulaVisitor
    {
        public bool IsCtlFormula { get; private set; } = true;
        private bool _expectingTemporalQuantifier = false;

        public override void VisitUnaryFormula(UnaryFormula formula)
        {
            var isTemporalQuantifier = formula.Operator == UnaryOperator.Finally ||
                                       formula.Operator == UnaryOperator.Globally ||
                                       formula.Operator == UnaryOperator.Next;
            if (_expectingTemporalQuantifier != isTemporalQuantifier)
                IsCtlFormula = false;
            else
            {
                _expectingTemporalQuantifier = (formula.Operator == UnaryOperator.All || formula.Operator == UnaryOperator.Exists);
                Visit(formula.Operand);
            }
        }

        public override void VisitBinaryFormula(BinaryFormula formula)
        {
            var isTemporalQuantifier = formula.Operator == BinaryOperator.Until;
            if (_expectingTemporalQuantifier != isTemporalQuantifier)
                IsCtlFormula = false;
            else
            {
                _expectingTemporalQuantifier = false;
                Visit(formula.LeftOperand);
                if (IsCtlFormula)
                    Visit(formula.RightOperand);
            }
        }

        public override void VisitAtomarPropositionFormula(AtomarPropositionFormula formula)
        {
            if (_expectingTemporalQuantifier)
                IsCtlFormula = false;
        }

        public override void VisitBoundedUnaryFormula(BoundedUnaryFormula formula)
        {
            IsCtlFormula = false;
        }

        public override void VisitBoundedBinaryFormula(BoundedBinaryFormula formula)
        {
            IsCtlFormula = false;
        }

        public override void VisitRewardFormula(RewardFormula formula)
        {
            IsCtlFormula = false;
        }

        public override void VisitProbabilisticFormula(ProbabilitisticFormula formula)
        {
            IsCtlFormula = false;
        }
    }
}

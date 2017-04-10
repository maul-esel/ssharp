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
	using System.Globalization;
	using System.Text;
	using Utilities;

	/// <summary>
	///   Gets the string representation of a <see cref="Formula" />.
	/// </summary>
	internal class ToStringVisitor : FormulaVisitor
	{
		/// <summary>
		///   Gets the string representation of the formula.
		/// </summary>
		public static string FormulaToString(Formula formula)
		{
			var visitor=new ToStringVisitor();
			visitor.Visit(formula);
			return visitor.FormulaString;
		}

		/// <summary>
		///   The string builder that is used to construct the string representation.
		/// </summary>
		private readonly StringBuilder _builder = new StringBuilder();

		/// <summary>
		///   Gets the string representation of the formula.
		/// </summary>
		public string FormulaString => _builder.ToString();

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitUnaryFormula(UnaryFormula formula)
		{
			_builder.Append("(");

			switch (formula.Operator)
			{
				case UnaryOperator.Next:
					_builder.Append(" X ");
					break;
				case UnaryOperator.Finally:
					_builder.Append(" F ");
					break;
				case UnaryOperator.Globally:
					_builder.Append(" G ");
					break;
				case UnaryOperator.Not:
					_builder.Append(" ! ");
					break;
				case UnaryOperator.All:
					_builder.Append(" A ");
					break;
				case UnaryOperator.Exists:
					_builder.Append(" E ");
					break;
				default:
					Assert.NotReached($"Unknown or unsupported unary operator '{formula.Operator}'.");
					break;
			}

			Visit(formula.Operand);
			_builder.Append(")");
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBinaryFormula(BinaryFormula formula)
		{
			_builder.Append("(");
			Visit(formula.LeftOperand);

			switch (formula.Operator)
			{
				case BinaryOperator.And:
					_builder.Append(" && ");
					break;
				case BinaryOperator.Or:
					_builder.Append(" || ");
					break;
				case BinaryOperator.Implication:
					_builder.Append(" -> ");
					break;
				case BinaryOperator.Equivalence:
					_builder.Append(" <-> ");
					break;
				case BinaryOperator.Until:
					_builder.Append(" U ");
					break;
				default:
					Assert.NotReached($"Unknown or unsupported binary operator '{formula.Operator}'.");
					break;
			}

			Visit(formula.RightOperand);
			_builder.Append(")");
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitAtomarPropositionFormula(AtomarPropositionFormula formula)
		{
			_builder.Append(formula.Label);
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBoundedUnaryFormula(BoundedUnaryFormula formula)
		{
			_builder.Append("(");

			switch (formula.Operator)
			{
				case UnaryOperator.Finally:
					_builder.Append(" F");
					break;
				default:
					Assert.NotReached($"Unknown or unsupported unary operator '{formula.Operator}'.");
					break;
			}
			_builder.Append($"<={formula.Bound} ");

			Visit(formula.Operand);
			_builder.Append(")");
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBoundedBinaryFormula(BoundedBinaryFormula formula)
		{
			_builder.Append("(");
			Visit(formula.LeftOperand);

			switch (formula.Operator)
			{
				case BinaryOperator.Until:
					_builder.Append(" U");
					break;
				default:
					Assert.NotReached($"Unknown or unsupported binary operator '{formula.Operator}'.");
					break;
			}
			_builder.Append($"<={formula.Bound} ");

			Visit(formula.RightOperand);
			_builder.Append(")");
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitRewardFormula(RewardFormula formula)
		{
			if (formula is CalculateLongRunExpectedRewardFormula)
			{
				_builder.Append(" LongRunReward(?,");
				_builder.Append(formula.RewardRetriever.Label);
				_builder.Append(" )");
			}
			else if (formula is CalculateExpectedAccumulatedRewardFormula)
			{
				_builder.Append(" ExpectedAccumulatedReward(?,");
				_builder.Append(formula.RewardRetriever.Label);
				_builder.Append(" )");
			}
			else if (formula is ExpectedAccumulatedRewardFormula)
			{
				var expectedAccumulated = (ExpectedAccumulatedRewardFormula)formula;
				var lowerBound = expectedAccumulated.LowerBound.ToString(CultureInfo.InvariantCulture);
				var upperBound = expectedAccumulated.UpperBound.ToString(CultureInfo.InvariantCulture);
				_builder.Append($"ExpectedAccumulatedReward({lowerBound}, {upperBound}, ");
				_builder.Append(formula.RewardRetriever.Label);
				_builder.Append(")");
			}
			else if (formula is LongRunExpectedRewardFormula)
			{
				var longRunExpected = (LongRunExpectedRewardFormula)formula;
				var lowerBound = longRunExpected.LowerBound.ToString(CultureInfo.InvariantCulture);
				var upperBound = longRunExpected.UpperBound.ToString(CultureInfo.InvariantCulture);
				_builder.Append($"LongRunReward({lowerBound}, {upperBound}, ");
				_builder.Append(formula.RewardRetriever.Label);
				_builder.Append(")");
			}
			else
			{
				Assert.NotReached("Not supported, yet");
			}
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitProbabilisticFormula(ProbabilitisticFormula formula)
		{
			_builder.Append("P { ");
			switch (formula.Comparator)
			{
				case ProbabilisticComparator.LowerThan:
					_builder.Append("<");
					break;
				case ProbabilisticComparator.LowerEqual:
					_builder.Append("<=");
					break;
				case ProbabilisticComparator.BiggerThan:
					_builder.Append(">");
					break;
				case ProbabilisticComparator.BiggerEqual:
					_builder.Append(">=");
					break;
				default:
					throw new ArgumentOutOfRangeException();
			}
			_builder.Append(formula.CompareToValue.ToString(CultureInfo.InvariantCulture));
			_builder.Append(" } [ ");
			Visit(formula.Operand);
			_builder.Append(" ]");
		}
	}
}
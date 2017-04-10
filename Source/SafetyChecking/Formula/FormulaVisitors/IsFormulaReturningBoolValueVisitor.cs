﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ISSE.SafetyChecking.Formula
{
	internal class IsFormulaReturningBoolValueVisitor : FormulaVisitor
	{
		/// <summary>
		///   Indicates whether the formula is returning true or false.
		/// </summary>
		public bool IsFormulaReturningBoolValue { get; private set; }

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitUnaryFormula(UnaryFormula formula)
		{
			IsFormulaReturningBoolValue = true;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBinaryFormula(BinaryFormula formula)
		{
			IsFormulaReturningBoolValue = true;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitAtomarPropositionFormula(AtomarPropositionFormula formula)
		{
			IsFormulaReturningBoolValue = true;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBoundedUnaryFormula(BoundedUnaryFormula formula)
		{
			IsFormulaReturningBoolValue = true;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBoundedBinaryFormula(BoundedBinaryFormula formula)
		{
			IsFormulaReturningBoolValue = true;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitRewardFormula(RewardFormula formula)
		{
			if (formula is CalculateExpectedAccumulatedRewardFormula ||
				formula is CalculateLongRunExpectedRewardFormula)
			{
				IsFormulaReturningBoolValue = false;
			}
			else if (formula is ExpectedAccumulatedRewardFormula ||
				formula is LongRunExpectedRewardFormula)
			{
				IsFormulaReturningBoolValue = true;
			}
			else
			{
				throw new Exception("Not supported, yet");
			}
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitProbabilisticFormula(ProbabilitisticFormula formula)
		{
			IsFormulaReturningBoolValue = true;
		}
	}
}

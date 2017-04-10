﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ISSE.SafetyChecking.Formula
{
	internal class IsFormulaReturningRewardResultVisitor : FormulaVisitor
	{
		/// <summary>
		///   Indicates whether the formula is returning a reward result.
		/// </summary>
		public bool IsReturningRewardResult { get; private set; }

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitUnaryFormula(UnaryFormula formula)
		{
			IsReturningRewardResult = false;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBinaryFormula(BinaryFormula formula)
		{
			IsReturningRewardResult = false;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitAtomarPropositionFormula(AtomarPropositionFormula formula)
		{
			IsReturningRewardResult = false;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBoundedUnaryFormula(BoundedUnaryFormula formula)
		{
			IsReturningRewardResult = false;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitBoundedBinaryFormula(BoundedBinaryFormula formula)
		{
			IsReturningRewardResult = false;
		}

		/// <summary>
		///   Visits the <paramref name="formula." />
		/// </summary>
		public override void VisitRewardFormula(RewardFormula formula)
		{
			if (formula is CalculateExpectedAccumulatedRewardFormula ||
				formula is CalculateLongRunExpectedRewardFormula)
			{
				IsReturningRewardResult = true;
			}
			else if (formula is ExpectedAccumulatedRewardFormula ||
				formula is LongRunExpectedRewardFormula)
			{
				IsReturningRewardResult = false;
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
			IsReturningRewardResult = false;
		}
	}
}

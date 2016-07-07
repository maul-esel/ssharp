﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2016, Institute for Software & Systems Engineering
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

namespace SafetySharp.Analysis
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.IO;
	using System.Linq;
	using System.Text;
	using Heuristics;
	using ModelChecking;
	using Modeling;
	using Runtime.Serialization;
	using Utilities;

	/// <summary>
	///   Performs safety analyses on a model.
	/// </summary>
	public sealed class SafetyAnalysis
	{
		private readonly HashSet<FaultSet> _checkedSets = new HashSet<FaultSet>();
		private readonly Dictionary<FaultSet, CounterExample> _counterExamples = new Dictionary<FaultSet, CounterExample>();
		private readonly Dictionary<FaultSet, Exception> _exceptions = new Dictionary<FaultSet, Exception>();
		private FaultSetCollection _criticalSets;
		private FaultSet _forcedSet;
		private InvariantChecker _invariantChecker;
		private Result _result;
		private FaultSetCollection _safeSets;
		private FaultSet _suppressedSet;

		/// <summary>
		///   The model checker's configuration that determines certain model checker settings.
		/// </summary>
		public AnalysisConfiguration Configuration = AnalysisConfiguration.Default;

		/// <summary>
		///   How to handle fault activation during analysis.
		/// </summary>
		public FaultActivationBehaviour FaultActivationBehaviour = FaultActivationBehaviour.Nondeterministic;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		public SafetyAnalysis()
		{
			Configuration.ProgressReportsOnly = true;
		}

		/// <summary>
		///   Gets a list of heuristics to use during the analysis.
		/// </summary>
		public List<IFaultSetHeuristic> Heuristics { get; } = new List<IFaultSetHeuristic>();

		/// <summary>
		///   Raised when the model checker has written an output. The output is always written to the console by default.
		/// </summary>
		public event Action<string> OutputWritten = Console.WriteLine;

		/// <summary>
		///   Computes the minimal critical sets for the <paramref name="hazard" />.
		/// </summary>
		/// <param name="model">The model the safety analysis should be conducted for.</param>
		/// <param name="hazard">The hazard the minimal critical sets should be computed for.</param>
		/// <param name="maxCardinality">
		///   The maximum cardinality of the fault sets that should be checked. By default, all minimal
		///   critical fault sets are determined.
		/// </param>
		public static Result AnalyzeHazard(ModelBase model, Formula hazard, int maxCardinality = Int32.MaxValue)
		{
			return new SafetyAnalysis().ComputeMinimalCriticalSets(model, hazard, maxCardinality);
		}

		/// <summary>
		///   Computes the minimal critical sets for the <paramref name="hazard" />.
		/// </summary>
		/// <param name="model">The model the safety analysis should be conducted for.</param>
		/// <param name="hazard">The hazard the minimal critical sets should be computed for.</param>
		/// <param name="maxCardinality">
		///   The maximum cardinality of the fault sets that should be checked. By default, all minimal
		///   critical fault sets are determined.
		/// </param>
		public Result ComputeMinimalCriticalSets(ModelBase model, Formula hazard, int maxCardinality = Int32.MaxValue)
		{
			Requires.NotNull(model, nameof(model));
			Requires.NotNull(hazard, nameof(hazard));

			ConsoleHelpers.WriteLine("Running Deductive Cause Consequence Analysis.");

			var stopwatch = new Stopwatch();
			stopwatch.Start();

			var allFaults = model.Faults;
			FaultSet.CheckFaultCount(allFaults.Length);

			var forcedFaults = allFaults.Where(fault => fault.Activation == Activation.Forced).ToArray();
			var suppressedFaults = allFaults.Where(fault => fault.Activation == Activation.Suppressed).ToArray();
			var nondeterministicFaults = allFaults.Where(fault => fault.Activation == Activation.Nondeterministic).ToArray();

			_suppressedSet = new FaultSet(suppressedFaults);
			_forcedSet = new FaultSet(forcedFaults);

			var isComplete = true;

			// remove information from previous analyses
			Reset(model);

			// Serialize the model and initialize the invariant checker
			var serializer = new RuntimeModelSerializer();
			serializer.Serialize(model, !hazard);

			Func<AnalysisModel> createModel = () => new ActivationMinimalExecutedModel(serializer.Load, Configuration.SuccessorCapacity);
			_invariantChecker = new InvariantChecker(createModel, message => OutputWritten?.Invoke(message), Configuration, formulaIndex: 0);
			_result = new Result(model, suppressedFaults, forcedFaults, Heuristics);

			// remember all safe sets of current cardinality - we need them to generate the next power set level
			var currentSafe = new HashSet<FaultSet>();

			// We check fault sets by increasing cardinality; this is, we check the empty set first, then
			// all singleton sets, then all sets with two elements, etc. We don't check sets that we
			// know are going to be critical sets due to monotonicity
			for (var cardinality = 0; cardinality <= allFaults.Length; ++cardinality)
			{
				// Generate the sets for the current level that we'll have to check
				var sets = GeneratePowerSetLevel(cardinality, allFaults, currentSafe);
				currentSafe.Clear();

				// Remove all sets that conflict with the forced or suppressed faults; these sets are considered to be safe.
				// If no sets remain, skip to the next level
				sets = RemoveInvalidSets(sets, currentSafe);
				if (sets.Count == 0)
					continue;

				// Abort if we've exceeded the maximum fault set cardinality; doing the check here allows us
				// to report the analysis as complete if the maximum cardinality is never reached
				if (cardinality > maxCardinality)
				{
					isComplete = false;
					break;
				}

				if (cardinality == 0)
					ConsoleHelpers.WriteLine("Checking the empty fault set...");
				else
					ConsoleHelpers.WriteLine($"Checking {sets.Count} sets of cardinality {cardinality}...");

				// use heuristics
				var setsToCheck = new List<FaultSet>(sets);
				foreach (var heuristic in Heuristics)
					heuristic.Augment(setsToCheck);

				// We have to check each set - heuristics may add further during the loop
				while (setsToCheck.Count > 0)
				{
					var set = setsToCheck[setsToCheck.Count - 1];

					var isCurrentLevel = sets.Remove(set); // returns true if set was actually contained
					setsToCheck.RemoveAt(setsToCheck.Count - 1);

					// for current level, we already know the set is valid
					bool isValid = isCurrentLevel || !IsInvalid(set);

					bool isSafe = true;
					if (isValid)
						isSafe = CheckSet(set, nondeterministicFaults, allFaults, cardinality);

					if (isSafe && isCurrentLevel)
						currentSafe.Add(set);

					// inform heuristics about result and give them the opportunity to add further sets
					foreach (var heuristic in Heuristics)
						heuristic.Update(setsToCheck, set, isSafe);
				}

				// in case heuristics removed a set (they shouldn't)
				foreach (var set in sets)
				{
					var isSafe = CheckSet(set, nondeterministicFaults, allFaults, cardinality);
					if (isSafe)
						currentSafe.Add(set);
				}
			}

			// Reset the nondeterministic faults so as to not influence subsequent analyses
			foreach (var fault in nondeterministicFaults)
				fault.Activation = Activation.Nondeterministic;

			// due to heuristics usage, we may have informatiuon on non-minimal critical sets
			var minimalCritical = RemoveNonMinimalCriticalSets();

			_result.IsComplete = isComplete;
			_result.Time = stopwatch.Elapsed;
			_result.SetResult(minimalCritical, _checkedSets, _counterExamples, _exceptions);

			return _result;
		}

		private void Reset(ModelBase model)
		{
			_safeSets = new FaultSetCollection(model.Faults.Length);
			_criticalSets = new FaultSetCollection(model.Faults.Length);
			_checkedSets.Clear();
			_counterExamples.Clear();
			_exceptions.Clear();
		}

		private HashSet<FaultSet> RemoveNonMinimalCriticalSets()
		{
			var minimal = _criticalSets.GetMinimalSets();

			foreach (var set in _criticalSets)
			{
				if (!minimal.Contains(set))
				{
					_exceptions.Remove(set);
					_counterExamples.Remove(set);
				}
			}

			return minimal;
		}

		private bool CheckSet(FaultSet set, Fault[] nondeterministicFaults, Fault[] allFaults, int cardinality)
		{
			var isHeuristic = cardinality != set.Cardinality;
			if (isHeuristic)
				_result.HeuristicSuggestionCount++;

			var isSafe = true;

			// check if set is trivially safe or critical
			// (do not add to safeSets / criticalSets if so, in order to keep them small)
			if (IsTriviallySafe(set))
			{
				_result.TrivialChecksCount++;
				if (isHeuristic)
					_result.HeuristicTrivialCount++;

				// do not add to safeSets: all subsets are subsets of safeSet as well
				return true;
			}

			if (IsTriviallyCritical(set))
			{
				_result.TrivialChecksCount++;
				if (isHeuristic)
					_result.HeuristicTrivialCount++;

				// do not add to criticalSets: non-minimal, and all supersets are supersets of criticalSet as well
				return false;
			}

			// if configured to do so, check with forced fault activation
			if (FaultActivationBehaviour == FaultActivationBehaviour.ForceOnly
				|| FaultActivationBehaviour == FaultActivationBehaviour.ForceThenFallback)
				isSafe = CheckSet(set, nondeterministicFaults, allFaults, cardinality, Activation.Forced, isHeuristic);

			if (isSafe && FaultActivationBehaviour == FaultActivationBehaviour.ForceThenFallback)
				ConsoleHelpers.WriteLine("    Checking again with nondeterministic activation...");

			// check with nondeterministic fault activation
			if (isSafe && FaultActivationBehaviour != FaultActivationBehaviour.ForceOnly)
				isSafe = CheckSet(set, nondeterministicFaults, allFaults, cardinality, Activation.Nondeterministic, isHeuristic);

			if (isSafe) // remember non-trivially safe sets to avoid checking their subsets
			{
				_safeSets.Add(set);

				if (isHeuristic)
					_result.HeuristicNonTrivialSafeCount++;
			}

			return isSafe;
		}

		private bool CheckSet(FaultSet set, Fault[] nondeterministicFaults, Fault[] allFaults,
							  int cardinality, Activation activationMode, bool isHeuristic)
		{
			// Enable or disable the faults that the set represents
			set.SetActivation(nondeterministicFaults, activationMode);

			foreach (var model in _invariantChecker.AnalyzedModels.Cast<ExecutedModel>())
				model.ChangeFaultActivations(GetUpdateFaultActivations(allFaults));

			var heuristic = set.Cardinality == cardinality ? String.Empty : "[heuristic]";

			try
			{
				var result = _invariantChecker.Check();

				if (!result.FormulaHolds)
				{
					if (!isHeuristic)
						ConsoleHelpers.WriteLine($"    {heuristic} critical:  {{ {set.ToString(allFaults)} }}", ConsoleColor.DarkRed);

					_criticalSets.Add(set);
				}
				else if (isHeuristic)
				{
					ConsoleHelpers.WriteLine($"    {heuristic} safe:  {{ {set.ToString(allFaults)} }}", ConsoleColor.Blue);
				}

				_checkedSets.Add(set);

				if (result.CounterExample != null)
					_counterExamples.Add(set, result.CounterExample);

				return result.FormulaHolds;
			}
			catch (AnalysisException e)
			{
				ConsoleHelpers.WriteLine($"    {heuristic} critical:  {{ {set.ToString(allFaults)} }} [exception thrown]", ConsoleColor.DarkRed);
				Console.WriteLine(e.InnerException);

				_checkedSets.Add(set);
				_criticalSets.Add(set);
				_exceptions.Add(set, e.InnerException);

				if (e.CounterExample != null)
					_counterExamples.Add(set, e.CounterExample);
				return false;
			}
		}

		private bool IsTriviallyCritical(FaultSet faultSet)
		{
			return _criticalSets.ContainsSubsetOf(faultSet);
		}

		private bool IsTriviallySafe(FaultSet faultSet)
		{
			return _safeSets.ContainsSupersetOf(faultSet);
		}

		/// <summary>
		///   Creates a function that determines the activation state of a fault.
		/// </summary>
		private static Func<Fault, Activation> GetUpdateFaultActivations(Fault[] faults)
		{
			return fault =>
			{
				Assert.That(fault != null && fault.IsUsed, "Invalid fault.");
				Assert.InRange(fault.Identifier, faults);

				return faults[fault.Identifier].Activation;
			};
		}

		/// <summary>
		///   Generates a level of the power set.
		/// </summary>
		/// <param name="cardinality">The cardinality of the sets that should be generated.</param>
		/// <param name="faults">The fault set the power set is generated for.</param>
		/// <param name="previousSafe">The set of safe sets generated at the previous level.</param>
		private static HashSet<FaultSet> GeneratePowerSetLevel(int cardinality, Fault[] faults, HashSet<FaultSet> previousSafe)
		{
			var result = new HashSet<FaultSet>();

			switch (cardinality)
			{
				case 0:
					// There is only the empty set with a cardinality of 0
					result.Add(new FaultSet());
					break;
				case 1:
					// We have to kick things off by explicitly generating the singleton sets; at this point,
					// we know that there are no further minimal critical sets if the empty set is already critical.
					if (previousSafe.Count > 0)
					{
						foreach (var fault in faults)
							result.Add(new FaultSet(fault));
					}
					break;
				default:
					// We now generate the sets with the requested cardinality based on the sets from the previous level
					// which had a cardinality that is one less than the sets we're going to generate now. The basic
					// idea is that we create the union between all safe sets and all singleton sets and discard
					// the ones we don't want, while avoiding duplicate generation of sets.

					var setsToRemove = new HashSet<FaultSet>();
					for (var i = 0; i < faults.Length; ++i)
					{
						var fault = faults[i];
						setsToRemove.Clear();

						foreach (var safeSet in previousSafe)
						{
							// avoid duplicate set generation
							if (safeSet.Contains(fault))
							{
								setsToRemove.Add(safeSet);
								continue;
							}

							var set = safeSet.Add(fault);

							// set is trivially critical iff one of the direct subsets is not safe (i.e. critical)
							// * the faults faults[0], ..., faults[i-1] are not definitely not contained in set (see above)
							// * faults[i] is definitely in set, but set.Remove(faults[i]) == safeSet and is thus safe.
							var isTriviallyCritical = false;
							for (var j = i + 1; j < faults.Length; ++j)
							{
								var f = faults[j];
								if (set.Contains(f) && !previousSafe.Contains(set.Remove(f)))
								{
									isTriviallyCritical = true;
									break;
								}
							}

							// Check if the newly generated set is a super set of any critical sets;
							// if so, discard it
							if (!isTriviallyCritical)
								result.Add(set);
						}

						// all supersets of sets in setsToRemove have either
						// been previously generated or are critical
						previousSafe.ExceptWith(setsToRemove);

						// if no more sets in previousSafe, further iterations are pointless
						if (previousSafe.Count == 0)
							break;
					}
					break;
			}

			return result;
		}

		/// <summary>
		///   Removes all invalid sets from <paramref name="sets" /> that conflict with either <see cref="_suppressedSet" /> or
		///   <see cref="_forcedSet" />.
		/// </summary>
		private HashSet<FaultSet> RemoveInvalidSets(HashSet<FaultSet> sets, HashSet<FaultSet> currentSafe)
		{
			if (_suppressedSet.IsEmpty && _forcedSet.IsEmpty)
				return sets;

			var validSets = new HashSet<FaultSet>();
			foreach (var set in sets)
			{
				if (IsInvalid(set))
					currentSafe.Add(set);
				else
					validSets.Add(set);
			}

			return validSets;
		}

		private bool IsInvalid(FaultSet set)
		{
			// The set must contain all forced faults, hence it must be a superset of those
			// The set is not allowed to contain any suppressed faults, hence the intersection must be empty
			if (!_forcedSet.IsSubsetOf(set) || !_suppressedSet.GetIntersection(set).IsEmpty)
			{
				_safeSets.Add(set);
				return true;
			}

			return false;
		}

		/// <summary>
		///   Represents the result of a safety analysis.
		/// </summary>
		public class Result
		{
			/// <summary>
			///   Initializes a new instance.
			/// </summary>
			/// <param name="model">The <see cref="Model" /> instance the safety analysis was conducted for.</param>
			/// <param name="suppressedFaults">The faults whose activations have been completely suppressed during analysis.</param>
			/// <param name="forcedFaults">The faults whose activations have been forced during analysis.</param>
			/// <param name="heuristics">The heuristics that are used during the analysis.</param>
			internal Result(ModelBase model, IEnumerable<Fault> suppressedFaults, IEnumerable<Fault> forcedFaults,
							IEnumerable<IFaultSetHeuristic> heuristics)
			{
				Model = model;
				SuppressedFaults = suppressedFaults;
				ForcedFaults = forcedFaults;
				Heuristics = heuristics.ToArray(); // make a copy so that later changes to the heuristics don't affect the results
			}

			/// <summary>
			///   Gets the faults whose activations have been completely suppressed during analysis.
			/// </summary>
			public IEnumerable<Fault> SuppressedFaults { get; }

			/// <summary>
			///   Gets the faults whose activations have been forced during analysis.
			/// </summary>
			public IEnumerable<Fault> ForcedFaults { get; }

			/// <summary>
			///   Gets the minimal critical sets, each critical set containing the faults that potentially result in the occurrence of a
			///   hazard.
			/// </summary>
			public ISet<ISet<Fault>> MinimalCriticalSets { get; private set; }

			/// <summary>
			///   Gets all of the fault sets that were checked for criticality. Some sets might not have been checked as they were known to
			///   be critical sets due to the monotonicity of the critical set property.
			/// </summary>
			public ISet<ISet<Fault>> CheckedSets { get; private set; }

			/// <summary>
			///   Gets the exception that has been thrown during the analysis, if any.
			/// </summary>
			public IDictionary<ISet<Fault>, Exception> Exceptions { get; private set; }

			/// <summary>
			///   Gets the faults that have been checked.
			/// </summary>
			public IEnumerable<Fault> Faults => Model.Faults;

			/// <summary>
			///   Gets the counter examples that were generated for the critical fault sets.
			/// </summary>
			public IDictionary<ISet<Fault>, CounterExample> CounterExamples { get; private set; }

			/// <summary>
			///   Gets a value indicating whether the analysis might is complete, i.e., all fault sets have been checked for criticality.
			/// </summary>
			public bool IsComplete { get; internal set; }

			/// <summary>
			///   Gets the <see cref="Model" /> instance the safety analysis was conducted for.
			/// </summary>
			public ModelBase Model { get; }

			/// <summary>
			///   Gets the time it took to complete the analysis.
			/// </summary>
			public TimeSpan Time { get; internal set; }

			/// <summary>
			///   Gets the heuristics that were used during analysis.
			/// </summary>
			public IEnumerable<IFaultSetHeuristic> Heuristics { get; }

			/// <summary>
			///   The total number of fault sets suggested by the heuristics.
			/// </summary>
			public int HeuristicSuggestionCount { get; internal set; }

			/// <summary>
			///   The number of sets suggested by a heuristic that were not trivially safe.
			/// </summary>
			public int HeuristicNonTrivialSafeCount { get; internal set; }

			/// <summary>
			///   The number of sets suggested by a heuristic that were trivially safe or critical.
			/// </summary>
			public int HeuristicTrivialCount { get; internal set; }

			/// <summary>
			///   The number of trivial checks that have been performed.
			/// </summary>
			public int TrivialChecksCount { get; internal set; }

			/// <summary>
			///   Initializes a new instance.
			/// </summary>
			/// <param name="criticalSets">The minimal critical sets.</param>
			/// <param name="checkedSets">The sets that have been checked.</param>
			/// <param name="counterExamples">The counter examples that were generated for the critical fault sets.</param>
			/// <param name="exceptions">The exceptions that have been thrown during the analysis.</param>
			internal void SetResult(HashSet<FaultSet> criticalSets, HashSet<FaultSet> checkedSets,
									Dictionary<FaultSet, CounterExample> counterExamples, Dictionary<FaultSet, Exception> exceptions)
			{
				var knownFaultSets = new Dictionary<FaultSet, ISet<Fault>>();

				MinimalCriticalSets = Convert(knownFaultSets, criticalSets);
				CheckedSets = Convert(knownFaultSets, checkedSets);
				CounterExamples = counterExamples.ToDictionary(pair => Convert(knownFaultSets, pair.Key), pair => pair.Value);
				Exceptions = exceptions.ToDictionary(pair => Convert(knownFaultSets, pair.Key), pair => pair.Value);
			}

			/// <summary>
			///   Converts the integer-based sets to a sets of fault sets.
			/// </summary>
			private ISet<ISet<Fault>> Convert(Dictionary<FaultSet, ISet<Fault>> knownSets, HashSet<FaultSet> sets)
			{
				var result = new HashSet<ISet<Fault>>(ReferenceEqualityComparer<ISet<Fault>>.Default);

				foreach (var set in sets)
					result.Add(Convert(knownSets, set));

				return result;
			}

			/// <summary>
			///   Converts the integer-based set to a set faults.
			/// </summary>
			private ISet<Fault> Convert(Dictionary<FaultSet, ISet<Fault>> knownSets, FaultSet set)
			{
				ISet<Fault> faultSet;
				if (knownSets.TryGetValue(set, out faultSet))
					return faultSet;

				faultSet = new HashSet<Fault>(set.ToFaultSequence(Model.Faults));
				knownSets.Add(set, faultSet);

				return faultSet;
			}

			/// <summary>
			/// 
			/// </summary>
			/// <param name="directory">The directory the generated counter examples should be written to.</param>
			/// <param name="clearFiles">Indicates whether all files in the directory should be cleared before saving the counter examples.</param>
			public void SaveCounterExamples(string directory, bool clearFiles = true)
			{
				Requires.NotNullOrWhitespace(directory, nameof(directory));

				if (clearFiles && Directory.Exists(directory))
				{
					foreach (var file in new DirectoryInfo(directory).GetFiles())
						file.Delete();
				}

				foreach (var pair in CounterExamples)
				{
					var fileName = String.Join("_", pair.Key.Select(f => f.Name));
					if (String.IsNullOrWhiteSpace(fileName))
						fileName = "emptyset";

					pair.Value.Save(Path.Combine(directory, $"{fileName}{CounterExample.FileExtension}"));
				}
			}

			/// <summary>
			///   Returns a string representation of the minimal critical fault sets.
			/// </summary>
			public override string ToString()
			{
				var builder = new StringBuilder();
				var percentage = CheckedSets.Count / (double)(1L << Faults.Count()) * 100;

				builder.AppendLine();
				builder.AppendLine("=======================================================================");
				builder.AppendLine("=======      Deductive Cause Consequence Analysis: Results      =======");
				builder.AppendLine("=======================================================================");
				builder.AppendLine();

				if (Exceptions.Any())
				{
					builder.AppendLine("*** Warning: Unhandled exceptions have been thrown during the analysis. ***");
					builder.AppendLine();
				}

				if (!IsComplete)
				{
					builder.AppendLine("*** Warning: Analysis might be incomplete; not all fault sets have been checked. ***");
					builder.AppendLine();
				}

				Func<IEnumerable<Fault>, string> getFaultString =
					faults => String.Join(", ", faults.Select(fault => fault.Name).OrderBy(name => name));

				builder.AppendLine($"Elapsed Time: {Time}");
				builder.AppendLine($"Fault Count: {Faults.Count()}");
				builder.AppendLine($"Faults: {getFaultString(Faults)}");

				if (ForcedFaults.Any())
					builder.AppendLine($"Forced Faults: {getFaultString(ForcedFaults)}");

				if (SuppressedFaults.Any())
					builder.AppendLine($"Suppressed Faults: {getFaultString(SuppressedFaults)}");

				builder.AppendLine();
				builder.AppendLine($"Checked Fault Sets: {CheckedSets.Count} ({percentage:F0}% of all fault sets)");
				builder.AppendLine($"Minimal Critical Sets: {MinimalCriticalSets.Count}");
				builder.AppendLine();

				var i = 1;
				foreach (var criticalSet in MinimalCriticalSets)
				{
					builder.AppendFormat("   ({1}) {{ {0} }}", String.Join(", ", criticalSet.Select(fault => fault.Name).OrderBy(name => name)), i++);

					Exception e;
					if (Exceptions.TryGetValue(criticalSet, out e))
					{
						builder.AppendLine();
						builder.Append(
							$"    An unhandled exception of type {e.GetType().FullName} was thrown while checking the fault set: {e.Message}");
					}

					builder.AppendLine();
				}

				var heuristicCount = Heuristics.Count();
				if (heuristicCount != 0)
				{
					builder.AppendLine();

					if (HeuristicSuggestionCount == 0)
						builder.AppendLine("No suggestions were made by the heuristics.");
					else
					{
						var nonTriviallyCritical = HeuristicSuggestionCount - HeuristicNonTrivialSafeCount - HeuristicTrivialCount;
						var percentageTrivial = HeuristicTrivialCount / (double)(HeuristicSuggestionCount) * 100;
						var percentageNonTrivialSafe = HeuristicNonTrivialSafeCount / (double)(HeuristicSuggestionCount) * 100;
						var percentageNonTrivialCritical = nonTriviallyCritical / (double)(HeuristicSuggestionCount) * 100;

						builder.AppendLine($"Of {HeuristicSuggestionCount} fault sets suggested by {heuristicCount} heuristics");
						builder.AppendLine($"    {HeuristicTrivialCount} ({percentageTrivial:F0}%) were trivially safe or trivially critical,");
						builder.AppendLine($"    {HeuristicNonTrivialSafeCount} ({percentageNonTrivialSafe:F0}%) were non-trivially safe, and");
						builder.AppendLine($"    {nonTriviallyCritical} ({percentageNonTrivialCritical:F0}%) were non-trivially critical.");
						builder.AppendLine($"In total, {TrivialChecksCount} trivial checks were performed.");
					}
				}

				return builder.ToString();
			}
		}
	}
}
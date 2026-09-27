/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Map;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.InfiniteFixpointRepetition;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskStringIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaFloydHoareValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager.BspmResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBouncer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStyle;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TermcompProofBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.InterpolationPreferenceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public abstract class AbstractBuchiCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	protected final String mIdentifier;
	protected final String mTaskFilename;
	protected final boolean mIsConcurrent;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int mIteration;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected NestedLassoRun<L, IPredicate> mCounterexample;
	protected final PredicateFactoryForInterpolantAutomata mDefaultStateFactory;
	protected final BuchiCegarLoopBenchmarkGenerator mBenchmarkGenerator;
	protected final PredicateFactory mPredicateFactory;
	protected boolean mIsSemiDeterministic;
	protected boolean mUseDoubleDeckers;

	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences mPref;

	private final BuchiAutomizerModuleDecompositionBenchmark mMDBenchmark;

	/**
	 * Construct a termination proof in the form that is required for the Termination Competition.
	 * http://termination-portal.org/wiki/Termination_Competition This proof is finally print in the console output and
	 * can be huge.
	 */
	private final boolean mConstructTermcompProof;
	private final TermcompProofBenchmark mTermcompProofBenchmark;

	private final InterpolationTechnique mInterpolation;

	private BackwardCoveringInformation mBci;

	private final CfgSmtToolkit mCsToolkitWithoutRankVars;
	private final CfgSmtToolkit mCsToolkitWithRankVars;

	private final BinaryStatePredicateManager mBinaryStatePredicateManager;

	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of of the program.
	 */
	private A mAbstraction;

	private final StrategyFactory<L> mRefinementStrategyFactory;
	private final TaskIdentifier mTaskIdentifier;
	private final BuchiInterpolantAutomatonBuilder<L> mInterpolantAutomatonBuilder;
	private final List<BuchiInterpolantAutomatonConstructionStyle> mBiaConstructionStyleSequence;

	private final Minimization mAutomataMinimizationAfterFeasibilityBasedRefinement;
	private final Minimization mAutomataMinimizationAfterRankBasedRefinement;

	public AbstractBuchiCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz, final A initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		assert services != null;
		mIdentifier = icfg.getIdentifier();
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIdentifier);
		mTaskFilename = ILocation.getAnnotation(icfg).getFileName();
		mIsConcurrent = IcfgUtils.isConcurrent(icfg);

		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMDBenchmark = new BuchiAutomizerModuleDecompositionBenchmark(mServices.getBacktranslationService());
		mPredicateFactory = predicateFactory;
		mCsToolkitWithoutRankVars = icfg.getCfgSmtToolkit();
		mCsToolkitWithRankVars = rankVarConstructor.getCsToolkitWithRankVariables();
		mBinaryStatePredicateManager = new BinaryStatePredicateManager(mCsToolkitWithRankVars, predicateFactory,
				rankVarConstructor.getUnseededVariable(), rankVarConstructor.getOldRankVariables(), mServices,
				SIMPLIFICATION_TECHNIQUE);
		mBenchmarkGenerator = benchmarkGenerator;
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		mPref = taPrefs;
		mDefaultStateFactory = new PredicateFactoryForInterpolantAutomata(mCsToolkitWithRankVars.getManagedScript(),
				predicateFactory, mPref.getHoareSettings().computeHoareAnnotation());

		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mInterpolation = baPref.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				InterpolationTechnique.class);
		mUseDoubleDeckers = !baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_IGNORE_DOWN_STATES);

		InterpolationPreferenceChecker.check(Activator.PLUGIN_NAME, mInterpolation, mServices);
		mConstructTermcompProof = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CONSTRUCT_TERMCOMP_PROOF);
		mTermcompProofBenchmark = mConstructTermcompProof ? new TermcompProofBenchmark(mServices) : null;

		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(mServices, mPref, mInterpolation, SIMPLIFICATION_TECHNIQUE,
						mCsToolkitWithoutRankVars, mPredicateFactory, icfg);
		mRefinementStrategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs, icfg,
				mPredicateFactory, mDefaultStateFactory, transitionClazz);
		mAbstraction = initialAbstraction;
		mInterpolantAutomatonBuilder = new BuchiInterpolantAutomatonBuilder<>(mServices, mCsToolkitWithRankVars,
				SIMPLIFICATION_TECHNIQUE, predicateFactory, mInterpolation);
		mBiaConstructionStyleSequence =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BIA_CONSTRUCTION_STRATEGY,
						BuchiInterpolantAutomatonConstructionStrategy.class).getBiaConstrucionStyleSequence(baPref);
		mAutomataMinimizationAfterFeasibilityBasedRefinement = baPref.getEnum(
				BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT,
				Minimization.class);
		mAutomataMinimizationAfterRankBasedRefinement = baPref.getEnum(
				BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT,
				Minimization.class);
	}

	/**
	 * Check if {@code abstraction} is empty (i.e. does not accept any word).
	 *
	 * @param abstraction
	 *            The current abstraction
	 * @return true iff {@code abstraction} is empty
	 * @throws AutomataLibraryException
	 */
	protected abstract boolean isAbstractionEmpty(A abstraction) throws AutomataLibraryException;

	/**
	 * Refine the given {@code abstraction} i.e. calculate the difference with the given {@code interpolantAutomaton}
	 * for the case where we detected that a finite prefix of the lasso-shaped counterexample is infeasible. In this
	 * case the module (i.e., the subtrahend {@code interpolantAutomaton} of the difference) will be a weak Büchi
	 * automaton (Büchi automaton where set of final states is a trap). In fact, the module will have only a single
	 * accepting state that is labeled with "false" and that has a self-loop for every letter.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param interpolantAutomaton
	 *            The subtrahend of the difference, a weak Büchi automaton
	 * @return The new refined abstraction
	 * @throws AutomataLibraryException
	 */
	protected abstract A refineFinite(A abstraction,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException;

	/**
	 * Refine the given {@code abstraction} i.e. calculate the difference with the given {@code interpolantAutomaton}
	 * for the case where we detected that the lasso that is represented by the automaton can only be taken finitely
	 * often.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param interpolantAutomaton
	 *            The subtrahend of the difference
	 * @return The new refined abstraction
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A refineBuchi(A abstraction,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException;

	/**
	 * Reduce the size of the given {@code abstraction} w.r.t the given minimization technique
	 * {@code automataMinimization}.
	 *
	 * @param abstraction
	 *            The current abstraction
	 * @param automataMinimization
	 *            The minimization technique
	 * @return A new potentially smaller automaton than {@code abstraction} that still recognizes the same language
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A reduceAbstractionSize(final A abstraction, final Minimization automataMinimization)
			throws AutomataOperationCanceledException;

	public final BuchiCegarLoopResult<L> runCegarLoop() throws IOException {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.getHoareSettings().getHoarePositions());
		mLogger.info("Compute interpolants for " + mInterpolation);
		mLogger.info("Backedges is " + mPref.interpolantAutomaton());
		mLogger.info("Determinization is " + mPref.interpolantAutomatonEnhancement());
		mLogger.info("Difference is " + mPref.differenceSenwa());
		mLogger.info("Minimize is " + mPref.getMinimization());

		mIteration = 0;
		final String name = getClass().getSimpleName();
		mLogger.info("======== Iteration %s == of CEGAR loop == %s ========", mIteration, name);

		if (mPref.dumpAutomata()) {
			writeAutomatonToFile(mAbstraction, "BuchiInitialAbstraction");
		}
		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionEmpty(mAbstraction);
		} catch (final AutomataLibraryException e1) {
			mLogger.warn("Verification cancelled");
			mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
			return BuchiCegarLoopResult.constructTimeoutResult(new ToolchainCanceledException(e1.getClassOfThrower()),
					mMDBenchmark, mTermcompProofBenchmark);
		}
		if (initalAbstractionCorrect) {
			mMDBenchmark.reportNoRemainderModule();
			return BuchiCegarLoopResult.constructTerminatingResult(mMDBenchmark, mTermcompProofBenchmark);
		}

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			mLogger.info("======== Iteration %s ============", mIteration);
			mBenchmarkGenerator.announceNextIteration();
			boolean abstractionCorrect;
			try {
				abstractionCorrect = isAbstractionEmpty(mAbstraction);
			} catch (final AutomataLibraryException e1) {
				mLogger.warn("Verification cancelled");
				reportRemainderModule(false);
				return BuchiCegarLoopResult.constructTimeoutResult(
						new ToolchainCanceledException(e1.getClassOfThrower()), mMDBenchmark, mTermcompProofBenchmark);
			}
			if (abstractionCorrect) {
				mMDBenchmark.reportNoRemainderModule();
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportNoRemainderModule();
				}
				return BuchiCegarLoopResult.constructTerminatingResult(mMDBenchmark, mTermcompProofBenchmark);
			}

			LassoCheck<L> lassoCheck;
			try {
				final TaskIdentifier taskIdentifier = new SubtaskIterationIdentifier(mTaskIdentifier, mIteration);
				mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
				final String identifier = mIdentifier + "_Iteration" + mIteration;
				lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
						mCsToolkitWithoutRankVars.getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
						mCounterexample, this::getControlConfiguration, identifier, mServices, SIMPLIFICATION_TECHNIQUE,
						mRefinementStrategyFactory, mAbstraction, taskIdentifier, mBenchmarkGenerator);
				if (lassoCheck.getLassoCheckResult().getContinueDirective() == ContinueDirective.REPORT_UNKNOWN) {
					// if result was unknown, then try again but this time add one
					// iteration of the loop to the stem.
					// This allows us to verify Vincent's coolant examples
					final TaskIdentifier unwindingTaskIdentifier =
							new SubtaskAdditionalLoopUnwinding(taskIdentifier, 1);
					mLogger.info("Result of lasso check was UNKNOWN. I will concatenate loop to stem and try again.");
					final NestedRun<L, IPredicate> newStem =
							mCounterexample.getStem().concatenate(mCounterexample.getLoop());
					mCounterexample = new NestedLassoRun<>(newStem, mCounterexample.getLoop());
					lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
							mCsToolkitWithoutRankVars.getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
							mCounterexample, this::getControlConfiguration, identifier, mServices,
							SIMPLIFICATION_TECHNIQUE, mRefinementStrategyFactory, mAbstraction, unwindingTaskIdentifier,
							mBenchmarkGenerator);
				}
			} catch (final ToolchainCanceledException e) {
				final int traceHistogramMaxStem =
						new HistogramOfIterable<>(mCounterexample.getStem().getWord()).getMax();
				final int traceHistogramMaxLoop =
						new HistogramOfIterable<>(mCounterexample.getLoop().getWord()).getMax();
				final String taskDescription =
						"analyzing lasso (" + "stem: length " + mCounterexample.getStem().getLength() + " TraceHistMax "
								+ traceHistogramMaxStem + " " + "loop: length " + mCounterexample.getLoop().getLength()
								+ " TraceHistMax " + traceHistogramMaxLoop + ")";
				e.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				return BuchiCegarLoopResult.constructTimeoutResult(e, mMDBenchmark, mTermcompProofBenchmark);
			} finally {
				mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
			}

			final ContinueDirective cd = lassoCheck.getLassoCheckResult().getContinueDirective();
			mBenchmarkGenerator.reportLassoAnalysis(lassoCheck);
			// One file per synthesis scope, never merged: the whole lasso always, the loop alone when it ran.
			exportLassoTraceReport(mIteration, lassoCheck, false);
			if (lassoCheck.getLoopDump().hasRun()) {
				exportLassoTraceReport(mIteration, lassoCheck, true);
			}
			try {
				switch (cd) {
				case REFINE_BOTH:
					mAbstraction = refineFiniteInternal(refineBuchiInternal(lassoCheck), lassoCheck);
					break;
				case REFINE_FINITE:
					mAbstraction = refineFiniteInternal(mAbstraction, lassoCheck);
					break;
				case REFINE_BUCHI:
					mAbstraction = refineBuchiInternal(lassoCheck);
					break;
				case REPORT_UNKNOWN:
				case REPORT_NONTERMINATION:
					// Ignore the insufficient thread locations in the counterexample
					final var inUseLocs = new HashSet<>(
							mCsToolkitWithoutRankVars.getConcurrencyInformation().getInUseErrorNodeMap().values());
					final NestedWord<L> stem = getWordWithoutLocs(mCounterexample.getStem(), inUseLocs);
					final NestedWord<L> loop = getWordWithoutLocs(mCounterexample.getLoop(), inUseLocs);
					if (cd == ContinueDirective.REPORT_NONTERMINATION && getOverapproximations().isEmpty()) {
						reportRemainderModule(true);
						// The loop is empty, i.e. it contains only self-loops in the insufficient thread locations.
						if (loop.length() == 0) {
							return BuchiCegarLoopResult.constructInsufficientThreadsResult();
						}
						return BuchiCegarLoopResult.constructNonTerminatingResult(stem, loop,
								lassoCheck.getNonTerminationArgument(), mMDBenchmark, mTermcompProofBenchmark);
					}
					reportRemainderModule(false);
					return BuchiCegarLoopResult.constructUnknownResult(stem, loop, getOverapproximations(),
							mMDBenchmark, mTermcompProofBenchmark);
				default:
					throw new AssertionError("impossible case");
				}
				mLogger.info("Abstraction has " + mAbstraction.sizeInformation());

				if (mPref.dumpAutomata()) {
					writeAutomatonToFile(mAbstraction, mIteration, "BuchiAbstraction");
				}

			} catch (final AutomataLibraryException e) {
				return BuchiCegarLoopResult.constructTimeoutResult(
						new ToolchainCanceledException(e.getClassOfThrower()), mMDBenchmark, mTermcompProofBenchmark);
			} catch (final ToolchainCanceledException e) {
				return BuchiCegarLoopResult.constructTimeoutResult(e, mMDBenchmark, mTermcompProofBenchmark);
			}
		}
		return BuchiCegarLoopResult.constructTimeoutResult(
				new ToolchainCanceledException(getClass(), "exceeding the number of iterations"), mMDBenchmark,
				mTermcompProofBenchmark);
	}

	protected String getDumpPath(final boolean besideInputFile, final String directory, final String filename,
			final String suffix) {
		return TraceAbstractionUtils.constructDumpPath(besideInputFile, mTaskFilename, directory, filename, null,
				suffix);
	}

	protected void writeAutomatonToFile(final IAutomaton<L, IPredicate> automaton, final TaskIdentifier tid,
			final String message) {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.DumpTime);
		final String fullAutomataPath = getDumpPath(mPref.dumpAutomataBesideFile(), mPref.dumpAutomataDirectory(),
				mPref.dumpAutomataFilename(), tid.toString());
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices),
				TraceAbstractionUtils.determineAutomatonName(automaton), fullAutomataPath, mPref.dumpAutomataFormat(),
				message, automaton);
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.DumpTime);
	}

	protected void writeAutomatonToFile(final IAutomaton<L, IPredicate> automaton, final int iteration,
			final String suffix, final String message) {
		final TaskIdentifier tid = new SubtaskStringIdentifier(new SubtaskIterationIdentifier(null, iteration), suffix);
		writeAutomatonToFile(automaton, tid, message);
	}

	protected void writeAutomatonToFile(final IAutomaton<L, IPredicate> automaton, final int iteration,
			final String suffix) {
		writeAutomatonToFile(automaton, iteration, suffix, "");
	}

	protected void writeAutomatonToFile(final IAutomaton<L, IPredicate> automaton, final String suffix) {
		final TaskIdentifier tid = new SubtaskStringIdentifier(null, suffix);
		writeAutomatonToFile(automaton, tid, "");
	}

	@SuppressWarnings("unchecked")
	private static <L extends IIcfgTransition<?>> NestedWord<L> getWordWithoutLocs(final NestedRun<L, ?> run,
			final Set<IcfgLocation> ignoredLocs) {
		if (ignoredLocs.isEmpty()) {
			return run.getWord();
		}
		final L[] letters = (L[]) run.getWord().asList().stream().filter(x -> !ignoredLocs.contains(x.getTarget()))
				.toArray(IIcfgTransition<?>[]::new);
		return NestedWord.nestedWord(new Word<>(letters));
	}

	private A refineFiniteInternal(final A abstraction, final LassoCheck<L> lassoCheck)
			throws AutomataLibraryException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final var traceCheck = constructRefinementEngineResult(lassoCheck);
		final NestedWordAutomaton<L, IPredicate> interpolAutomaton = traceCheck.getInfeasibilityProof();

		final IHoareTripleChecker htc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, traceCheck.getPredicateUnifier());

		final DeterministicInterpolantAutomaton<L> determinized = new DeterministicInterpolantAutomaton<>(mServices,
				mCsToolkitWithRankVars, htc, interpolAutomaton, traceCheck.getPredicateUnifier(), false, false);
		final A result;
		try {
			result = reduceAbstractionSize(refineFinite(abstraction, determinized),
					mAutomataMinimizationAfterFeasibilityBasedRefinement);
		} catch (final AutomataOperationCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		} catch (final ToolchainCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		}
		determinized.switchToReadonlyMode();
		if (mPref.dumpAutomata()) {
			writeAutomatonToFile(interpolAutomaton, mIteration, "BuchiInterpolantAutomatonUsedInRefinementAfter");
		}
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportFiniteModule(mIteration, interpolAutomaton);
		}
		mMDBenchmark.reportTrivialModule(mIteration, interpolAutomaton.size());
		assert NwaFloydHoareValidityCheck.forInterpolantAutomaton(mServices, mCsToolkitWithRankVars.getManagedScript(),
				new IncrementalHoareTripleChecker(mCsToolkitWithRankVars, false), traceCheck.getPredicateUnifier(),
				interpolAutomaton, true).getResult();
		mBenchmarkGenerator.addEdgeCheckerData(htc.getStatistics());
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		return result;
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			constructRefinementEngineResult(final LassoCheck<L> lassoCheck) {
		final var lcr = lassoCheck.getLassoCheckResult();
		if (lassoCheck.getLassoCheckResult().getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
			// if both (stem and loop) are infeasible we take the smaller one.
			final int stemSize = mCounterexample.getStem().getLength();
			final int loopSize = mCounterexample.getLoop().getLength();
			if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE && loopSize <= stemSize) {
				return lassoCheck.getLoopCheck();
			}
			return lassoCheck.getStemCheck();
		}
		if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
			return lassoCheck.getLoopCheck();
		}
		assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
		return lassoCheck.getConcatCheck();
	}

	private A refineBuchiInternal(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		final BspmResult bspmResult = lassoCheck.getBspmResult();
		final IPredicate hondaPredicate = bspmResult.getHondaPredicate();
		final IPredicate rankEqAndSi = bspmResult.getRankEqAndSi();

		assert !SmtUtils.isFalseLiteral(bspmResult.getStemPrecondition().getFormula());
		assert !SmtUtils.isFalseLiteral(hondaPredicate.getFormula());
		assert !SmtUtils.isFalseLiteral(rankEqAndSi.getFormula());

		final RankingFunction rankingFunction = bspmResult.getTerminationArgument().getRankingFunction();
		final Script script = mCsToolkitWithRankVars.getManagedScript().getScript();
		mMDBenchmark.reportRankingFunction(mIteration, rankingFunction, script);

		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		int stage = 0;
		/*
		 * Iterate through a sequence of BuchiInterpolantAutomatonConstructionStyles Each construction style defines how
		 * an interpolant automaton is constructed. Constructions that provide simpler (less nondeterministic) automata
		 * should come first. In each iteration we compute the difference which causes an on-demand construction of the
		 * automaton and evaluate the automaton afterwards. If the automaton is "good" we keep the difference and
		 * continued with the termination analysis. If the automaton is "bad" we construct the next automaton. Currently
		 * an automaton is "good" iff the counterexample of the current CEGAR iteration is accepted by the automaton
		 * (otherwise the counterexample would not be excluded and we might get it again in the next iteration of the
		 * CEGAR loop).
		 *
		 */
		for (final BuchiInterpolantAutomatonConstructionStyle constructionStyle : mBiaConstructionStyleSequence) {
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton;
			A newAbstraction;
			boolean isUseful;
			try {
				final PredicateUnifier pu =
						new PredicateUnifier(mLogger, mServices, mCsToolkitWithRankVars.getManagedScript(),
								mPredicateFactory, mCsToolkitWithRankVars.getSymbolTable(), SIMPLIFICATION_TECHNIQUE,
								bspmResult.getStemPrecondition(), hondaPredicate, rankEqAndSi,
								bspmResult.getStemPostcondition(), bspmResult.getRankDecreaseAndBound(),
								bspmResult.getSiConjunction());
				final IPredicate[] stemInterpolants = getStemInterpolants(mCounterexample.getStem(),
						bspmResult.getStemPrecondition(), bspmResult.getStemPostcondition(), pu);
				final IPredicate[] loopInterpolants =
						getLoopInterpolants(mCounterexample.getLoop(), hondaPredicate, rankEqAndSi, pu);
				final NestedWordAutomaton<L, IPredicate> inputAutomaton =
						mInterpolantAutomatonBuilder.constructInterpolantAutomaton(bspmResult.getStemPrecondition(),
								mCounterexample, stemInterpolants, hondaPredicate, loopInterpolants,
								BuchiAutomizerUtils.getVpAlphabet(mAbstraction), mDefaultStateFactory);
				if (mPref.dumpAutomata()) {
					writeAutomatonToFile(inputAutomaton, mIteration, "BuchiInterpolantAutomaton",
							constructionStyle.toString());
				}
				final IHoareTripleChecker ehtc =
						HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
								HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, pu);
				final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
				bhtc.putDecreaseEqualPair(hondaPredicate, rankEqAndSi);
				assert NwaFloydHoareValidityCheck
						.forInterpolantAutomaton(mServices, mCsToolkitWithRankVars.getManagedScript(), bhtc, pu,
								inputAutomaton, true, bspmResult.getStemPrecondition())
						.getResult();

				assert new BuchiAccepts<>(new AutomataLibraryServices(mServices), inputAutomaton,
						mCounterexample.getNestedLassoWord()).getResult();

				interpolantAutomaton = mInterpolantAutomatonBuilder.constructGeneralizedAutomaton(mCounterexample,
						constructionStyle, bspmResult, pu, stemInterpolants, loopInterpolants, inputAutomaton, bhtc);
				mIsSemiDeterministic = constructionStyle.isAlwaysSemiDeterministic();
				newAbstraction = refineBuchi(mAbstraction, interpolantAutomaton);
				// Switch to read-only-mode for lazy constructions
				if (interpolantAutomaton instanceof NondeterministicInterpolantAutomaton) {
					((NondeterministicInterpolantAutomaton<?>) interpolantAutomaton).switchToReadonlyMode();
				} else if (interpolantAutomaton instanceof BuchiInterpolantAutomatonBouncer) {
					((BuchiInterpolantAutomatonBouncer<?>) interpolantAutomaton).switchToReadonlyMode();
				}
				mBenchmarkGenerator.addEdgeCheckerData(bhtc.getStatistics());
				isUseful = isUsefulInterpolantAutomaton(interpolantAutomaton, mCounterexample);
			} catch (final AutomataOperationCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "applying stage " + stage);
				throw new ToolchainCanceledException(e, rti);
			} catch (final ToolchainCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				throw e;
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e.getMessage());
			}
			if (mPref.dumpAutomata()) {
				final String automatonString;
				if (interpolantAutomaton.getVpAlphabet().getCallAlphabet().isEmpty()) {
					automatonString = "InterpolantBuchiAutomatonUsedInRefinementAfter";
				} else {
					automatonString = "InterpolantBuchiNestedWordAutomatonUsedInRefinementAfter";
				}
				writeAutomatonToFile(interpolantAutomaton, mIteration, automatonString, constructionStyle.toString());
			}
			final boolean tacasDump = false;
			if (tacasDump) {
				final String determinicity;
				final boolean isSemiDeterministic =
						new IsSemiDeterministic<>(new AutomataLibraryServices(mServices), interpolantAutomaton)
								.getResult();
				final boolean isDeterministic =
						new IsDeterministic<>(new AutomataLibraryServices(mServices), interpolantAutomaton).getResult();
				if (isDeterministic) {
					determinicity = "Deterministic";
					assert isSemiDeterministic : "but semi deterministic";
				} else if (isSemiDeterministic) {
					determinicity = "Semideterministic";
				} else {
					determinicity = "Nondeterministic";
				}
				final String automatonString;
				if (interpolantAutomaton.getVpAlphabet().getCallAlphabet().isEmpty()) {
					automatonString = "BuchiInterpolantAutomatonUsedInRefinement";
				} else {
					automatonString = "BuchiInterpolantNestedWordAutomatonUsedInRefinement";
				}
				writeAutomatonToFile(interpolantAutomaton, mIteration, determinicity + automatonString,
						constructionStyle.toString());
			}
			if (isUseful) {
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportBuchiModule(mIteration, interpolantAutomaton);
				}
				mBenchmarkGenerator.announceSuccessfullRefinementStage(stage);
				switch (constructionStyle.getInterpolantAutomaton()) {
				case DETERMINISTIC:
				case LASSO_AUTOMATON:
					mMDBenchmark.reportDeterministicModule(mIteration, interpolantAutomaton.size());
					break;
				case SCROOGE_NONDETERMINISM:
				case EAGER_NONDETERMINISM:
					mMDBenchmark.reportNonDeterministicModule(mIteration, interpolantAutomaton.size());
					break;
				default:
					throw new AssertionError("unsupported");
				}
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				mBenchmarkGenerator.addBackwardCoveringInformationBuchi(mBci);
				return reduceAbstractionSize(newAbstraction, mAutomataMinimizationAfterRankBasedRefinement);
			}
			stage++;
		}
		throw new AssertionError("no settings was sufficient");
	}

	private boolean isUsefulInterpolantAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolAutomatonUsed,
			final NestedLassoRun<L, IPredicate> counterexample) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> oldApi;
		oldApi = new RemoveUnreachable<>(new AutomataLibraryServices(mServices), interpolAutomatonUsed).getResult();
		final NestedWord<L> stem = counterexample.getStem().getWord();
		final NestedWord<L> loop = counterexample.getLoop().getWord();
		final NestedWord<L> stemAndLoop = stem.concatenate(loop);
		final NestedLassoWord<L> stemExtension = new NestedLassoWord<>(stemAndLoop, loop);
		final NestedWord<L> loopAndLoop = loop.concatenate(loop);
		final NestedLassoWord<L> loopExtension = new NestedLassoWord<>(stem, loopAndLoop);
		final boolean wordAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, counterexample.getNestedLassoWord())
						.getResult();
		if (!wordAccepted) {
			mLogger.info("Bad chosen interpolant automaton: word not accepted");
			return false;
		}
		// 2015-01-14 Matthias: word, stemExtension, and loopExtension are only
		// different representations of the same word. The following lines
		// do not make any sense (but might be helpful to reveal a bug.
		final boolean stemExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, stemExtension).getResult();
		if (!stemExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: stem extension not accepted");
		}
		final boolean loopExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, loopExtension).getResult();
		if (!loopExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: loop extension not accepted");
		}
		return true;
	}

	private IPredicate[] getStemInterpolants(final NestedRun<L, IPredicate> stem, final IPredicate precondition,
			final IPredicate postcondition, final PredicateUnifier predicateUnifier) {
		if (BuchiAutomizerUtils.isEmptyStem(stem)) {
			return null;
		}
		final InterpolatingTraceCheck<L> traceCheck =
				constructTraceCheck(precondition, postcondition, stem, predicateUnifier);
		if (traceCheck.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("incorrect predicates - stem");
		}
		return traceCheck.getInterpolants();
	}

	private IPredicate[] getLoopInterpolants(final NestedRun<L, IPredicate> loop, final IPredicate hondaPredicate,
			final IPredicate rankEqAndSi, final PredicateUnifier predicateUnifier) {
		final InterpolatingTraceCheck<L> traceCheck =
				constructTraceCheck(rankEqAndSi, hondaPredicate, loop, predicateUnifier);
		if (traceCheck.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("incorrect predicates - loop");
		}
		mBci = TraceCheckUtils.computeCoverageCapability(mServices, traceCheck, mLogger);
		return traceCheck.getInterpolants();
	}

	private InterpolatingTraceCheck<L> constructTraceCheck(final IPredicate precond, final IPredicate postcond,
			final NestedRun<L, IPredicate> run, final PredicateUnifier predicateUnifier) {
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			return new InterpolatingTraceCheckCraig<>(precond, postcond, new TreeMap<>(),
					new Counterexample<>(run.getWord()), mServices, mCsToolkitWithRankVars, mPredicateFactory,
					predicateUnifier, AssertCodeBlockOrder.NOT_INCREMENTALLY, false, false, mInterpolation, true,
					SIMPLIFICATION_TECHNIQUE);
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect: {
			return new TraceCheckSpWp<>(precond, postcond, new TreeMap<>(), new Counterexample<>(run.getWord()),
					mCsToolkitWithRankVars, AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true,
					mServices, false, mPredicateFactory, predicateUnifier, mInterpolation,
					mCsToolkitWithRankVars.getManagedScript(), SIMPLIFICATION_TECHNIQUE, false);
		}
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
	}

	private void reportRemainderModule(final boolean nonterminationKnown) {
		mMDBenchmark.reportRemainderModule(mAbstraction.size(), nonterminationKnown);
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportRemainderModule(nonterminationKnown);
		}
	}

	private HashRelation<String, ILocation> getOverapproximations() {
		final NestedWord<L> stem = mCounterexample.getStem().getWord();
		final NestedWord<L> loop = mCounterexample.getLoop().getWord();
		final HashRelation<String, ILocation> overapproximations = new HashRelation<>();
		overapproximations.addAll(Overapprox.getOverapproximations(stem.asList()));
		overapproximations.addAll(Overapprox.getOverapproximations(loop.asList()));
		return overapproximations;
	}

	protected Object getControlConfiguration(final IPredicate predicate) {
		if (mIsConcurrent) {
			return ((IMLPredicate) predicate).getProgramPoints();
		}
		return ((ISLPredicate) predicate).getProgramPoint();
	}

	private static class SubtaskAdditionalLoopUnwinding extends TaskIdentifier {
		private final int mAdditionaUnwindings;

		public SubtaskAdditionalLoopUnwinding(final TaskIdentifier parentTaskIdentifier,
				final int additionaUnwindings) {
			super(parentTaskIdentifier);
			mAdditionaUnwindings = additionaUnwindings;
		}

		@Override
		protected String getSubtaskIdentifier() {
			return mAdditionaUnwindings + "additionalUnwindings";
		}

	}

	/**
	 * Write the report of one synthesis scope of {@code lassoCheck}: {@code lasso_trace_<N>.txt} for the whole lasso,
	 * {@code lasso_trace_<N>_loop.txt} for the loop alone. Every timing, benchmark and proof comes from that scope
	 * only; the two scopes are never added up. RESULT reports the other scope as UNCHECKED, so that a consumer reading
	 * "Loop termination" or "Lasso termination" always gets the verdict that matches this file's timings.
	 */
	private void exportLassoTraceReport(final int iteration, final LassoCheck<L> lassoCheck,
			final boolean loopScope) {
		final File outputDir = new File(System.getProperty("user.dir"), "lasso_traces");
		if (!outputDir.exists()) {
			outputDir.mkdirs();
		}
		final File outputFile = new File(outputDir, String.format(loopScope ? "lasso_trace_%d_loop.txt" : "lasso_trace_%d.txt", iteration));

		try (PrintWriter pw = new PrintWriter(new FileWriter(outputFile))) {
			pw.println("========================================");
			pw.printf("LASSO TRACE REPORT - Iteration #%d%n", iteration);
			pw.println("========================================");
			pw.println();

			final var lcr = lassoCheck.getLassoCheckResult();
			final LassoCheck.SynthesisDump d = loopScope ? lassoCheck.getLoopDump() : lassoCheck.getLassoDump();
			// The stem this scope analysed: the trivial one for the loop alone -- always shown, since it is what the
			// timings below were measured on -- and the real one, when feasible, for the whole lasso.
			final boolean stemShown = loopScope || lcr.getStemFeasibility() == TraceCheckResult.FEASIBLE;

			// --- VARIABLE TYPES AND FUNCTION SIGNATURES ---
			pw.println("--- VARIABLE TYPES AND FUNCTION SIGNATURES ---");
			try {
				// Collect variables from stem and loop TransFormulas
				final Map<String, Sort> allVariables = new LinkedHashMap<>();
				final Set<FunctionSymbol> allFunctions = new LinkedHashSet<>();

				if (stemShown) {
					final UnmodifiableTransFormula stemTF =
							loopScope ? d.getAnalysedStemTF() : lassoCheck.computeStemTF();
					collectVariablesAndFunctions(stemTF, allVariables, allFunctions);
				}
				if (lcr.getLoopFeasibility() == TraceCheckResult.FEASIBLE) {
					final UnmodifiableTransFormula loopTF = lassoCheck.computeLoopTF();
					collectVariablesAndFunctions(loopTF, allVariables, allFunctions);
				}
				// Also collect linearized variables (TermVariables after preprocessing)
				final LassoUnderConstruction lucForVars = d.getLinearizedLasso();
				if (lucForVars != null) {
					collectLinearizedVariables(lucForVars.getStem(), allVariables);
					collectLinearizedVariables(lucForVars.getLoop(), allVariables);
				}

				// Print variable types
				pw.println("Variables:");
				if (allVariables.isEmpty()) {
					pw.println("  (none)");
				} else {
					for (final Map.Entry<String, Sort> entry : allVariables.entrySet()) {
						pw.printf("  %-50s : %s%n", entry.getKey(), entry.getValue());
					}
				}
				pw.println();

				// Print function signatures
				pw.println("Function signatures:");
				if (allFunctions.isEmpty()) {
					pw.println("  (none)");
				} else {
					for (final FunctionSymbol func : allFunctions) {
						final Sort[] paramSorts = func.getParameterSorts();
						final Sort returnSort = func.getReturnSort();
						final String params = java.util.Arrays.stream(paramSorts)
								.map(Sort::toString)
								.collect(Collectors.joining(", "));
						pw.printf("  %s(%s) -> %s%n", func.getName(), params, returnSort);
					}
				}
			} catch (final Exception e) {
				pw.printf("  ERROR extracting types: %s%n", e.getMessage());
			}
			pw.println();

			// --- LINEARIZED TRACE (TransFormula) ---
			pw.println("--- LINEARIZED TRACE (TransFormula) ---");
			if (stemShown) {
				try {
					final UnmodifiableTransFormula stemTF =
							loopScope ? d.getAnalysedStemTF() : lassoCheck.computeStemTF();
					pw.println("Stem TransFormula:");
					pw.println(stemTF);
				} catch (final Exception e) {
					pw.printf("Stem TransFormula: ERROR (%s)%n", e.getMessage());
				}
			} else {
				pw.printf("Stem TransFormula: N/A (stem feasibility: %s)%n", lcr.getStemFeasibility());
			}
			pw.println();
			if (lcr.getLoopFeasibility() == TraceCheckResult.FEASIBLE) {
				try {
					final UnmodifiableTransFormula loopTF = lassoCheck.computeLoopTF();
					pw.println("Loop TransFormula:");
					pw.println(loopTF);
				} catch (final Exception e) {
					pw.printf("Loop TransFormula: ERROR (%s)%n", e.getMessage());
				}
			} else {
				pw.printf("Loop TransFormula: N/A (loop feasibility: %s)%n", lcr.getLoopFeasibility());
			}
			pw.println();

			// --- PREPROCESSED LINEAR TRACE (partitioner disabled, single formula) ---
			pw.println("--- PREPROCESSED LINEAR TRACE (partitioner=OFF, single unified formula) ---");
			final LassoUnderConstruction luc = d.getLinearizedLasso();
			final PreprocessingBenchmark lucPpBench = d.getLinearizedLassoPreprocessingBenchmark();
			if (luc == null) {
				pw.println("  (not available)");
			} else {
				// Preprocessing benchmark (time per preprocessor)
				if (lucPpBench != null) {
					pw.printf("  Preprocessing initial max DAG size: %d%n", lucPpBench.getIntialMaxDagSizeLassos());
					final List<String> ppNames = lucPpBench.getPreprocessors();
					final List<Float> ppRels = lucPpBench.getMaxDagSizeLassosRelative();
					for (int i = 0; i < ppNames.size(); i++) {
						pw.printf("    %s -> relative DAG size: %.4f%n", ppNames.get(i), ppRels.get(i));
					}
					pw.println();
				}
				pw.println("Stem (linearized):");
				pw.printf("  Formula:  %s%n", luc.getStem().getFormula().toStringDirect());
				pw.printf("  InVars:   %s%n", luc.getStem().getInVars());
				pw.printf("  OutVars:  %s%n", luc.getStem().getOutVars());
				pw.printf("  AuxVars:  %s%n", luc.getStem().getAuxVars());
				pw.println();
				pw.println("Loop (linearized):");
				pw.printf("  Formula:  %s%n", luc.getLoop().getFormula().toStringDirect());
				pw.printf("  InVars:   %s%n", luc.getLoop().getInVars());
				pw.printf("  OutVars:  %s%n", luc.getLoop().getOutVars());
				pw.printf("  AuxVars:  %s%n", luc.getLoop().getAuxVars());
			}
			pw.println();

			// --- RAW TRACE ---
			pw.println("--- RAW TRACE ---");
			final NestedWord<L> stem = mCounterexample.getStem().getWord();
			final NestedWord<L> loop = mCounterexample.getLoop().getWord();
			pw.printf("Stem (length=%d):%n", stem.length());
			for (int i = 0; i < stem.length(); i++) {
				pw.printf("  [%d] %s%n", i, stem.getSymbol(i));
			}
			pw.printf("Loop (length=%d):%n", loop.length());
			for (int i = 0; i < loop.length(); i++) {
				pw.printf("  [%d] %s%n", i, loop.getSymbol(i));
			}
			pw.println();

			// --- RESULT ---
			pw.println("--- RESULT ---");
			pw.printf("Stem feasibility:    %s%n", lcr.getStemFeasibility());
			pw.printf("Loop feasibility:    %s%n", lcr.getLoopFeasibility());
			pw.printf("Concat feasibility:  %s%n", lcr.getConcatFeasibility());
			pw.printf("Loop termination:    %s%n", loopScope ? lcr.getLoopTermination() : "UNCHECKED");
			pw.printf("Lasso termination:   %s%n", loopScope ? "UNCHECKED" : lcr.getLassoTermination());
			pw.printf("Continue directive:  %s%n", lcr.getContinueDirective());
			pw.println();

			// --- STRATEGY SHUFFLE ---
			pw.println("--- STRATEGY SHUFFLE ---");
			final long seedLoop = d.getShuffleSeed();
			final java.util.List<String> orderLoop = loopScope ? d.getStrategyOrder() : List.of();
			// empty order: synthesis not run; seed < 0: static order (shuffle disabled)
			if (!orderLoop.isEmpty()) {
				pw.printf("  [Loop-only synthesis] %s%n",
						seedLoop >= 0 ? "Seed: " + seedLoop : "Static order (shuffle disabled)");
				for (int i = 0; i < orderLoop.size(); i++) {
					pw.printf("    [%d] %s%n", i + 1, orderLoop.get(i));
				}
			} else {
				pw.println("  [Loop-only synthesis] (not run)");
			}
			final long seedLasso = d.getShuffleSeed();
			final java.util.List<String> orderLasso = loopScope ? List.of() : d.getStrategyOrder();
			// empty order: synthesis not run; seed < 0: static order (shuffle disabled)
			if (!orderLasso.isEmpty()) {
				pw.printf("  [Lasso synthesis]     %s%n",
						seedLasso >= 0 ? "Seed: " + seedLasso : "Static order (shuffle disabled)");
				for (int i = 0; i < orderLasso.size(); i++) {
					pw.printf("    [%d] %s%n", i + 1, orderLasso.get(i));
				}
			} else {
				pw.println("  [Lasso synthesis]     (not run)");
			}
			pw.println();

			// --- FIXPOINT CHECK ---
			pw.println("--- FIXPOINT CHECK ---");
			pw.printf("  Result: %s%n", d.getFixpointCheckResult());
			if (d.getFixpointCheckTimeNs() >= 0) {
				pw.printf("  Time:   %d ns (%.2f ms)%n",
						d.getFixpointCheckTimeNs(),
						d.getFixpointCheckTimeNs() / 1_000_000.0);
			}
			pw.println();

			// --- NONTERMINATION ARGUMENT ---
			pw.println("--- NONTERMINATION ARGUMENT ---");
			final NonTerminationArgument ntArg = d.getNonTerminationArgument();
			if (ntArg == null) {
				pw.println("  (none)");
			} else if (ntArg instanceof GeometricNonTerminationArgument) {
				final GeometricNonTerminationArgument gntArg = (GeometricNonTerminationArgument) ntArg;
				pw.println("  Type: GeometricNonTerminationArgument");
				pw.println("  State at init:");
				gntArg.getStateInit().forEach((var, val) ->
						pw.printf("    %-40s = %s%n", var.getGloballyUniqueId(), val));
				pw.println("  State at honda:");
				gntArg.getStateHonda().forEach((var, val) ->
						pw.printf("    %-40s = %s%n", var.getGloballyUniqueId(), val));
				pw.printf("  Number of GEVs: %d%n", gntArg.getNumberOfGEVs());
				for (int g = 0; g < gntArg.getNumberOfGEVs(); g++) {
					pw.printf("  GEV[%d] (lambda=%s):%n", g, gntArg.getLambdas().get(g));
					gntArg.getGEVs().get(g).forEach((var, val) ->
							pw.printf("    %-40s = %s%n", var.getGloballyUniqueId(), val));
				}
			} else if (ntArg instanceof InfiniteFixpointRepetition) {
				final InfiniteFixpointRepetition ifr = (InfiniteFixpointRepetition) ntArg;
				pw.println("  Type: InfiniteFixpointRepetition (detected via FixpointCheck)");
				pw.println("  Values at init:");
				ifr.getValuesAtInit().forEach((var, val) ->
						pw.printf("    %-40s = %s%n", var, val));
				pw.println("  Values at honda:");
				ifr.getValuesAtHonda().forEach((var, val) ->
						pw.printf("    %-40s = %s%n", var, val));
			} else {
				pw.printf("  Type: %s%n", ntArg.getClass().getSimpleName());
				pw.println("  " + ntArg);
			}
			pw.println();

			// --- TERMINATION ANALYSIS SETTINGS ---
			final boolean partitionerOn = lassoCheck.isPartitioneerEnabled();
			final String partitionerTag = partitionerOn ? "partitioner=ON" : "partitioner=OFF";
			pw.printf("--- TERMINATION ANALYSIS SETTINGS [%s] ---%n", partitionerTag);
			pw.printf("  analysis_type:              %s%n", lassoCheck.getRankAnalysisType());
			pw.println("  num_strict_invariants:      0");
			pw.println("  num_non_strict_invariants:  1");
			pw.println("  non_decreasing_invariants:  true");
			pw.printf("  simplify_termination_arg:   %s%n", lassoCheck.isSimplifyTerminationArgument());
			pw.printf("  simplify_supporting_invs:   %s%n", lassoCheck.isSimplifyTerminationArgument());
			pw.println("  overapproximate_stem:       false");
			pw.printf("  template_benchmark_mode:    %s%n", lassoCheck.isTemplateBenchmarkMode());
			pw.printf("  partitioner_enabled:        %s%n", partitionerOn);
			pw.println();

			// --- TERMINATION ANALYSIS BENCHMARKS ---
			final List<TerminationAnalysisBenchmark> tBenchmarks =
					d.getTerminationAnalysisBenchmarks();
			pw.printf("--- TERMINATION ANALYSIS BENCHMARKS [%s] ---%n", partitionerTag);
			if (tBenchmarks.isEmpty()) {
				pw.println("  (none)");
			} else {
				long totalTTimeNs = 0;
				for (int i = 0; i < tBenchmarks.size(); i++) {
					final TerminationAnalysisBenchmark b = tBenchmarks.get(i);
					final long tTimeNs =
							(Long) b.getKeyValueMap().get(TerminationAnalysisBenchmark.s_Label_Time);
					final String satStr = b.getConstraintsSatisfiability().toString();
					pw.printf("  [%d] Template: %-25s  Degree: %d  Satisfiability: %-7s  Time: %d ns (%.2f ms)%n",
							i + 1, b.getTemplate(), b.getDegree(), satStr,
							tTimeNs, tTimeNs / 1_000_000.0);
					pw.printf("       Variables (stem/loop): %d/%d  Disjuncts (stem/loop): %d/%d%n",
							b.getVariablesStem(), b.getVariablesLoop(),
							b.getDisjunctsStem(), b.getDisjunctsLoop());
					pw.printf("       Supporting invariants: %d  Motzkin applications: %d%n",
							b.getSupportingInvariants(), b.getMotzkinApplications());

					// Show template-specific parameters
					final String tpl = b.getTemplate();
					if ("affine".equals(tpl)) {
						pw.println("       Template params: f(x) = Σ(ai*xi) + c, delta > 0");
						pw.println("         Constraints: f(x) > 0 ∧ f(x') <= f(x) - delta");
					} else if (tpl != null && tpl.endsWith("-nested")) {
						final String nStr = tpl.replace("-nested", "");
						pw.printf("         Template params: %s functions f0..f%s, delta > 0%n", nStr, Integer.parseInt(nStr) - 1);
						pw.println("         Constraints: f0(x') < f0(x) - δ");
						pw.printf("                      fi(x') < fi(x) + f(i-1)(x) for i=1..%s%n", Integer.parseInt(nStr) - 1);
						pw.printf("                      f%s(x) > 0%n", Integer.parseInt(nStr) - 1);
					} else if (tpl != null && tpl.endsWith("-phase")) {
						final String nStr = tpl.replace("-phase", "");
						pw.printf("         Template params: %s phases f0..f%s, δ0..δ%s > 0%n", nStr, Integer.parseInt(nStr) - 1, Integer.parseInt(nStr) - 1);
						pw.println("         Constraints: ∨i fi(x) > 0");
						pw.println("                      f0(x') < f0(x) - δ0");
						pw.printf("                      fi(x') < fi(x) - δi ∨ f(i-1)(x) > 0 for i=1..%s%n", Integer.parseInt(nStr) - 1);
					} else if (tpl != null && tpl.endsWith("-lex")) {
						final String nStr = tpl.replace("-lex", "");
						pw.printf("         Template params: %s components f0..f%s, δ0..δ%s > 0%n", nStr, Integer.parseInt(nStr) - 1, Integer.parseInt(nStr) - 1);
						pw.println("         Constraints: fi(x) > 0 for all i");
						pw.println("                      ∨i fi(x') < fi(x) - δi");
						pw.println("                      fi(x') <= fi(x) ∨ ∃j<i: fj(x') < fj(x) - δj");
					} else if (tpl != null && tpl.endsWith("-piece")) {
						final String nStr = tpl.replace("-piece", "");
						pw.printf("         Template params: %s pieces f0..f%s with predicates g0..g%s, delta > 0%n", nStr, Integer.parseInt(nStr) - 1, Integer.parseInt(nStr) - 1);
						pw.println("         Constraints: fi(x) > 0, ∨i gi(x) >= 0");
						pw.println("                      gi(x) < 0 ∨ gj(x') < 0 ∨ fj(x') < fi(x) - delta");
					}

					totalTTimeNs += tTimeNs;
				}
				pw.printf("  Total termination analysis time: %.2f ms%n", totalTTimeNs / 1_000_000.0);
			}
			pw.println();

			// --- AFFINE TEMPLATE SMT ASSERTS (0 strict, 1 non-strict) ---
			/*pw.println("--- AFFINE TEMPLATE SMT ASSERTS (0 strict, 1 non-strict) ---");
			boolean foundAffine = false;
			for (final TerminationAnalysisBenchmark b : tBenchmarks) {
				if ("affine".equals(b.getTemplate())
						&& b.getNumStrictInvariants() == 0
						&& b.getNumNonStrictInvariants() == 1) {
					foundAffine = true;
					final List<Term> asserts = b.getAssertedTerms();
					pw.printf("  Total assertions: %d (Motzkin applications: %d, SIs: %d)%n",
							asserts.size(), b.getMotzkinApplications(), b.getSupportingInvariants());
					pw.println();

					// Collect free TermVariables (Motzkin coefficients) across all assertions
					final Set<TermVariable> freeVars = new java.util.LinkedHashSet<>();
					for (final Term t : asserts) {
						for (final TermVariable tv : t.getFreeVars()) {
							freeVars.add(tv);
						}
					}
					pw.println("  Free variables (declare-fun):");
					for (final TermVariable tv : freeVars) {
						pw.printf("    (declare-fun %s () %s)%n", tv.getName(), tv.getSort());
					}
					pw.println();

					pw.println("  Assertions:");
					int assertIdx = 1;
					for (final Term t : asserts) {
						pw.printf("  [%d] (assert %s)%n", assertIdx++, t.toStringDirect());
					}
					break; // only the first affine benchmark with 1-strict/0-non-strict
				}
			}
			if (!foundAffine) {
				pw.println("  (no affine template benchmark with 1-strict/0-non-strict found in this iteration)");
			}
			pw.println();*/

			// --- TERMINATION ARGUMENT (if found) ---
			pw.println("--- TERMINATION ARGUMENT ---");
			final BspmResult bspmResult = d.getBspmResult();
			if (bspmResult != null && bspmResult.getTerminationArgument() != null) {
				final TerminationArgument termArg = bspmResult.getTerminationArgument();
				final RankingFunction rf = termArg.getRankingFunction();
				pw.printf("  Ranking function type: %s%n", rf.getName());
				pw.printf("  Ranking function:      %s%n", rf);
				pw.println("  Variables:");
				for (final IProgramVar v : rf.getVariables()) {
					pw.printf("    %s%n", v.getGloballyUniqueId());
				}
				pw.println("  Supporting invariants:");
				if (termArg.getSupportingInvariants().isEmpty()) {
					pw.println("    (none)");
				} else {
					int siIdx = 0;
					for (final SupportingInvariant si : termArg.getSupportingInvariants()) {
						pw.printf("    [%d] %s%n", siIdx++, si);
					}
				}
				if (!termArg.getArrayIndexSupportingInvariants().isEmpty()) {
					pw.println("  Array index supporting invariants:");
					int aiIdx = 0;
					for (final Term t : termArg.getArrayIndexSupportingInvariants()) {
						pw.printf("    [%d] %s%n", aiIdx++, t.toStringDirect());
					}
				}
			} else {
				pw.println("  (none)");
			}
			pw.println();

			// --- NONTERMINATION ANALYSIS SETTINGS ---
			pw.printf("--- NONTERMINATION ANALYSIS SETTINGS [%s] ---%n", partitionerTag);
			pw.printf("  analysis_type:        %s%n", lassoCheck.getGntaAnalysisType());
			pw.printf("  num_gevs:             %d%n", lassoCheck.getGntaDirections());
			pw.println("  allow_bounded:        true");
			pw.println("  nilpotent_components: true");
			pw.printf("  partitioner_enabled:  %s%n", partitionerOn);
			pw.println();

			// --- NONTERMINATION ANALYSIS BENCHMARKS ---
			final List<NonterminationAnalysisBenchmark> ntBenchmarks =
					d.getNonterminationAnalysisBenchmarks();
			pw.printf("--- NONTERMINATION ANALYSIS BENCHMARKS [%s] ---%n", partitionerTag);
			if (ntBenchmarks.isEmpty()) {
				pw.println("  (none)");
			} else {
				long totalNtTimeNs = 0;
				for (int i = 0; i < ntBenchmarks.size(); i++) {
					final NonterminationAnalysisBenchmark b = ntBenchmarks.get(i);
					pw.printf("  [%d] IsFixpoint: %-5s  Satisfiability: %-7s  Time: %d ns (%.2f ms)%n",
							i + 1, b.isFixpoint(), b.getConstraintsSatisfiability(),
							b.getTime(), b.getTime() / 1_000_000.0);
					pw.printf("       Variables (stem/loop): %d/%d  Disjuncts (stem/loop): %d/%d%n",
							b.getVariablesStem(), b.getVariablesLoop(),
							b.getDisjunctsStem(), b.getDisjunctsLoop());
					totalNtTimeNs += b.getTime();
				}
				pw.printf("  Total nontermination analysis time: %.2f ms%n", totalNtTimeNs / 1_000_000.0);
			}
			pw.println();

			// --- PREPROCESSING BENCHMARKS ---
			final List<PreprocessingBenchmark> ppBenchmarks =
					d.getPreprocessingBenchmarks();
			pw.printf("--- PREPROCESSING BENCHMARKS [%s] ---%n", partitionerTag);
			if (ppBenchmarks.isEmpty()) {
				pw.println("  (none)");
			} else {
				for (int i = 0; i < ppBenchmarks.size(); i++) {
					final PreprocessingBenchmark pb = ppBenchmarks.get(i);
					pw.printf("  [Lasso %d] Initial max DAG size: %d%n", i + 1, pb.getIntialMaxDagSizeLassos());
					final List<String> preprocessors = pb.getPreprocessors();
					final List<Float> relatives = pb.getMaxDagSizeLassosRelative();
					for (int j = 0; j < preprocessors.size(); j++) {
						pw.printf("    %s -> relative DAG size: %.4f%n",
								preprocessors.get(j), relatives.get(j));
					}
				}
			}
			pw.println();

			// --- TIMING SUMMARY ---
			long totalTNs = 0;
			for (final TerminationAnalysisBenchmark b : tBenchmarks) {
				totalTNs += (Long) b.getKeyValueMap().get(TerminationAnalysisBenchmark.s_Label_Time);
			}
			long totalNtNs = 0;
			for (final NonterminationAnalysisBenchmark b : ntBenchmarks) {
				totalNtNs += b.getTime();
			}
			pw.printf("--- TIMING SUMMARY [%s] ---%n", partitionerTag);
			final long fixpointNs = Math.max(0, d.getFixpointCheckTimeNs());
			pw.printf("Fixpoint check time:  %.2f ms%n", fixpointNs / 1_000_000.0);
			// Total of everything this scope ran -- fixpoint, ranking-function templates and GNTA -- each of which is
			// also listed on its own line below; the other scope is never included.
			pw.printf("Total LassoRanker time: %.2f ms%n", (fixpointNs + totalTNs + totalNtNs) / 1_000_000.0);
			pw.printf("  Termination analysis:     %.2f ms%n", totalTNs / 1_000_000.0);
			pw.printf("  Nontermination analysis:   %.2f ms%n", totalNtNs / 1_000_000.0);

		} catch (final IOException e) {
			mLogger.warn("Failed to export lasso trace report: " + e.getMessage());
		}
	}

	private static void collectVariablesAndFunctions(final UnmodifiableTransFormula tf,
			final Map<String, Sort> variables, final Set<FunctionSymbol> functions) {
		// Collect program variables (inVars and outVars) with their sorts
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			variables.put(entry.getKey().getGloballyUniqueId(), entry.getKey().getSort());
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			variables.put(entry.getKey().getGloballyUniqueId(), entry.getKey().getSort());
		}
		// Collect auxiliary variables
		for (final TermVariable auxVar : tf.getAuxVars()) {
			variables.put(auxVar.getName(), auxVar.getSort());
		}
		// Collect non-theory function symbols from the formula
		final Set<FunctionSymbol> funcSymbols = SmtUtils.extractNonTheoryFunctionSymbols(tf.getFormula());
		functions.addAll(funcSymbols);
	}

	private static void collectLinearizedVariables(final ModifiableTransFormula mtf,
			final Map<String, Sort> variables) {
		for (final Map.Entry<IProgramVar, TermVariable> entry : mtf.getInVars().entrySet()) {
			final TermVariable tv = entry.getValue();
			variables.put(tv.getName(), tv.getSort());
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry : mtf.getOutVars().entrySet()) {
			final TermVariable tv = entry.getValue();
			variables.put(tv.getName(), tv.getSort());
		}
		for (final TermVariable auxVar : mtf.getAuxVars()) {
			variables.put(auxVar.getName(), auxVar.getSort());
		}
	}

}

/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.pasttel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LexicographicRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.MultiphaseRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.NestedRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.PiecewiseRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Maps PaSTTeL's structured JSON winner certificate (see PaSTTeL's report_json.h / ProofCertificate) back onto
 * LassoRanker's own {@link TerminationArgument}/{@link GeometricNonTerminationArgument} types, so the rest of
 * BuchiAutomizer (BinaryStatePredicateManager, BuchiCegarLoopResult, ...) needs no changes.
 *
 * Every mapping method returns {@code null} if the certificate cannot be faithfully reconstructed (an unresolvable
 * variable name, a non-integer ranking-function coefficient where an exact integer is required, an unrecognized
 * template name in technique_name): callers must treat that as "no usable result", not as an error, and fall back to
 * LassoRanker.
 */
public final class PasttelResultMapper {

	private PasttelResultMapper() {
	}

	/**
	 * @param winner
	 *            the "winner" object of PaSTTeL's AnalysisReport, with status == "TERMINATING".
	 * @param vars
	 *            program-variable-name to {@link IProgramVar} lookup, as built by
	 *            {@link LassoJsonWriter#collectVariableMap(de.uni_freiburg.informatik.ultimate.lassoranker.Lasso)}
	 *            for the same lasso that was sent to PaSTTeL.
	 * @param arrayIndexSupportingInvariants
	 *            the array index (dis)equalities of the {@code LassoAnalysis} whose preprocessed lasso was sent to
	 *            PaSTTeL ({@code LassoAnalysis#getArrayIndexSupportingInvariants()}); attached to the result as
	 *            LassoRanker attaches them to its own termination arguments.
	 */
	public static TerminationArgument toTerminationArgument(final JsonObject winner, final Map<String, IProgramVar> vars,
			final Set<Term> arrayIndexSupportingInvariants) {
		final JsonArray rankingFunctionsJson = winner.getAsJsonArray("ranking_functions");
		if (rankingFunctionsJson == null || rankingFunctionsJson.isEmpty()) {
			return null;
		}
		final AffineFunction[] components = new AffineFunction[rankingFunctionsJson.size()];
		for (int i = 0; i < components.length; i++) {
			components[i] = toAffineFunction(rankingFunctionsJson.get(i).getAsJsonObject(), vars);
			if (components[i] == null) {
				return null;
			}
		}

		final String techniqueName = winner.has("technique_name") ? winner.get("technique_name").getAsString() : "";
		final RankingFunction rankingFunction = toRankingFunction(techniqueName, components, winner, vars);
		if (rankingFunction == null) {
			return null;
		}

		final List<SupportingInvariant> supportingInvariants = new ArrayList<>();
		final JsonArray siJson = winner.getAsJsonArray("supporting_invariants");
		if (siJson != null) {
			for (int i = 0; i < siJson.size(); i++) {
				final JsonObject one = siJson.get(i).getAsJsonObject();
				final AffineFunction base = toAffineFunction(one, vars);
				if (base == null) {
					return null;
				}
				final SupportingInvariant si = new SupportingInvariant(base);
				si.strict = one.has("is_strict") && one.get("is_strict").getAsBoolean();
				supportingInvariants.add(si);
			}
		}

		return new TerminationArgument(rankingFunction, supportingInvariants, arrayIndexSupportingInvariants);
	}

	private static RankingFunction toRankingFunction(final String techniqueName, final AffineFunction[] components,
			final JsonObject winner, final Map<String, IProgramVar> vars) {
		if (techniqueName.contains("PiecewiseTemplate")) {
			final JsonArray guardsJson = winner.getAsJsonArray("guards");
			if (guardsJson == null || guardsJson.size() != components.length) {
				return null;
			}
			final AffineFunction[] guards = new AffineFunction[guardsJson.size()];
			for (int i = 0; i < guards.length; i++) {
				guards[i] = toAffineFunction(guardsJson.get(i).getAsJsonObject(), vars);
				if (guards[i] == null) {
					return null;
				}
			}
			return new PiecewiseRankingFunction(components, guards);
		}
		if (techniqueName.contains("NestedTemplate")) {
			return new NestedRankingFunction(components);
		}
		if (techniqueName.contains("LexicographicTemplate")) {
			final RankingFunction[] parts = new RankingFunction[components.length];
			for (int i = 0; i < components.length; i++) {
				parts[i] = new LinearRankingFunction(components[i]);
			}
			return new LexicographicRankingFunction(parts);
		}
		if (techniqueName.contains("MultiphaseTemplate")) {
			return new MultiphaseRankingFunction(components);
		}
		if (techniqueName.contains("AffineTemplate") && components.length == 1) {
			return new LinearRankingFunction(components[0]);
		}
		// Unrecognized technique_name: don't guess which template this is.
		return null;
	}

	/**
	 * @param winner
	 *            the "winner" object of PaSTTeL's AnalysisReport, with status == "NON_TERMINATING".
	 */
	public static GeometricNonTerminationArgument toNonTerminationArgument(final JsonObject winner,
			final Map<String, IProgramVar> vars) {
		final Map<IProgramVar, Rational> stateHonda = toRationalMap(winner.getAsJsonObject("nt_state_honda"), vars);
		if (stateHonda == null) {
			return null;
		}
		Map<IProgramVar, Rational> stateInit = toRationalMap(winner.getAsJsonObject("nt_state_init"), vars);
		if (stateInit == null || stateInit.isEmpty()) {
			// FixpointTechnique (a degenerate GNTA with 0 GEVs) only ever populates nt_state_honda: the loop's
			// guard already holds at that very state, so init == honda.
			stateInit = stateHonda;
		}

		final List<Map<IProgramVar, Rational>> gevs = new ArrayList<>();
		final JsonArray gevsJson = winner.getAsJsonArray("nt_eigenvectors");
		if (gevsJson != null) {
			for (int i = 0; i < gevsJson.size(); i++) {
				final Map<IProgramVar, Rational> gev = toRationalMap(gevsJson.get(i).getAsJsonObject(), vars);
				if (gev == null) {
					return null;
				}
				gevs.add(gev);
			}
		}

		final List<Rational> lambdas = toRationalList(winner.getAsJsonArray("nt_lambdas"));
		final List<Rational> nus = toRationalList(winner.getAsJsonArray("nt_nus"));
		if (lambdas == null || nus == null || gevs.size() != lambdas.size()
				|| (!gevs.isEmpty() && gevs.size() != nus.size() + 1)) {
			return null;
		}

		return new GeometricNonTerminationArgument(stateInit, stateHonda, gevs, lambdas, nus);
	}

	private static AffineFunction toAffineFunction(final JsonObject rankingFunctionJson,
			final Map<String, IProgramVar> vars) {
		final AffineFunction result = new AffineFunction();
		final JsonObject coefficients = rankingFunctionJson.getAsJsonObject("coefficients");
		if (coefficients == null) {
			return null;
		}
		for (final var entry : coefficients.entrySet()) {
			final IProgramVar var = vars.get(entry.getKey());
			if (var == null) {
				return null;
			}
			final BigInteger coefficient = toExactInteger(entry.getValue().getAsJsonObject());
			if (coefficient == null) {
				return null;
			}
			result.put(var, coefficient);
		}
		final BigInteger constant = toExactInteger(rankingFunctionJson.getAsJsonObject("constant"));
		if (constant == null) {
			return null;
		}
		result.setConstant(constant);
		return result;
	}

	private static Map<IProgramVar, Rational> toRationalMap(final JsonObject stateJson,
			final Map<String, IProgramVar> vars) {
		if (stateJson == null) {
			return null;
		}
		final Map<IProgramVar, Rational> result = new java.util.LinkedHashMap<>();
		for (final var entry : stateJson.entrySet()) {
			final IProgramVar var = vars.get(entry.getKey());
			if (var == null) {
				return null;
			}
			result.put(var, toRational(entry.getValue().getAsJsonObject()));
		}
		return result;
	}

	private static List<Rational> toRationalList(final JsonArray arr) {
		if (arr == null) {
			return null;
		}
		final List<Rational> result = new ArrayList<>();
		for (int i = 0; i < arr.size(); i++) {
			result.add(toRational(arr.get(i).getAsJsonObject()));
		}
		return result;
	}

	/**
	 * @return the exact BigInteger value of a {"num","den"} Rational, or {@code null} if it is not integral. Ranking
	 *         function coefficients must be exact integers (see {@link AffineFunction}); silently rounding a
	 *         non-integer coefficient would produce an unsound certificate.
	 */
	private static BigInteger toExactInteger(final JsonObject rational) {
		final BigInteger den = new BigInteger(rational.get("den").getAsString());
		if (!den.equals(BigInteger.ONE)) {
			return null;
		}
		return new BigInteger(rational.get("num").getAsString());
	}

	private static Rational toRational(final JsonObject rational) {
		final BigInteger num = new BigInteger(rational.get("num").getAsString());
		final BigInteger den = new BigInteger(rational.get("den").getAsString());
		return Rational.valueOf(num, den);
	}
}

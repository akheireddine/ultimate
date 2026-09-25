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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Serializes an already-preprocessed {@link Lasso} (i.e. {@link Lasso#getStem()}/
 * {@link Lasso#getLoop()}, as returned by {@code LassoAnalysis.getLassos()}) directly
 * to PaSTTeL's JSON lasso schema, matching what
 * PaSTTeL/scripts/benchmark_ultimate_vs_pasttel.py derives from the "LINEARIZED TRACE"
 * section of a lasso dump -- see PaSTTeL/include/parser/json_trace_parser.h.
 *
 * The lasso must come from a run with the LassoRanker partitioner disabled: PaSTTeL's
 * schema has no notion of the multiple independent lasso components the partitioner can
 * produce, and every lasso dump this schema was validated against was generated with it
 * off.
 *
 * Does not populate constants/functions/axioms: no lasso from this toolchain carries any
 * by this point (array cells are already replacement variables), and PaSTTeL treats them
 * as optional.
 */
public final class LassoJsonWriter {

	private LassoJsonWriter() {
	}

	public static String toJson(final Lasso lasso, final Script script) {
		final JsonObject root = new JsonObject();

		final JsonArray programVars = new JsonArray();
		final JsonObject varTypes = new JsonObject();
		collectVars(lasso.getStem(), programVars, varTypes);
		collectVars(lasso.getLoop(), programVars, varTypes);

		root.add("program_vars", programVars);
		root.add("var_types", varTypes);

		final JsonArray stem = new JsonArray();
		stem.add(transitionToJson(lasso.getStem(), script, "S0", "S1"));
		root.add("stem", stem);

		final JsonArray loop = new JsonArray();
		loop.add(transitionToJson(lasso.getLoop(), script, "L0", "L1"));
		root.add("loop", loop);

		return root.toString();
	}

	/**
	 * @return program-variable-name (as used in the JSON this class writes) to {@link IProgramVar} lookup for every
	 *         variable in the lasso -- for resolving PaSTTeL's JSON result back to the same {@link IProgramVar}s
	 *         (see {@link PasttelResultMapper}).
	 */
	public static Map<String, IProgramVar> collectVariableMap(final Lasso lasso) {
		final Map<String, IProgramVar> result = new LinkedHashMap<>();
		for (final IProgramVar v : lasso.getStem().getInVars().keySet()) {
			result.put(v.getGloballyUniqueId(), v);
		}
		for (final IProgramVar v : lasso.getStem().getOutVars().keySet()) {
			result.put(v.getGloballyUniqueId(), v);
		}
		for (final IProgramVar v : lasso.getLoop().getInVars().keySet()) {
			result.put(v.getGloballyUniqueId(), v);
		}
		for (final IProgramVar v : lasso.getLoop().getOutVars().keySet()) {
			result.put(v.getGloballyUniqueId(), v);
		}
		return result;
	}

	private static void collectVars(final LinearTransition trans, final JsonArray programVars,
			final JsonObject varTypes) {
		for (final IProgramVar v : trans.getInVars().keySet()) {
			addVarIfNew(v, programVars, varTypes);
		}
		for (final IProgramVar v : trans.getOutVars().keySet()) {
			addVarIfNew(v, programVars, varTypes);
		}
	}

	private static void addVarIfNew(final IProgramVar v, final JsonArray programVars, final JsonObject varTypes) {
		final String name = v.getGloballyUniqueId();
		if (varTypes.has(name)) {
			return;
		}
		programVars.add(name);
		varTypes.addProperty(name, v.getTermVariable().getSort().toString());
	}

	private static JsonObject transitionToJson(final LinearTransition trans, final Script script,
			final String source, final String target) {
		final JsonObject obj = new JsonObject();
		obj.addProperty("source", source);
		obj.addProperty("target", target);
		obj.addProperty("formula", formulaToSmtLib2(trans, script));
		obj.add("in_vars", varMapToJson(trans.getInVars()));
		obj.add("out_vars", varMapToJson(trans.getOutVars()));
		obj.add("aux_vars", new JsonArray());

		final JsonArray assignedVars = new JsonArray();
		for (final IProgramVar v : trans.getOutVars().keySet()) {
			assignedVars.add(v.getGloballyUniqueId());
		}
		obj.add("assigned_vars", assignedVars);
		return obj;
	}

	private static JsonObject varMapToJson(final Map<IProgramVar, TermVariable> vars) {
		final JsonObject obj = new JsonObject();
		for (final Map.Entry<IProgramVar, TermVariable> e : vars.entrySet()) {
			obj.addProperty(e.getKey().getGloballyUniqueId(), e.getValue().toString());
		}
		return obj;
	}

	private static String formulaToSmtLib2(final LinearTransition trans, final Script script) {
		final List<Term> disjuncts = new ArrayList<>();
		for (final List<LinearInequality> polyhedron : trans.getPolyhedra()) {
			final List<Term> conjuncts = new ArrayList<>();
			for (final LinearInequality ineq : polyhedron) {
				conjuncts.add(ineq.asTerm(script));
			}
			disjuncts.add(SmtUtils.and(script, conjuncts));
		}
		return SmtUtils.or(script, disjuncts).toString();
	}
}

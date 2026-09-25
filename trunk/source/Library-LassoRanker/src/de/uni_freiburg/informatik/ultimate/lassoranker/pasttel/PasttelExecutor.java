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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Invokes the PaSTTeL CLI binary on a lasso already serialized to JSON (see {@link LassoJsonWriter}) and returns its
 * structured "-o json" result (see PaSTTeL's report_json.h/AnalysisReport).
 *
 * Mode {@code BOTH} races termination and non-termination techniques in the same PaSTTeL process; LassoCheck only
 * uses it when the termination-direction and non-termination-direction {@code LassoAnalysis} preprocessing produced
 * the same lasso (see {@code LassoCheck.tryPasttelBoth}), since their NlaHandling settings otherwise differ
 * (over- vs under-approximation) and a verdict derived from the wrong-direction approximation would be unsound.
 * Within one call, PaSTTeL still races all its ranking-function templates (or non-termination techniques) internally
 * in parallel -- calling it once per lasso (rather than once per template, as LassoCheck's own LassoRanker path
 * does) is what actually exercises that parallelism.
 */
public final class PasttelExecutor {

	public enum Mode {
		TERMINATE("terminate"), NONTERMINATE("nonterminate"), BOTH("both");

		private final String mCliValue;

		Mode(final String cliValue) {
			mCliValue = cliValue;
		}
	}

	private PasttelExecutor() {
	}

	/**
	 * @return the parsed top-level JSON object of PaSTTeL's AnalysisReport, or {@code null} if PaSTTeL did not
	 *         produce a usable result (timeout, non-zero exit, malformed output) -- callers should fall back to
	 *         LassoRanker in that case, not treat it as an error.
	 * @throws IOException
	 *             if the binary itself could not be launched (e.g. not found).
	 */
	public static JsonObject run(final String binaryPath, final String jsonInputFile, final Mode mode,
			final int timeoutSeconds, final int cpus, final IUltimateServiceProvider services) throws IOException {
		// -val: re-check every synthesized certificate against the SMT solver before PaSTTeL reports it as
		// conclusive. Always on here, not opt-in: this is the one direct, independent check on the certificate's
		// own mathematical validity in this pipeline (PasttelResultMapper only checks that it *maps back*, not
		// that it *holds*; BuchiAutomizer's Hoare-triple checks only run once the certificate is already accepted).
		final String[] command = { binaryPath, "-a", mode.mCliValue, "-o", "json", "-t",
				String.valueOf(timeoutSeconds), "-c", String.valueOf(cpus), "-q", jsonInputFile };
		final MonitoredProcess process = MonitoredProcess.exec(command, null, null, services);
		// Grace period beyond PaSTTeL's own -t: PaSTTeL enforces the timeout itself and exits cleanly: this is a
		// backstop against the process not honoring it, not the primary timeout mechanism.
		final MonitoredProcessState state = process.impatientWaitUntilTime(timeoutSeconds * 1000L + 5000L);
		final String stdout = readAll(process.getInputStream());

		if (state.isRunning() || state.isKilled() || state.getReturnCode() != 0) {
			return null;
		}
		try {
			return JsonParser.parseString(stdout).getAsJsonObject();
		} catch (final RuntimeException e) {
			return null;
		}
	}

	private static String readAll(final InputStream in) throws IOException {
		final StringBuilder sb = new StringBuilder();
		try (BufferedReader reader = new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8))) {
			String line;
			while ((line = reader.readLine()) != null) {
				sb.append(line).append('\n');
			}
		}
		return sb.toString();
	}
}

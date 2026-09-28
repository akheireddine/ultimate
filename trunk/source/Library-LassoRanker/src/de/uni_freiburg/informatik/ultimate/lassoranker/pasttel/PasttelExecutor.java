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
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Invokes the PaSTTeL CLI binary on a lasso already serialized to JSON (see {@link LassoJsonWriter}) and returns its
 * structured "-o json" result (see PaSTTeL's report_json.h/AnalysisReport).
 *
 * LassoCheck only asks it for ranking functions ({@link Mode#TERMINATE}): non-termination stays with LassoRanker's
 * GNTA, whatever the backend. Within one call, PaSTTeL still races all its ranking-function templates (or non-termination techniques) internally
 * in parallel -- calling it once per lasso (rather than once per template, as LassoCheck's own LassoRanker path
 * does) is what actually exercises that parallelism.
 */
public final class PasttelExecutor {

	public enum Mode {
		TERMINATE("terminate"), NONTERMINATE("nonterminate");

		private final String mCliValue;

		Mode(final String cliValue) {
			mCliValue = cliValue;
		}
	}

	/**
	 * How long to wait for the rest of stdout once PaSTTeL has exited; a backstop, since it is normally all read.
	 */
	private static final long STDOUT_GRACE_MILLIS = 5000L;

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
				String.valueOf(timeoutSeconds), "-c", String.valueOf(cpus), "-q", "-val", jsonInputFile };
		final MonitoredProcess process = MonitoredProcess.exec(command, null, null, services);
		// Drain stdout while PaSTTeL runs, not after. MonitoredProcess pumps it into a 2 KiB pipe, and once the
		// process has exited it waits up to 200 ms for that pump to finish; a JSON report larger than the pipe (the
		// usual case, 2-6 KiB) would block the pump until someone reads, i.e. make every call 200 ms longer.
		final InputStream stdoutStream = process.getInputStream();
		final CompletableFuture<String> stdoutFuture = CompletableFuture.supplyAsync(() -> {
			try {
				return readAll(stdoutStream);
			} catch (final IOException e) {
				return null;
			}
		});
		// Grace period beyond PaSTTeL's own -t: PaSTTeL enforces the timeout itself and exits cleanly: this is a
		// backstop against the process not honoring it, not the primary timeout mechanism.
		final MonitoredProcessState state = process.impatientWaitUntilTime(timeoutSeconds * 1000L + 5000L);
		if (state.isRunning() || state.isKilled() || state.getReturnCode() != 0) {
			stdoutFuture.cancel(true);
			return null;
		}
		final String stdout;
		try {
			// The pump closes the pipe right after the process exits, so this returns at once.
			stdout = stdoutFuture.get(STDOUT_GRACE_MILLIS, TimeUnit.MILLISECONDS);
		} catch (final ExecutionException | TimeoutException e) {
			stdoutFuture.cancel(true);
			return null;
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			return null;
		}
		if (stdout == null) {
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

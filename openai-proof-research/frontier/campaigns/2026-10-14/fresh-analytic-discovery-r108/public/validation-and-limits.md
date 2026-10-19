# Validation, failed routes and limits

Original prose CC BY 4.0. These are author checks, not an independent review.

## General proof checks

The full proof was developed after the scope freeze. It never replaces the frozen left-hand side by Gaussian, commuting, separable, energy-capped, finite-dimensional or local states. The finite-support witness is only a tool inside a contradiction argument for the affine regularized objective; it does not replace the theorem's domain.

The hostile cases checked analytically are:

* **Rank-one Gaussian candidate at positive entropy:** adding a tiny null-mode occupancy costs output entropy only linearly but frees input entropy at order (t\log(1/t)\); the compensating decrease in the occupied mode strictly lowers output entropy. This proves the chosen reference is interior, rather than assuming it.
* **Wrong scalar normalization:** (K/\sqrt\lambda\) can expand Euclidean norms even when the correct KKT identity holds. The exact example below records that failure. The author proof instead normalizes both thermal Hamiltonians and uses the resulting unitary in every comparison.
* **Noncommuting noise:** the two congruences for (R\) and (R+I\) and the defect convolution retain matrix order. Separate input/output reference eigenbases do not make (K\) diagonal. No independent-mode tensorization of the input state occurs.
* **Arbitrary non-Gaussian/squeezed inputs:** the hypothesized witness is an arbitrary state and is never assumed to have a Gaussian covariance extremality property. Only the chosen comparison reference is Gaussian.
* **States with bad scores or missing high moments:** the original witness needs finite energy only. Seventh moments and finite defect norms are proved for the new Gibbs minima, using the logarithm bounds. They are not transferred to the witness or all near-minimizers. The old EPnI equality branch's infinite-score obstruction therefore is not ignored.
* **Displacements and mixture means:** the exact covariance remainder is (\kappa(1-\kappa)\mu_\gamma\mu_\gamma^*\). Its sign in cancellation is negative. The relative-entropy penalty controls the input mean separately from the centered defect.
* **Different thermal temperatures:** the relaxation has common decay rate one and reference-dependent noise, so covariance passes through (K\). A proposed inverse-temperature-dependent drift was abandoned; no positivity/complete-positivity claim for that drift is used.
* **No uniform energy cap in the theorem:** for a fixed hypothetical violation the positive relative-entropy term supplies a uniform energy bound only on its auxiliary minimizing sequence. The final contradiction eliminates that witness. No constant uniform in all possible input energies is required.
* **Pure endpoint:** it is obtained from faithful mixtures with a fixed finite-energy thermal state and continuity of both entropy minima; the proof does not use a divergent (h(0)\) in KKT.

## Exact finite diagnostic

`check_algebra.py` uses only Python rational arithmetic, with a positive Taylor-series tail bound for exponentials. It chooses

\[
H_0=\operatorname{diag}(1,4),\quad H_1=\operatorname{diag}(1,9),\quad
\lambda=1/25,\quad K=\begin{pmatrix}3/25&-12/25\\2/25&9/50\end{pmatrix}.
\]

Set (R=(e^{H_1}-I)^{-1}\), (Q=(e^{H_0}-I)^{-1}\), (B=Q-KRK^*\). The script proves (B>0\), (\|K\|<1\), (K\) invertible, and both required strict slack inequalities for (\varepsilon=1/100\). Consequently (E=L^{-1}BL^{-1}>0\) gives an admissible actual channel. It checks (K^*H_0K=\lambda H_1\), unitarity of the corrected normalization, and (KK^*Q\ne QKK^*\).

The naive normalization sends the second unit vector to a vector of squared length (657/100>1\). Thus its arithmetic comparison cannot be justified by Euclidean contractivity. This is an obstruction to one proof map, not a counterexample to (T). The example is a stationary reference; the script does **not** claim it is a global Gaussian optimizer. `algebra-check.json` records exact rational lower bounds. These finite checks neither prove the general theorem nor establish substantiality.

## Retrieval and execution failures

The primary HTML requests for `1705.00499v2` and `1312.2251v3` returned HTTP 404. Successful inspected versions are v1 and v2 respectively. All successful original bodies and their text views are private and separately hashed. Other web search hits were navigation only.

Two exploratory Python invocations found unavailable optional packages (`bs4` and `sympy`). No package was installed; standard-library HTML parsing and exact fractions replaced those attempts. After context continuation, two reads initially used the parent math directory rather than the research repository and returned file-not-found; they were immediately repeated with the explicit research cwd. No files were written by those failed reads. Several combined source/history reads exceeded output budgets; the reading ledger makes conservative extent claims and records recovered ranges. No failed or truncated read is treated as complete semantic inspection.

All 74 pinned raw source retrievals succeeded and match their Git blobs in the complete tree. Only nine selected-family files are fully claimed read; the rest have individual partial or unread statuses. Selected primary text versions are fixed by their arXiv version URLs, not by generated HTML display dates.

## Integrity control boundary

`verify.py` is offline and read-only. It requires an externally supplied expected manifest SHA256, checks exact owned file/directory inventory, rejects symlinks, compares external anchors, checks pinned raw URLs and Git blob headers against all 13,223 complete-tree entries, verifies all primary byte/view hashes, and enforces the original scope hash. It does not fetch, repair, reseal, run a proof assistant, or certify mathematics. A changed external ledger correctly causes a mismatch; the verifier does not silently exempt it.

The preseal control receipt records the actual integrity checks and deliberate in-memory corruptions. Those controls are not a correctness or contribution PASS. No third-party body is included under the public original-prose/code directory. No shared file was edited, no stage/commit/reset operation occurred, and no publication, browser UI, messaging, nested delegation, formalization, or manuscript/release production was performed.

The runtime reported GPT-6 Astra/high. This child did not launch or reconfigure a provider, model, reasoning mode or service tier; the requested normal/default service-tier setting is owned by the parent/orchestrator and is not independently evidenced by this local packet.

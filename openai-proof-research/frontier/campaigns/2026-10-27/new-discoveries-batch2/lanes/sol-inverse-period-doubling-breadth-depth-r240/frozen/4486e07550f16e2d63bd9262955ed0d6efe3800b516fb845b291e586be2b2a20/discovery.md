# Almost perfect additive complements: full source question remains open here

The sustained source is Wouter van Doorn, Boning Liu and Quanyu Tang, *On almost perfect additive complements*, https://arxiv.org/html/2610.35027v1, Conjecture 1.3. Its abstract history https://arxiv.org/abs/2610.35027 lists only v1, 26 October 2026 08:40:02 UTC. No DOI is asserted. The literal objects are A,B subset of the nonnegative integers, both infinite, with every sufficiently large integer in A+B. Write A(x)=#(A intersect [0,x]) and similarly B. “Almost perfect” means A(x)B(x)-x does not tend to +infinity. The conjecture is the universal assertion

    limsup_{x→∞} A(x)B(x)/x ∈ {3/2} ∪ [8/5,2].

It is NOT merely the already-public 3/2 lower bound, not only unique representation for every n, and not a finite prefix or one radix family. All initial exceptional integers and all real x tending to infinity belong to its scope. Source Theorem 1.1 is already proved; it receives no nomination. All body bytes were saved, copied and SHA256-bound before the first primary body read. Exact URL/UTC/hash receipts are http.jsonl and primary-freeze.json. The latest abstract was checked after v1 body retrieval and lists no later version.

## Actual closest bodies and the full known adaptation

Read the primary introduction, Lemmas 2.1–2.5, Section 3 proof, Section 4 mixed-radix bounds, and Sections 5.1–5.3. Read Gabardo–Lai, *Spectral measures associated with the factorization of the Lebesgue measure on a set via convolution*, https://arxiv.org/pdf/1311.2209, obtained v1 (9 November 2013 20:37:57 UTC), Theorem 2.2, Lemmas 2.3–2.5 and its full iterative factorization proof (PDF pp6–10). Source bibliography identifies J. Fourier Anal. Appl.20(2014)453–475; the published body was not separately authenticated. The theorem is explicitly attributed there essentially to Lewis; no new factorization machinery is claimed.

Also read Zhang, *A sharp bound for additive complements*, https://arxiv.org/html/2610.29963v1, introduction, Lemma 2.1, Lemma 4.2 counting/convolution proof, and Sections 5–6. This is an October 2026 discrete proof of the SAME 3/2 threshold, not Conjecture 1.3's gap. The body reports a 5 August 2026 announcement of the threshold; that announcement was not independently retrieved. Read Ma, https://arxiv.org/html/2205.04128 (render says v1, 9 May 2022), Lemma 2.1 and its mixed-radix count/limsup construction. Published Ma and 2024 Bárány–Fang–Sándor full bodies were not separately read.

Here is the full applicable bridge, rather than an appeal to familiarity or shortness. Set r(n)=# representations and C(N)=# pairs a,b≤N<a+b. Exactly,

    A(N)B(N)-N = 1 + Σ_{n≤N}(r(n)-1) + C(N).

For large n, r(n)≥1. Bounded excess on a subsequence forces the nondecreasing tail sum of nonnegative integers to be bounded, hence r(n)=1 eventually. Taking a further subsequence N_j gives bounded C(N_j) and A(N_j)B(N_j)/N_j→1. The normalized counting measures have subsequential limits μ,ν with μ*ν=uniform[0,1]: exceptional representations and crossings have O(1) total mass before normalization. Compactness and continuity of convolution prove this statement, without assuming the sets are perfect.

Gabardo–Lai classify μ,ν by alternating convolution digit factors of radices M_i≥2, either stopping with one Lebesgue tail or continuing infinitely. Their proof partitions Fourier zeros of the uniform measure, extracts a periodic factor by Lemma 2.5 and iterates. For the first two factors, let u=M_1 sup(supp ν), which lies in [1-1/M_2,1]. Support endpoints and the first two digit copies give normalized-product lower bounds

    max{2/(2-u), 2/(2-M_2+M_2 u)} ≥ (2M_2+2)/(M_2+2) ≥ 3/2.

The first fraction increases with u, the second decreases; equality in their maximum's minimum is at u=M_2/(M_2+1). Distribution functions converge at common continuity points; approaching the selected endpoints from above transfers these LOWER bounds to the original global limsup. In the trivial limiting pair the source's gap/difference count proves limsup=2. This completes the known 3/2 bridge, not the gap conjecture. Source Theorem 5.2 further states the analogous deeper-factor bounds; no credit is taken for restating it.

For genuinely perfect pairs the full established radix classification and Ma's formula give a complete gap adaptation. Let d_k≥2, D_0=0, D_k=(1-D_{k-1})/d_k and s=liminf D_k. The product limsup is 2/(1+s). If G=limsup d_k<infinity, then d_k≤G eventually and 0<D_k≤1/2. The exact identity

    D_k=(d_{k-1}-1)/(d_k d_{k-1})+D_{k-2}/(d_k d_{k-1})

implies D_k≥(1+D_{k-2})/(2G), hence s≥1/(2G-1). Along d_k=G infinitely often, min{D_{k-1},(1-D_{k-1})/G}≤1/(G+1); thus s≤1/(G+1). If G=2, the eventual recurrence contracts to s=1/3 and the limsup is 3/2. If G≥3, 2/(1+s)≥2(G+1)/(G+2)≥8/5. If radices are unbounded, a subsequence has D_k→0 and limsup=2. This proves every perfect-subclass parameter, but there is no supplied classification of EVERY almost-perfect pair by a single global radix sequence. The source's modular lifts also show why replacing “almost perfect” by “perfect” is not a justified premise change.

## Residual universal obligation

A plausible route would prove the following stability/transfer dichotomy: for every almost-perfect pair whose global limsup is <8/5, bounded-excess subsequential factorization forces its global limsup to be ≤3/2. Together with the known lower bound this proves Conjecture 1.3. This dichotomy is NOT proved here. A single all-binary limiting pair along selected N_j only controls scaled counting functions at those scales and supplies lower bounds; it supplies no upper bound at all intervening or later peak scales. Moving a supremum or limsup through that subsequential convergence would be invalid. Nor do the exact local radix identities construct such a global sequence for arbitrary A,B. Zhang's gap argument under a <3/2 hypothesis cannot be applied under <8/5 without a new hypothesis bridge. No complete classical subsumer for this residual was identified, and no substantive exclusion is made from elementary length.

## Other reconnaissance and exclusions

Finch, https://arxiv.org/html/2610.34300v1, history v1 25 October 2026 13:59:30 UTC, is a second fresh source lead. Conjecture 14 asks N_A(4m²+3)=4 for EVERY m≥0 and N_A(3^(2j+1))=4 for EVERY j≥0 for x_1=...=x_{k-1}=0,x_k=1,x_n=x_{n-1}+x_{n-k}² mod3. Its Propositions 11–13 and Addenda were read. The capture criterion does not prove either family ever captures; a uniform generation argument is absent. No proof or large finite survey is claimed. Conjecture 23 has a literal small-index defect: k=2 has pure cycle 0,1,1,2, μ=0, but its required r≥k+1 makes first run start r=5 and z=9. This is only a parameter/definition correction, not eligible discovery credit and not a full all-k law. No PROOF.md is created for it.

Shalev2610.34482 is already public proof of five Au identities; no fresh question selected. He2610.37155 announces a positive lattice-order construction, and Gubarev2610.34463 announces/proves nil-ring counterexamples; these are public-resolution reconnaissance exclusions, not our discoveries. Their introductions/statements were inspected; no full independent audit of those proofs is claimed. Matching2610.37512, valuation2610.37356 and PIR2610.36447 hit r194/r199 investigations before sustained work, were not reopened, and receive no fresh count. Old totient/reliability/UUD/matrix/Guo/power-sum/Sirola targets stayed parked.

## Bounded novelty, provenance and diagnostics

1527 qualified canonical original-path reference snapshots were refreshed using r195's qualification plus r198 bindings and direct lane reports, retaining the corrected r193/r194/r197 indexes and adding r199's index. 1075 additional inherited reference aliases were copied and screened separately; equal hashes never establish provenance, and copied histories were not recursively promoted. r111–113 original paths remain in the canonical inventory. All active research and administrative documents are snapshots, not immutable live scientific dependencies. Changed-records.json preserves refreshed bodies; broad displayed reads were bounded/truncated, so this is not a claim that all historical text was read exhaustively.

Exact arXiv/title/author and statement-family screens preceded investment; exact-alias-screen.json also screens the closest Gabardo dependency. No DOI is supplied by the obtained main-source metadata, so no invented DOI clearance. Exact matches to the two target sources were absent from this bounded inventory, including the separately retained legacy aliases. Current HTTP registry catalog screen finds no match but is dated 9 September 2026, commit c74ecadd; no current head/tree or complete proof-body history was obtained. Subscription indexes, all citing bodies, current global registry history and worldwide priority are uncleared. This is fresh-to-the-screen, not demonstrated worldwide novelty.

checks.py and run-checks.sh are exact, capped, runnable diagnostics: 2929 rational two-support controls, 15309 radix steps and the uncredited k=2 capture issue. They validate arithmetic and implementation only. No finite results prove Conjecture1.3 or14. All commands use the prescribed guard; exceptions/failures are recorded candidly in FAILURES.md. No shared edits, git, browser, external messages/uploads, MathDB edits, Lean or manuscript work. Counts9additional/39total,next40 unchanged.

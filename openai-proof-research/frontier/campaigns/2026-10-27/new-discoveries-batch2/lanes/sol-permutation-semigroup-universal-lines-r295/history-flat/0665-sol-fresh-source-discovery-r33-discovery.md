# Fresh source investigation r33 — full target unresolved, credit 0

## Literal selected question and source fidelity

For every integer n>=1 and every Hermitian positive-semidefinite B in M_n(C) with EVERY diagonal entry equal to 1, does there exist a permutation sigma of all n coordinates such that

    || strictLower(P_sigma B P_sigma*) ||_op <= (2/pi) ||B||_op ?

This is the entire sharp-constant question, not a fixed dimension, real-only restriction, prescribed permutation, expected squared-vector bound, or Schatten-p estimate. A strict refutation must give ONE actual such B and establish violation for EVERY permutation. A successful ordering in finitely many examples proves neither alternative universally.

Actual source: Oswald–Zhou, *Correction: Random reordering in SOR-type methods*, Numer.Math.154(2023)521–525, published11August2023, Section1 Eq(2), explicit conjecture at bottom of p522. Publisher full HTML and PDF obtained; p522 rendered/read. Both complex Hermitian scope and unit diagonal are explicit. Source PDF SHA256454ed50c725080b099a8f72fb7c8dcf3045c01b428e165aca566a417e6209ab8. Exact URL:
https://link.springer.com/content/pdf/10.1007/s00211-023-01365-9.pdf

Publisher full body:
https://link.springer.com/article/10.1007/s00211-023-01365-9

Early live leads were actual current AIM568 and clopenOP00384:
https://raw.githubusercontent.com/MColbrook/AIM/8729eab98bafe409b66c5e39253bf56569a62327/problems/568-sor-permutation-sharp-constant.md
https://clopen.solutions/OP-00384/
Their open status is only a lead, not novelty clearance. The correction's conjecture survives the original paper's older mistaken auxiliary bounds. Original actual publisher body read; current arXiv record1510.04727 has latestv2,20July2016. The2023 correction is later and controls this investigation. No later correction/resolution located in this bounded screen.

## Early public and closest-body screen BEFORE diagnostics

Read rules, ledger, NEXT, prior context, upstream metadata/catalogue and recent summaries. Avoided all assigned/excluded families, particularly r30matroid, r31Hankel and r32Brownian. AIM495 binomial exact optimal-support scaling and AIM617 polynomial convex-difference decomposition were considered from current entries, not independently cleared at primary-body level; no result about them is claimed.

Current exact-title/author/triangular-truncation searches performed29October2026, queries in search-log.json. Correct Zhou author identity was established by the actual https://zhou.ac.cn/ homepage: the listed2016 truncation paper,2017 SOR paper and2022 conjugate-transform paper match the source. Its current preprint list includes2026 harmonic-analysis papers, none described as this sharp permutation result; the list itself is not complete citing-body coverage.

Actual relevant bodies read:

1. The2023 correction, all three mathematical sections, including its proof of E=(1/3)H²+(1/6)diag(H²), H=B-diag(B), and the paving induction. It gives C<122.3 for PSD matrices; the earlier32.42 derivation is withdrawn. These are SOURCE facts, not discoveries. The displayed average is a bound on each fixed vector averaged over permutations; it does not give a common permutation uniformly over all vectors at the sharp threshold.
2. The2017 publisher original, including triangular-truncation/reordering theorem and paving proof, interpreted through the2023 correction.
3. Zhou2022 *Properties and applications of a conjugate transform on Schatten classes*, DOI10.1186/s13660-022-02863-4, actual full publisher body, especially the permutation assertion(iv) and its proof by paving/induction with C=2(gamma_epsilon-1)/(1-epsilon). Existence of some dimension-independent constant does not give2/pi. The proof's blockwise triangle estimates are much too large for that constant.
4. Zhou2016 *Triangular truncation and its extremal matrices*, DOI10.1002/nla.2045, actual author-hosted published-format PDF https://zhou.ac.cn/articles/truncation.pdf (SHA25692c6ee76788808adc41649d0b395aff09acdb193350ddfba453cf318f3477155). Read fixed-order Toeplitz obstruction, Theorem1 and spectrum-shifted PSD example. Theorem1 page9 rendered/read. It concerns a given coordinate ordering; its logarithmic lower bounds cannot themselves refute an existential permutation bound. This is the closest classical obstruction, explicitly credited.
5. Long, *Sharp noncommutative Hilbert and Riesz inequalities: classification and spectral corrections*, latest https://arxiv.org/html/2610.10158v2 (25October2026; v1submitted7October). Actual Section8.6.1 Corollary8.11 and full proof read: for1<p<infinity, sup_n||T_n:S_n^p->S_n^p||=csc(pi/p), retained diagonal triangular projection, also finite-algebra coefficients. This is not an operator-norm permutation theorem. Passing through ||X||op<=||X||p<=n^(1/p)||X||op introduces a dimension factor; csc(pi/p) diverges as p->infinity, and this direct bound is at least1 even before handling diagonal deletion. Thus this concrete norm-transfer bridge does not give2/pi. No truth audit of that paper attempted or needed.
6. Pinned OpenAI quadratic strong-operator paving theorem accepted true as instructed. Actual introduction/main theorem and definitions read at
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quadratic-Strong-Operator-Paving-over-Arbitrary-Maximal-Abelian-Subalgebras-September-25-2026/build/source/sections/introduction.tex
It supplies r_epsilon=ceil(400000000epsilon^-2)+ceil(4/epsilon)+1 blocks, with compression and diagonal subtraction. In finite dimension the compression can be forced to I by testing a full orthonormal basis at delta<1/sqrt(n): any nonzero complementary projection has sum_i||(I-q)e_i||²>=1. For zero-diagonal H the diagonal subtraction a then has norm<=epsilon||H||, giving pinching bound2epsilon||H||. Inserting this into the source's block induction produces constants involving r_epsilon, far above2/pi. This particular explicit subsumption bridge fails; no claim that every possible use of paving is impossible. No upstream truth audit.

No matching full public proof/refutation was located. This bounded screen is NOT a novelty PASS, worldwide priority claim, or exhaustive specialist/citing-body review.

## Ordinary route attack and falsifiers — all uncredited

### Why an unpermuted counterexample is insufficient

The classical Hilbert-kernel mechanism can be made source-admissible. For n=512 and zero-based indices set A_ij=1/(i-j) for i!=j, A_ii=0, and B=I+iA/4. The standard Fourier symbol of A has modulus<=pi: compression of multiplication by its sawtooth Fourier series gives ||A||<=pi. Equivalently the quadratic form is an integral against that bounded symbol; this is the usual Toeplitz argument explicitly discussed in Zhou2016. Thus iA is Hermitian, B has unit diagonal and eigenvalues in[1-pi/4,1+pi/4]; in particular B is positive definite and ||B||<2, using pi<4.

For the all-ones vector, ||strictLower(B)1||²/||1||²=sum_{j=0}^{511}H_j²/(16*512). The checker proves this exact rational number exceeds16/9, with H_0=0,H_j=sum_{k=1}^j1/k. Hence this particular ordering has norm>4/3>(2/pi)||B||, using pi>3. This is a classical fixed-order obstruction, NOT a refutation: no assertion is made about its minimum over permutations. It earns no credit and warrants no Lean. The retained rational computation is only a sanity check of the known mechanism, not a new universal result.

### Why structured Fourier candidates did not survive

The first floating diagnostic covers88 actual Gram/circulant-projection matrices:48 random unit-row Gram matrices of dimensions3..6 (every permutation evaluated), plus40 structured/larger examples n=8,12,16,24,32 (160random orders followed by at most3local-swap sweeps). Seed3301;39,228total order evaluations. Every example has a found order below2/pi. This is finite floating evidence, no exact all-permutation or universal certificate. Some original Fourier orderings exceed2/pi; that does not make them source counterexamples.

For an elementary reason, the half-frequency projection examples reorder into the two-orthonormal-bases Gram form [[I,U],[U*,I]], U unitary. Then B=[I;U*][I,U], B²=2B, ||B||=2; putting one basis before the other makes strictLower(B)=[[0,0],[U*,0]] of norm1. Thus the ratio is1/2. This known special-case block computation explains a false numerical lead; it is explicitly NOT a candidate or extra count.

Two additional diagnostics retain failed witness searches: all40,320orders for the8x8 Walsh-two-basis Gram; and1,000sampled orders for its32x32 analogue. Even the largest norm found in these runs is below the source threshold. Neither calculation establishes a universal statement or a floating exact norm certification. Their poor value as source-counterexample routes is recorded, not hidden.

### Why averaging remains a gap

The corrected source E formula has been independently checked by exact integer summation:270entry identities across3real symmetric zero-diagonal matrices at each n=2..6,2,616permutations total. This verifies implementation of an ALREADY PUBLISHED identity. For J_3 the averaged matrix has norm5/3 while every individual L_sigma L_sigma* has norm(3+sqrt5)/2>5/3. Thus replacing an average operator's norm by an upper bound for the norm of some individual summand is not a valid general inference. J_3 itself satisfies the source conjecture, and is not a refutation. The full issue is choosing one order that controls all unit vectors, without losing the sharp constant.

## Current registry chronology/coverage

At11:05–11:06UTC live heads: AIM8729eab98bafe409b66c5e39253bf56569a62327, OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a, Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5; unchanged fromr32. Their complete inherited scoped inventories are hashed/referenced in registry-screen.json, with relevant path hits preserved. OpenAI scope is preprints13,578entries; AIM3,541; Count183; main69. A path hit is merely a lead: actual closest theorem bodies were compared above.

Omega dev advanced to5f94e981243583f47844e82a3f385c15372fb4b7. Complete compare from953086aaf8dbba50658ea758d655753a486ce219:3commits/7files; latest commit11:03:40UTC. Added FibonacciAtomic kernel/provenance files and changed predictive-wave documentation, no triangular-correlation target. Inherited complete D5(12,497)/Problems(1,544) atf9745e6a plusr32's4commit/5path solenoid delta plus this complete small delta provide current scoped path coverage (D5twoaddedLeanpaths; Problems unchanged). Whole-dev coverage remains incomplete; never infer complete repository coverage from a truncated tree. Registry-screen.json hashes both inherited inventories and the prior delta; actual new compare retained locally. No relevant same-scope manuscript found through this bounded path+semantic screen.

Access failures: initial wrong Omega repository/branch guess422, then correct known repository endpoint; guessed clopen category404, then its actual public search and target record. Neither was403/429/challenge. No blocked endpoint bypass, login, retry loop, external message, upload, account action or browser tab. An attempted HTML parser import lacked bs4; the retained extractor uses standard library only. Exact requested and final URLs, timestamps, hashes and failures are inhttp.json. Publisher adds cookie-error query parameters but returned full actual public bodies, not a challenge.

## Disposition and reproducibility

Full ordinary theorem/refutation remains UNRESOLVED. Strongest falsifier of any claim of completion: there is no all-dimension sharp ordering construction, nor an admissible matrix with EVERY permutation strictly above2/pi. Fixed-order logarithmic obstructions, polynomial-time heuristics, finite diagnostic agreement, known block cases and source identities do not satisfy the assignment.

Run `bash run-checks.sh` from this lane or pass its full path. Exact checks and deterministic diagnostics run serially under512MiBAS, CPU<=45seconds and individual wall<=55seconds, BLAS1. guard.py samples process-group RSS every45ms, kills over2800MiB or60seconds. Final replay is fresh Python source only; no candidate oleans or Lean used. Final guard reports retain sampled peaks; transient unsampled peaks cannot be excluded. Initial lightweight inspection snippets were not all RSS-monitored; candid limitation, no formal/large job was run.

No PROOF.md, Lean declaration, type/axiom certificate, paper, independent review request, nomination, acceptance or credit. Consequently candidate Lean actual-type/axiom/origin/unsafe auditing is not applicable; there is no formal endpoint to audit. Any future full candidate must first undergo root-owned independent review, then the stipulated pinned Lean4.34.1/mathlibd13f23... strict serial/source-only replay and actual declaration audit. Counts remain5/30additional,35/60total; credit0. Solo; only assignedr33lane written. Root owns acceptance.

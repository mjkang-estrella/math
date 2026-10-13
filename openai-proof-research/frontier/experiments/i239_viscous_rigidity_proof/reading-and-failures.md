# I239 — reading limits, attempted objections, and provenance

## Independent outcome

PASS for finalized I236 analytic SHA-256 `a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`. A pending review and early mathematical note were written before completion, then replaced by the final verdict and complete independent calculations. No substantive repair was necessary. No count change or contribution verdict is claimed.

I read the complete finalized I236 report, analytic proof, reading record, literature record and input authentication. AGENTS.md and sources/upstream.json were read completely. The prior I224/I228/I229/I231 material was supplied by the user; no other gate or live sibling output was opened. Local source reads were confined to the pinned family and the named primary excerpts. Exact ranges are in literature.md and input-authentication.json.

## Objections checked and resolved

- A scalar support maximum could be useless if maximizers hit the spatial boundary. The strict extra curvature supplies a common r²/2 boundary gap, and the uniform time modulus preserves a gap on a common interval.
- Semiconvexity of that maximum initially gives only one increment bound for u. The reverse bound comes from a new support at the second time. It does not require a false lower-test inequality for the original maximum.
- A truncated cone infimum might fail to be Lipschitz or fail to recover v. The positive slope difference L-Lip(u) confines every minimizer to the interior and forces zero displacement whenever the regularized function equals u.
- Ordinary mollification does not preserve G_tau-subsolutions. The proof only asserts this preservation for autonomous sup/inf convolutions. Linear mollification enters later, under one-sided Hessian control for Fatou.
- Almost-everywhere nondivergence inequalities alone could ignore singular curvature. At fixed convolution scale, measure Hessians and one-sided Fatou retain the favorable singular sign. The lower bound is uniform in smoothing, not in convolution scale; the limits are correctly ordered.
- Uniform value convergence alone does not justify convergence of exponential gradient fluxes. The fixed Lipschitz bound and optimizing-displacement argument give a.e. gradient convergence along a countable sequence and bounded-flux domination.
- Harnack for weak solutions does not automatically apply to a weak supersolution. The replacement w is a genuine weak solution. Energy comparisons, Harnack, zero trace, and continuity give zero on each sphere; varying radii supplies local equality.
- The source's common-time rule could fail after adding a trace term if weighted jets or synchronization errors were mishandled. Dividing jets cancels theta_i, and the added common translation vectors annihilate the synchronization Hessian. Eta is sent to zero before lambda goes to infinity. The limit uses only horizontal test derivatives.
- Loss of second moment in the extremal weak measure limit could destroy contact. The sandwich forces equality and in fact prevents that loss. Separate center/radius subsequences preserve every fit, including boundaries.

No actual counterexample to the submitted theorem or failed step survived these checks.

## Actual counterexamples to excluded shortcuts

I independently checked the algebra of I236 Section 7. For p_N determined by p_N³/3+tau p_N=Nx+1/3+tau and f_N'=p_N, V_N=f_N-Nt²/2 solves G_tau=0. At the indicated point its Hessian makes the change under p->p+delta proportional to N(2delta+delta²)/(1+tau), excluding a Hessian-independent gradient-Lipschitz constant. For p³/3+tau p=x, V=f-t²/2 is another smooth exact solution. Any nontrivial nonnegative even smooth spatial probability mollifier gives G_tau[V*eta](0,t)=tau int eta/(p²+tau)-1<0. These are local smooth PDE examples; neither is alleged to satisfy global FIT.

The fit-only function t log|t| is spatially affine but not time-Lipschitz at zero; it fails the required subsolution inequality on negative times. It therefore excludes deleting the PDE from Lemma 2.1, not the lemma itself. The infinite-tau limiting equation with FIT still admits sin t. No p-gradient convergence or uniform-in-tau estimate is inferred.

## Retrieval and reading limits

Pinned README and sections 02–05 were freshly retrieved in memory from immutable raw URLs. Every retrieved byte matched the reused local file and every Git blob matched the complete family tree. Only the exact family prefix was listed, not giant history or unrelated manuscripts.

Julin–Juutinen pages 1–6 and Crescimbeni–Forzani–Perini pages 1–5 were freshly retrieved and extracted in memory; they matched the existing primary excerpts exactly. Ohnuma–Sakaguchi pages 1–2 were also matched to fresh extraction; both its reused excerpts through page 4 were read. No full unread PDF was retained and no source copy was written.

One combined source display returned a truncation notice near the transition from pinned text to primary text. The decisive sum-rule contract and both complete text excerpts were subsequently read in separate bounded ranges. No conclusion depends on text lost to that truncation. No retrieval failed. Trudinger was read as an existing primary page image; its other pages were not read in I239. Sánchez Morgado was read only through the page-2 equations, with the exact line range recorded.

No generic REG_tau search was conducted. The known operator and excluded comparison papers were checked only as needed for the proof interface. References named in their bibliographies were not presumed read.

## Work restrictions

Only the five authorized files were written: the I239 review, analytic-check.md, reading-and-failures.md, input-authentication.json, and the I239 literature.md. No I236 file was changed. No subordinate agents, live gate reads, shared edits, research code, numerical tests/scans/experiments, snapshots, seals, staging, commits, or publication. Commands were confined to reading, bounded lookup, retrieval/extraction, authoring these notes, and provenance hashing/serialization. Detached hashes are returned separately; the manifest contains no self-hash.

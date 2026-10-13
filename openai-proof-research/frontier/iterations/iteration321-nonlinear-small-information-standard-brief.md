# I321 — nonlinear small-information endpoint, new research round

Prepared new delegated round; GPT-6.1 Sol, high reasoning, Standard service. Work only in openai-proof-research and read AGENTS.md and sources/upstream.json. No child agents, live sibling reads, git, publication, shared-index edits or numerical scans. Fourteen findings remain accepted toward twenty. Do not change any acceptance or count.

## Full target, retained without narrowing

For X uniform on {-1,1}^n and arbitrary u:X->[-1,1], define psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2, I(u)=E psi(u)-psi(Eu). When I(u)=psi(a), define Delta_r(u)=psi(ra)-I(T_ru) and d_a(u)=min_(i,s=+-1)E|u-s aX_i|². For fixed 0<a1<1 and 0<r0<=r1<1, prove or refute with an exactly normalized family:

    d_a(u)<=C(a1,r0,r1) a^(-4) Delta_r(u)

for all n>=1, 0<a<=a1 and r in [r0,r1]. Original endpoints, rare events, arbitrary bias and arbitrary complexity are included. The exponent four is already necessary even on one bit. Compact-rectangle R020 does not supply its endpoint rate.

## Completed earlier research and exact gaps

Read the complete finalized I313 report `frontier/iterations/i313-small-information-endpoint-research.md`, SHA256 d95ef78eacabdf52c0ce8d46a36f96cb18d06047e4fff61f26cade856319cc75, and full analysis `frontier/experiments/i313_small_information_endpoint/analysis.md`, SHA256 ab4f64ae00065ebb433855ea01e996747fc986acd5cb3e4f14e1d66a3f054024. Also read its failure log and source/authentication record. Full S313 was explicitly UNRESOLVED. Its partials are not new stipulations: audit any operation you use.

B313 gives equivalence of d_a and B=m²+q-max_i uhat(i)²+H, where m=Eu, q=sum_singletons uhat(i)² and H is higher Walsh mass. Q313 improves compression to a constant independent of a, so an increasing-kernel theorem would suffice. A313 proves full sharp a^(-4) stability for bounded affine kernels by averaging one-bit capacity and quantitative Jensen; general nonlinear fields do not have its symmetry/generator identity. L313 proves the target in a conservative radius ||u-s aX_i||_2<=c a^M, M=max{4+1/theta,4/(qout-2)}, but there is no quantitative global entrance to that shrinking radius. Higher Walsh mass alone cannot select a soft coordinate: exactly normalized two-coordinate affine fields have H=0 and nonzero d_a. Uniform fourth-order expansion is false for arbitrary low-information kernels; the exactly normalized rare spikes and rare Boolean outputs in I313 expose this but are not counterexamples to S313. Gaussian strictness/compactness and fixed-degree invariance have absolute errors and cannot be inserted at scale a^4 B without payment. Noise suppresses high modes, so a production estimate on a smoothed field alone does not pay the original distance.

The parent one-bit note is `frontier/iterations/i313-small-information-endpoint.md`. The reviewed full compact-rectangle proof is `frontier/reviews/i304-global-soft-proof.md`, SHA256 ebe55bd375f8eebd9956c6cfbd251135703d1d6c7cc137fd41a0ac2c807e0d92, with full analysis `frontier/experiments/i304_global_soft_proof/analysis.md`, SHA256 c9a10e576923b20a4570762b1817d143d1da71c5e332a6a7e80a6bb66f01b9c5. These are finalized and may be read. Source production/one-bit interfaces remain restricted exactly as recorded in I313; do not apply N131 as a general nonlinear theorem.

## New parent operation to audit and develop

Read `frontier/iterations/i320-quartic-nonlinear-normal-form.md`, SHA256 bf6e890f84fc16732f4e02f3d0f56682e1ae221568efad8701d516e4d31d7379, plus its authentication. This is an UNREVIEWED finite-cube local calculation, not the desired theorem. It fixes an interior m, h=1-m² and first-level f with Ef²=h, then expands exactly normalized u_a=m+a f+a²g+a³j+O(a^4), where g is orthogonal to levels zero and one. The proposed optimal quadratic correction is g_opt=-(m/h)(f²-h), and the optimal quartic deficit coefficient is

    r²(1-r²)[kappa*m²/(3h)+(1-kappa)/6],
    kappa=sum_i c_i^4/h², f=sum_i c_i X_i.

The full normal form writes the additional nonnegative squares and higher-level terms. This corrects a misleading approach: at m²>1/3 the biased one-bit channel is not a transverse local maximizer, but the optimized quartic coefficient is still positive. The parent did not prove uniform remainders as m->+-1 or n->infinity. Verify the formula before using it. No numerical evidence is being used to infer the theorem.

One possible direction is a weighted decomposition that treats mean, other first modes and higher modes with their different Hessian scales (a^4, a², order one around a balanced coordinate). Earlier L131 used the smallest a^4 eigenvalue for every term, producing a very small radius. A valid argument must keep rare-event input terms positive and quantify the exact information correction; uncontrolled clipping or substitution of an affine projection is invalid. Alternatively construct a rigorous counterexample or a distinct global comparison. Do not merely re-prove the existing affine or local theorem and call it S313.

## Output

Write only `frontier/iterations/i321-nonlinear-small-information.md`; `frontier/experiments/i321_nonlinear_small_information/{analysis.md,reading-and-failures.md,input-authentication.json}`; `frontier/sources/i321_nonlinear_small_information/literature.md`, plus short necessary metadata. Record actual primary reading extents, immutable identities, failures, and inherited-versus-new proof scope. Do not retain new full external bodies or sections. Give a full proof if achieved, or the exact remaining unpaid operation and any new genuinely proved partial. Separate correctness from contribution and world priority. Return detached hashes of the five finalized outputs. No live I316/I317/I319 bodies may be read.

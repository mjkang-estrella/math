Uncredited ordinary result: MathDB 337039

Source: Nuyens–Cools, arXiv:1709.03449v1 (11 September 2017), Conjecture 1, primary body retained as 337039.pdf; retrieval hash/UTC in sources.json, recorded before extraction. Read Conjecture 1, preceding numerical check, Lemma 1 proof context, Lemma 5 and its proof, Corollary 1, and Section 6 Conclusion. No complete audit of the paper's analytic error-bound dependencies is claimed or needed below. Lemma 5 only covers Fibonacci generators via z^{-1}=±z. That bridge does not settle general units. Its symmetry examples do not contradict the literal equality.

Exact meaningful scope: every positive integer N and every integer z coprime to N; take least nonnegative residues, and inverse modulo N. The record says integers N; fractions and modular-residue convention require the positive-modulus source context. No outcome is claimed from an invalid or negative modulus. The two sums over 1≤k,l≤N−1 in the record are equal, with B1(x)=x−1/2 and B2(x)=x²−x+1/6.

Complete elementary derivation. Put b(0)=0 and b(k)=k/N−1/2 for 1≤k<N, and c(t)=B2(t/N), 0≤t<N. The cyclic autocorrelation A(t)=Σ_{k=0}^{N−1} b(k)b((k−t) mod N) obeys

A(t)=(N/2)c(t)+1/(6N)−(1/4)1_{t=0}.

To verify this without a Fourier theorem, first use f(k)=k/N−1/2 also at k=0. For 0≤t<N the product is f(k)[f(k)−t/N+1_{k<t}]. Here Σf(k)=−1/2, Σf(k)²=N/12+1/(6N), and Σ_{k<t}f(k)=t(t−1)/(2N)−t/2. Thus its sum is N/12+1/(6N)+t²/(2N)−t/2=(N/2)c(t)+1/(6N). Replacing f(0) by zero changes the t=0 sum by −1/4; for t>0 the two changed terms cancel since f(t)+f(N−t)=0. This also covers N=1 by the t=0 calculation.

Grouping the record sum by t=k−l gives S(z)=Σ_t A(t)c(zt mod N). Since multiplication by a unit permutes residues, Σ_t c(zt)=Σ_t c(t)=1/(6N) and c(z·0)=1/6. Hence

S(z)=(N/2)Σ_t c(t)c(zt)+1/(36N²)−1/24.

The substitution u=zt proves Σ_t c(t)c(zt)=Σ_u c(z^{-1}u)c(u), so S(z)=S(z^{-1}). No unproved analytic bridges remain in this ordinary derivation. The bounded exact tests in exact-check.json check the displayed correlation and original sums; they are validation, not the proof.

Bounded prior investigation: live search queries recorded in search-notes.md and search-results.json did not identify a directly relevant successor proof. This is NOT novelty clearance. Classical cyclic correlation and Bernoulli-polynomial sum reciprocity make the deduction routine; retain for independent review with zero discovery credit, not as a proposed new theorem. Current proof registries were not cleared, so no promotion is requested. Expected certificate: a few polynomial finite-sum identities, modular permutation, and about 100–250 lines if pursued; formal dependencies are finite sums, rational polynomial arithmetic and modular equivalence. No Lean or manuscript investment made. Full-scope ordinary proof retained, proposals.json remains empty.

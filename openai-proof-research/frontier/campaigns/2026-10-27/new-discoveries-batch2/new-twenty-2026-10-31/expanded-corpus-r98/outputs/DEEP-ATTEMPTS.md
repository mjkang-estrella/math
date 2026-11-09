# Sustained routes and limits

## Modular symmetry, 358056

The source condition is ordered in x,y; both (x,y) and (y,x) must be tested. scripts/sumdiff.py encodes each such clause as `not sx or not sy or s(x+y) or s(x-y)` and odd cardinality using a Tseitin XOR chain. An independent asymmetry disjunction uses XORs of each nontrivial negation pair. Both failure modes were queried separately; no unrestricted symmetry assumption is built into the SAT instance. A solution at e=1,2 can be checked directly. Every queried UNSAT is only a solver result, not a formal proof. The original source states “small e” without a numerical bound; thus even e=240 cannot honestly be labeled beyond the *specified* authors' range. The source GitHub README guess gave404, not a denial; no access escalation or further access chase followed.

A possible proof route: if zero is absent, each x in S forces 2x in S. Classifying finite doubling-invariant sets subject also to ordered two-element constraints might force even cardinality. If zero is present, the remaining difficulty is to force negation symmetry from odd cardinality. Neither implication follows solely from doubling closure. No proof found.

## Chain polynomials, 360530

The current HTML paper no longer presents the same recursion. The exact historical definition is recovered in 2310.18798v1, Lemma4.8. A type is (nu,mu), with length r=nu+|mu|, degree d=r-length(mu), rank nu. scripts/chains.py implements all three cases with Fraction coefficients, checking integrality and the exact degree at every stage. The zeta coefficient is computed from a canonical representative of omega-prime by enumerating its s-edge subsets and counting those of type omega, exactly as in the original definition. Canonical representatives are monotone partial maps formed from disjoint contiguous forward chains and loops. It does not identify polynomials merely on matching small samples.

Length21 completed (3506 types at that length) without negative coefficients. The run requesting26 was killed by CPU limit during22; its complete stdout is retained. Case(ii) is positivity-preserving because the degree bound makes all four monomial-shift coefficients nonnegative. Thus only reduced types need new analysis; rerunning larger isolated-point families adds little mathematical information.

The latest paper Lemma5.18 and §7 contain aggregated generating functions and explicit positive formulas for their base polynomials. A possible bridge, not yet proved with all normalizations: with l proper chains, m isolated points, t extra chain edges, nu loops, and c=l+m, original and new coordinates satisfy `v_old=V_new-1`, `W=U*V*Q`; hence candidate substitution `P_old(z,w)=(1+w)^c p_new((z-w)/(1+w),w/(1+w))/normalization`. The negative term z-w means new positivity alone is insufficient; cancellations and the exact normalization must be checked. Since all these formulas are in the source, any short resulting positivity proof must be assessed for routine source consequence before formalization.

## Inclusion matrices, 360364

The original appendix is retained in the2025 published PDF. The source's interior-block recursion and boundary bijections are not enough by themselves: the final paragraph explicitly leaves the boundary block elimination unverified. Exact determinants through n13 and modular ranks through n16 found no counterexample. Modular full rank does not prove integral unimodularity; only the exact Bareiss runs have abs(det)=1 certificates as numerical diagnostics. There is no source-stated exact computational maximum, so no beyond-range claim is made here.

## Promotion, 354562

Random generation was visibly biased toward top-heavy labelings at large a, so the random sweep alone was not used as decisive evidence. A second implementation enumerates every monotone height function on the2x2x2 cube with heights0..7, equivalently every0..2 monotone labeling on[7]x[2]x[2]. It exhausts all75966 states and processes every distinct rowmotion orbit. Toggle bounds use actual lower/upper covers and outer bounds0,2. The statistic checked is the source's equivalent antipodal rowmotion sum, not a claimed standalone Lean proof of translated promotion. All5654 orbits pass, longest230. A next useful step would be an orbitwise coboundary, not another random sample.

## Ruzsa, 359254

The SAT model uses binary membership, exact AND variables for unordered pairs, multiplicity2 for distinct ordered summands and multiplicity1 for diagonal summands. A one-way sequential at-least counter bounds each residue's total representation count; coverage clauses force a representation. A feasible assignment is checked independently by literal ordered-pair enumeration. Fixing0 in A is sound up to translation: translating A shifts all sums by2t and preserves full coverage and maximum counts.

The surprising R37<=4 witness was investigated rather than combined blindly with the old quoted Rm>=6 theorem. A primary 2026 successor gives this exact refutation of the target and explains the old data discrepancy. No new credit and no misleading lower-bound proof from SAT timeouts.

# Material coverage gaps

This packet is a bounded investigation, not the several-hour complete pass requested in TASK.txt. No q7 ovoid incidence search, no full flag-lattice search beyond rank8, no non-coprime generalized Markov grid, no source-beyond-range all-genus test, and no eventual Paley theta calculation was completed. These omissions are explicit in the20 results. No formal endpoint survived and no Lean packet was manufactured. Source-backed analytical dispositions are not solutions. The work should not be integrated as20 technically exhausted targets or as a completed campaign requirement.

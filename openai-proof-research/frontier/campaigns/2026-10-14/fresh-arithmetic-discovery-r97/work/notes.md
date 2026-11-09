# r97 working notes (durable scratch; not a frozen statement)

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Reading order so far
1. AGENTS.md; research-brief-2026-10-20.txt; fresh-arithmetic-r97-brief.txt (full).
2. r96 REPORT.md, packet/public/{report,route-028,screens,reading-limits}.md, discovery-arithmetic-r96-parent/intake.json (full; route-028 via cat with harness truncation of long lines).
3. sources/upstream.json; NEW-TEN acceptance section (lines 1-80); catalogue titles; r95 family-history table (navigation only).
4. History hits followed (navigation): i83 Catalan finite measure (first 120 lines); r80 REPORT (196/odd zero divisors, Ivanov 2610.17662); t197o-hyperstar research head; astra-r4 T197O proof head (TECHNICAL); arithmetic-r1 paired Jacobsthal candidate head (via r94 history copy); proposals/number_theory.md 021 line; r89 other-screens (209 Gersten, 200); r83 research (201 Kurosh, 208); r90 history copy of screen-199; r61 checkpoint (031 Uchida co-Hopfian classical).
5. Family 009 history: r24 payload/screen-009.md (full: Hom reconstruction screen, valuation-type example psi_h, collapsed-plane + exponent-p valuation-descent gap); r73 reading-and-credit lines 15-30 (009 broad functoriality rejected).
6. Pinned source 009 mod-p companion: all five sections read in full (01-05? -> 01,02,03,04 read in full so far; 05 pending).

## Direction under consideration: 009 mod-p, compatible homomorphisms
Data: V_F = F^x/F^xp, R_F = span{[f]x[1-f]}. theta: V_K -> V_L linear with (theta x theta)(R_K) in R_L.
Model maps (r24 example generalised): valuation v on K, residue field kappa, field hom beta: kappa -> L,
any F_p-linear extension of beta_* to G_v/p where G_v = K^x/(1+m_v). All compatible (checked: v(f)>0, <0, =0 cases;
uses {w,-w}=0 and [-1]=0).
Pure value-group maps chi o v are compatible and can be nondegenerate (rank-2 valuation with residue field k).
Sums of two independent valuation maps are NOT compatible unless degenerate (approximation theorem).

Key reformulation: blocks V_{D(s)} (D=L^p) partition V_L\0; compatibility <=> theta(x), theta(1-x) same block or one is 0
(source lem:zero-symbol + Bloch-Gabber-Kato-free direction). theta(V_{C(f)}) lies in one block (isotropic subgroup).
For p=2, blocks are exactly projective lines through [1]; so theta is automatically a lineation P_C(K)->P_D(L)
(lines to lines or points). For p odd, line recovery with collapse is the unpaid step (source prop:intersection needs
nonmonomial images; collapses happen e.g. v(x) not in p Gamma).
Lineation theory: Carter-Vogt Mem. AMS 235 (1980); Rado Aequationes Math 1970; Brezuleanu-Radulescu J. Geom 1984.

Alternative examined: mod p^n reconstruction (Izhboldin p-torsion-freeness reduces to an infinitesimal rigidity lemma
for delta with {delta a,b}={delta b,a} whenever {a,b}=0). Likely TECHNICAL; not pursued yet.

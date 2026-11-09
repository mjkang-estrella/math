# Finite counterexample to Hegarty–Martinsson–Wedin Conjecture 4.2

Root revised copy: complete ordinary computer-assisted argument, independent preliminary mathematical review PASS; eligibility/novelty HOLD. One source family only. Independent preliminary review is recorded in sol-honest-tournament-preliminary-review-r1; this is not a novelty-cleared or accepted result. The explicit rational table is part of the construction, not numerical evidence replacing a proof.

## Literal target and separating inequality

Primary body: https://arxiv.org/pdf/1803.00823v1, Hegarty, Martinsson and Wedin, submitted 2 March 2018, Section 4: Rules 1–3 and Eq. (4.7) on printed p.12, Conjecture 4.2 on printed p.14. For every n in N, the conjecture identifies the attainable symmetric honest tournament win-vector region with A*_n, the convex hull defined by Rules 1–3 and equation (4.7). Whether a bar is attached to the attainable region is immaterial here: a strict separating inequality refutes both the actual and closure formulations. Section 2 requires a bounded number of sequential matches; the construction below has exactly 192. No extra identity-dependent information or access to unknown strengths is used.

Every vector x in A*_4 satisfies x1+x2 >= 1/2: vertices 1 and 2 each send two arcs, all four land in {1,2}, and v_i=indeg(i)/8. Convex combinations preserve the inequality. No hull software is needed for this inequality.

## Exact rational table and global map

Use edge order (12,13,14,23,24,34). The 729 rows in witness-table.csv enumerate all s in {0,1,2}^6 exactly once. Its four integers w_i(s), divided by 48, define V_i(s). verify_finite.py exhaustively checks, using integer arithmetic, the following finite assertions:

1. Every w_i is nonnegative and their sum is 48.
2. Under every permutation p of four players, V_{p(i)}(p.s)=V_i(s), with reversed edges complemented s->2-s.
3. If coordinate ij increases by 1, V_i does not decrease and V_j does not increase.

The verifier uses the CSV directly; it does not import the LP, floating point, symmetry quotient or discovery witness JSON. Every assertion is a bounded integer comparison; all 729 states and all 17,496 state/permutation combinations are checked. The table is an explicit finite definition. Replacing this certificate with a short structural winner rule would improve exposition but is not an unproved mathematical bridge.

For q in [0,1], define h0(q)=max(1-2q,0), h2(q)=max(2q-1,0), h1(q)=1-h0(q)-h2(q). Define, on the whole six-dimensional cube,

f_i(P)=sum_s V_i(s) product_{ij} h_{s_ij}(p_ij).

The h's are nonnegative and sum to 1, so f is a continuous probability-valued map. The permutation identities h0(1-q)=h2(q), h1(1-q)=h1(q) and the table symmetry prove global symmetry. Holding other coordinates fixed, the slope of f_i as p_ij increases on either half interval is twice a nonnegative convex combination of the corresponding table differences. Thus f_i is nondecreasing in its own win probability. Likewise f_j is nonincreasing. This proves honesty on the entire cube, including boundaries, rather than only on sampled doubly-monotonic matrices. This is also the explicit construction underlying source Proposition 6.8, whose proof was read before the attack.

## Actual finite tournament; no limiting theorem needed

Each unordered pair plays exactly N=32 times, in any fixed sequential schedule. Write Q_ij for the observed fraction won by i. Only after all 192 matches, draw fresh independent election randomness and elect a single winner according to the distribution f(Q). No election seed is drawn or included in any earlier tournament state. At empirical Q, every hat has denominator dividing 16, so every f_i(Q) has denominator dividing D=48*16^6. A single post-match uniform draw from {0,...,D-1} and the cumulative categorical intervals implements this election with finite randomness. This requires only rational sampling and match results. Relabeling players relabels the independent match-count distribution and f, so the source's winning-probability definition of symmetry holds. Even conditioning on the outcomes of every other match, changing a loss to a win raises one's own Q_ij and hence cannot lower one's probability of selection. Averaging proves honesty at each history, for every underlying P in M_4. There are precisely 6*32=192 matches.

Specialize to P with rows

    (1/2,1/2,1,1)
    (1/2,1/2,1/2,1/2)
    (0,1/2,1/2,1/2)
    (0,1/2,1/2,1/2).

Entries increase along rows and decrease down columns, so this is literally in D_4. Edges 13 and 14 are deterministic wins. Counts on the other four edges are independent Binomial(32,1/2).

For a fair count K, set t=E h0(K/32). Symmetry gives E h2=t and E h1=1-2t. Finite summation yields t=300540195/4294967296 (the verifier also checks t=binom(32,16)/2^33). Independence and the displayed multilinear formula collapse the expected top-two winning probability to only 81 terms. Expansion of those exact table entries gives

S(t)=1/4+(15/4)t-(17/2)t^2+(185/24)t^3-(11/4)t^4.

verify_finite.py independently derives all five coefficients directly from the CSV using the binomial theorem; it does not trust the LP or a stored polynomial. At the displayed t, S(t) is

    644305742079015272838458033019501771781 /
    1361129467683753853853498429727072845824

which is strictly less than 1/2. The positive gap is

    36258991762861654088291181844034651131 /
    1361129467683753853853498429727072845824.

Consequently this actual symmetric honest four-player tournament has a doubly-monotonic specialization outside A*_4. It refutes the universally quantified Conjecture 4.2, without claiming a characterization of the attainable region.

## Objections and limits

The finite table is large and was found by linear optimization. Its rational properties have separate exhaustive standard-library checks, not an external independent review or formal certificate. The source itself supplies the general finite-discretization technique (Propositions 6.6–6.8); only finding an actual separating table and finite tournament could be credited, never interpolation or LP formalization. The frugal theorem (Section 5) does not apply: no uniformly selected player is omitted from play. This construction uses all six pairs. No current registry head was obtained, no worldwide priority is claimed, and a classical/source-method routine-adaptation objection remains for root adjudication. No Lean or manuscript was written.

# H014 conditional coset backends: actual recurrences, missing full gain

2026-10-08. Native Astra independent followup, root algebra/cost check. No
experiments, predictor, whole-solver gain or new Lean claim. Let H=kerchi of
order h and suppose the correct scalar coset k0*H has already been recovered,
at the separately charged MCL cost. Q'=k0^-1 Q=uG for unknown u in H.

## Short-generator babies

Find and certify a small integer s of exact order h modulo q, with an explicit
addition chain costing c_s for multiplication by s. Babies P_0=G,
P_(a+1)=sP_a,0<=a<B, cost B*c_s rather than B full-length scalar evaluations.
Giants R_b=s^(-bB)Q' still use paid fixed-base evaluation of cost v_Q each.
A point match yields u=s^(a+bB) and k=k0*u; verify. Principal work

    B*c_s + ceil(h/B)*v_Q, optimized about2*sqrt(h*c_s*v_Q).

Memory includes B point/index records and the fixed-base table. Pay multiplier
search, factorization/order certification, chains, scalar bookkeeping, lookup,
setup and verification. Knowing the integer s^(-B) modulo q does not give a
short action chain for it. This improves only one emission side conditionally.
For a baseline kappa*sqrt(q), this principal term alone requires approximately
c_s*v_Q<kappa^2*m/4 (h~q/m), with applicable quotient constants handled separately.
Predictor/calibration/failed attempts still must fit the full-work gate.

A bounded search2<=s<=L can test exact order using certified prime divisors of h
and choose a frozen cheapest-chain rule. No ordinary-curve hypothesis guarantees
a suitable short generator. s=t^m ensures membership but not generation; the
literal m applications of[t] may consume the saving. This is a construction cost,
not a lower bound for every chain of that residue. No search run is justified yet.

## Two multiplicative herds

Choose certified s_1,...,s_r in H with actual short chains and a fixed selector
j(R). Records(R,a,herd) satisfy R=aG or R=aQ', a in H. Update

    R <- s_j(R)*R;  a <- s_j(R)*a modq.

A cross-herd match aG=bQ' gives u=a/b and verified k=k0*a/b. Same-herd matches
do not recover u: count their work, restart at paid random seeds, and retain a
table of all visited states. No constant-memory or free distinguished-point
claim. To ensure the chosen multipliers generate all H, for each prime ell|h
at least one s_j must satisfy s_j^(h/ell)!=1. Otherwise walks can stay in
disconnected multiplicative components with target-dependent missed meetings.

Even generation does not prove rapid useful cross-herd collisions. Small
commuting multipliers impose structure on reachable products. Random-map mixing,
fruitless-cycle and success assumptions must be tested or proved for a frozen
configuration; they are not automatic consequences of the invariant. This is an
executable conditional walk idea, not an established coset-rho speedup.

Both cards are known group-action/search refinements, not discoveries. A primary
prior-art lead is [Cheon's auxiliary-input work](https://www.math.snu.ac.kr/~jhcheon/publications/2010/StrongDH_JoC_Final2.pdf);
its auxiliary inputs are NOT supplied by MCL or ordinary ECDLP. No result from
that paper is assumed here. Additive progressions need paid rejection to remain
in a multiplicative coset. Cheap existing automorphisms are already credited to
the baseline through their actual kernel intersection. No cheap predictor or
favorable full-cost configuration survives yet, so no backend engine is built.

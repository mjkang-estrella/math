# Karp331384 continuation: no full result, credit0

28 October 2026. This continues root-beta-convolution-r9 without changing it.
The exact source is Karp1509.05120v1 Conjecture2. Its negative0<b<1 half and
stated integer-shift cases are already proved in that same source. The full
b>2 arbitrary-shift range remains unresolved here. No novelty, formal,
manuscript, review, packet or acceptance claim is made for this lane.

For h_b(t)=Gamma(t+b)/(Gamma(t+1)Gamma(b)), define

    ψ_k=Σ_(i=0)^k[h_b(a+α+i)h_b(a+β+k−i)
                 −h_b(a+i)h_b(a+α+β+k−i)].

All a,α,β>0 and k≥0 integer are as in the source. There is no extra k!.

## Exact b=3 identity

Since h_3(t)=(t+1)(t+2)/2, expansion and the standard finite sums of powers
give, for every k≥0,

    ψ_k = αβ(k+1)/4 · [2a²+2a(α+β+k+3)+αβ
                         +(α+β)(k+3)+2k+5] > 0.

Every bracket term is nonnegative and its constant is positive. The exact
symbolic identity is reproduced by check_structure.py. This is an uncounted
parameter instance, not a full answer or a claim of literature novelty.

## A concrete failure of the tempting generic route

Replacing the earlier h''≤0 assumption by log-concavity is insufficient,
even if h is positive and strictly increasing. Take h(t)=t² on t>0,
a=1/100, α=β=1/10 and k=1. The literal same finite-convolution difference is

    ψ_1 = −3829/250000 < 0.

Thus the continuous log-concavity of the summand, symmetry of the convolution,
and monotonicity of the adjacent ratio do not by themselves establish the
source conjecture. A discrete sum of translates of a symmetric log-concave
function need not remain unimodal under continuous translation. This example
is a counterexample to that proposed sufficient lemma, **not to Karp**.
Additional structure is needed; the Gamma ratio's exact unit-shift identity
is one candidate, stronger than monotonicity of that ratio alone.

## Numerical diagnostics only

screen.py tests1600 seeded cases at85 decimal digits, under a512MiB cap.
The range includes b from just above2 to approximately1000, a down to1e−7,
highly unequal real shifts up to1e5, and k≤100. No negative coefficient was
found. The smallest relative gap is about1.37e−36, showing why ordinary
machine precision would be unsafe. The saved rounded35-digit parameters were
rechecked at170 digits by direct Gamma products, rather than scaled logGamma;
the gap remains positive. Those reconstructed parameters are explicitly
distinguished from the original unrounded random numbers.

Neither this finite scan nor the b=3 identity proves the missing full range.
No new Lean investment is warranted until an all-b argument is obtained.
The exact source was re-identified in a bounded web search; no new public
resolution was located, but citation bodies were not exhaustively re-screened.
Journal full-body comparison remains unperformed. Accepted tally stays
2/30 additional and32/60 total. No external changes or problem-status updates.

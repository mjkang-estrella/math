# H041 primary bridges: corrected decomposition cost gate

2026-10-08 local / 2026-10-09 UTC. No new algorithm supplied; no experiment
admitted. Raw Claude Opus5.5 report: H041-primary-opus-raw.md. Native Sol
independent scope review completed and confirmed the corrected gate. Root checked the source and
the following accounting; this is paper analysis, not a Lean theorem.

## Primary read and accounting

Root successfully read the [PKM2016 paper, sections3.1–3.5](https://people.maths.ox.ac.uk/petit/files/16PKC_primeECDLP.pdf)
after the other author-host URL failed. The report had read only the [authors'
slides](https://troll.iis.sinica.edu.tw/pkc16/slides/6-1--Algebraic_approaches_for_the_Elliptic_Curve_Discrete_Logarithm_Problem_over_Prime_Fields.pdf).
The paper's partial model charges field operations and scalar multiplications
as units and displays

    P(p,m) + m! p / B^(m-1) * T(E,m,L) + B^omega,

where B=deg L and 2<omega<=3. For B^m approximately m!p, it explicitly identifies
the relation-solving threshold p^(1/2-1/m). Its useful decomposition probability
is heuristic; construction of the auxiliary curve is separate, with fixed-field
and chosen-field scenarios distinguished. Its 2016 discussion leaves dedicated
system solving and asymptotic complexity open. This is not a current impossibility
or novelty theorem.

Independent cost derivation: keep m fixed, prime subgroup order q comparable
to p, B=p^(1/m+o(1)), setup A, paid decomposition-attempt work D (including
sampling and valid witness handling), and linear-algebra cost L(B). D must bound
worst-case or conditional expected work per fresh attempt, including failures;
an unconditional average alone does not justify multiplying by a stopping time.
Factor-base lifts, signs and subgroup validity must also be checked. Suppose
the expected number of attempts needed for enough usable relations is at most
p^o(1) B/sigma. This includes a required useful-relation/rank/recovery condition;
it does not follow just from a mean number of polynomial roots. Then a
conditional upper cost invoice is

    A + p^o(1) B D / sigma + L(B) + final verification/recovery.

Write A=p^(a+o(1)), D=p^(d+o(1)), sigma=p^(-s+o(1)), and
L(B)=p^(ell/m+o(1)). Assuming the final costs do not dominate, the resulting
upper exponent is max(a, 1/m+d+s, ell/m). An exponent improvement is supported
by these bounds only if every term is strictly below1/2. Equality requires
constants and logarithmic factors; a failing upper bound is not a lower bound.

Thus for constant success overhead and a hypothetically applicable B^2 sparse
linear-algebra bound, m>4 and d<1/2-1/m are sufficient exponent gates when
setup and recovery fit. At m=5, the decomposition exponent threshold is3/10,
not1/5. For example d=1/4 would give relation exponent9/20 and linear exponent
2/5 in this conditional model. This illustrative exponent arithmetic asserts
no such solver exists. D<=p^(1/m) merely balances relation work with B^2;
it is not necessary for beating square-root work. Under the paper's displayed
B^omega model, the linear-algebra condition instead reads m>2omega.

No polynomial, sparse-solver or rank bound is supplied by these inequalities.
If m grows, factorials, relation density, equation degree/size and solver
constants cannot be hidden as fixed constants. All costs must ultimately use
matched field/bit/memory semantics, with curve construction and failed attempts
charged. No runtime or asymptotic conclusion follows from tiny instances alone.

## Other scope qualifications

- The recent2026 papers were search-result leads in the raw report. They were
  not opened by the proposer; no exhaustive current-literature exclusion or
  claim that every recent result is quantum is accepted here.
- The2024 critique and2015 survey were abstract-only reads. Neither supplies a
  proof rejecting coordinate-aware algorithms in this checkpoint.
- A signed x-coordinate membership test is invalid as an *oriented* interval
  oracle. An algorithm deliberately recovering both signs may still be correct;
  it needs a paid witness/recovery rule. H040's counterexample has that scope.
- Differential x-only states and other controllers are not excluded by a
  failure to reconstruct a y-coordinate for an arbitrary point-only transition.
  State, label recovery and useful-collision law must be specified and priced.
- The coprime homomorphism obstruction applies to the named homomorphic-filter
  construction; it is not a necessity theorem for all representation methods.
- H040's missing multiplication-map input blocks the named derivative bridge,
not every isogeny-based method: evaluating a supplied public isogeny on Q does
not require k or a representation of [k]. The genus4 fiber-product calculation also
  requires its precise branch and independence hypotheses.

## Result and next decisive step

Verified improvement remains NONE; accepted reference exponent remains1/2.
The raw report supplies no new public operation. A dedicated decomposition
solver could be reconsidered against the corrected total invoice, including
success, rank, witness extraction and setup. This corrects an overly restrictive
screen; it does not admit another generic infrastructure or experiment wave.

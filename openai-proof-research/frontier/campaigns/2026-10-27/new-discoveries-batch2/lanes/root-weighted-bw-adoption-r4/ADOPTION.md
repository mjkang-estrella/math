# Weighted BW case(i) handback — root assessment, 28 October 2026

Root read the completed pi-weighted-bw-case-i-r4 report and completed thread.
No full source theorem or counterexample, no Lean endpoint, and no credit.
Accepted2/30 additional,total32/60 unchanged. Preserve only checked elementary
reductions and failed-route information; do not adopt the advertised SOS and
n2 identity as proven. No additional formalization or independent review is
warranted for these incomplete/invalid supporting claims.

## Valid reductions and a corrected exact full-exterior norm

T(X,Y)=XWY-YWX is alternating and unchanged by adding multiples of Y or
W^-1 to X. Orthogonalizing against Y shows equivalence with the decomposable
wedge inequality ||Lambda(X wedge Y)||^2<=c^2||X wedge Y||^2,
c^2=w1^2+w2^2. The coordinate chain contraction formula is literal.

The norm on the FULL exterior square has the simple exact value
||Lambda||^2=S=sum_i w_i^2 for n>=2, not (sum_i w_i)^2 as discovery D2 says.
Indeed different offdiagonal output coordinates have disjoint supports in
the standard unit wedge basis and squared row norms S. The diagonal-output
Gram matrix is S I-w w^T; its cross-Gram entries with offdiagonal outputs
are zero. Therefore Lambda Lambda*=S I-v v*, with v=diag(w) as a vector
and ||v||^2=S. Its eigenvalues are S (multiplicity n^2-1),0. This proves
the full-exterior route fails when n>=3 and all weights positive. Root exact
matrix construction checks this at w=(2,1),(9,4,1),(9,4,2,1). This is an
uncounted supporting calculation, not the needed decomposable bound.

The per-entry Lagrange identity is correct. However, summing chain energies
double-counts two-cycle wedge coordinates such as E12 wedge E21 (they enter
both diagonal outputs). Thus a global chain/nonchain budget is not obtained
by simply treating those energies as a disjoint partition of wedge norm.
The claimed remaining coefficient-absorption argument needs this accounting
repair as well as the unresolved Pluecker estimates.

## Concrete failures of reported identities

1. SUMMARY R2/discovery D4, equality on ALL n2 pairs, is FALSE. W=I2,
X=I2,Y=E12 gives T=0 but c^2||X wedge Y||^2=4. Centering along the central
W^-1 direction can reduce norms; its shear invariance does not preserve the
unprojected wedge norm. The source's centered statement is not strengthened
by this handback.
2. R3/D5 SOS is FALSE as written. W=diag(2,1),X=E12,Y=E21,c^2=5 has true
sharpened deficit0, whereas the displayed SOS gives4. For p!=q, the operator
norm statement ||T_(E_pq)||^2=wp^2+wq^2 itself is valid, but needs a different
proof: outputs comprise (wp^2+wq^2)|Yqp|^2, the diagonal-input form
|wq Yqq-wp Ypp|^2, and the remaining independent row/column squares. The
latter coefficients are wp^2 or wq^2; hence the norm bound, attained at Y=Eqp.
The report's proposed mixed equality direction is not justified.
3. R4/D6 first sparse-family identity has an extraneous +w1^2. With a=b=0
its true deficit is0. For X=E12+aE13,Y=E21+bE31, the correct deficit is
|w2*a-w3*conj(b)|^2+(w2^2-w3^2)(|b|^2+|a*b|^2), with NO constant term.
Root checked its real symbolic specialization exactly; the complex expansion
follows by matching |a|^2,|b|^2,|ab|^2 and Re(ab). Other unverified SOS displays
are not adopted.
4. Eq15 is case(ii), already public; Eq16 is the source's consequence of
case(i). Correct the final handback's conflation. Full Fang–Cheng body still
unread; no novelty pass is inferred from the record or numeric searches.

independent_check.py/independent-checks.json retain exact counterexamples
and checks. Numeric sweeps, source metadata and a positive Gram spectrum on
sampled X do not prove the conjecture. No new-to-literature claim is adopted.

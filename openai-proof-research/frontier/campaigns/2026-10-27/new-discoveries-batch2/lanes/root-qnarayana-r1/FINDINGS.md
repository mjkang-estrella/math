# Endpoint q-Narayana research: no nominated outcome

Actual primary2610.28691v1 Section12.2-12.4 read. Conjecture12.7 concerns
coefficientwise TN of all four matrices A_nk=[n+1 choose k]_q[n choose k]_q/
[k+1]_q, B_nk=[n choose k]_q², and their squares indexed n+k,k. Source proves
order<=2 and fixed-q numerical TN all orders; neither establishes coefficient
signs of higher minors. It exact-checks leading7x7 minors of orders2,3,4.

Root search_minors.py uses exact Kronecker substitution with an explicit
factorial-times-coefficient-sum bound, balanced digits, integer Bareiss and
1GiB memory ceiling. Both printed3x3 anchor polynomials match. Maxindex16,
1200 proposed samples yielded841 admissible nonzero minors of orders3-6;
every decoded coefficient was nonnegative. Diagnostic only, no proof, no
discovery or formal claim. The all-order network/Schur argument is absent.
Early exact registry/source/id and web screens found no result; no novelty
clearance. Do not scale enumeration without a concrete mathematical plan.

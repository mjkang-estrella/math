# Preliminary C*-Corona obstruction — credit 0

## Source and scope

Krishna, *C*-Algebraic Bieberbach, Robertson, Lebedev-Milin, Zalcman,
Krzyz and Corona Conjectures*, DOI 10.20944/preprints202208.0140.v1,
Definition 2.6 and Conjecture 3.2, printed pp. 15–16. The author's actual
Zenodo 6917925 PDF is retained in `sources/`; its SHA-256 is
2d537f045e13a2c3b04fca8dd950b2e4144b78670e67f99c1ea2df2ef57afd59.
The parent rendered and read both pages. No published revision or matching
MathDB record has yet been established in this lane.

The definition requires, at every center a, an expansion with coefficients
on the LEFT: f(z)=sum b_n (z-a)^n, converging in norm in a norm ball.
Conjecture 3.2 quantifies over every unital C*-algebra, with no commutativity
assumption. For bounded functions f_j on its norm-open unit ball, the two
uniform C*-order lower bounds are assumed; bounded functions g_j,h_j of
that same analytic class are asserted with sum f_j g_j=1=sum h_j f_j.

This proposal refutes the n=1 assertion in M_2(C). It makes no assertion
about the commutative case, ordinary Frechet-holomorphic corona theorems,
or corona quotient algebras. It is a different source question and witness
from the connected C([0,1],C) Bieberbach candidate. No discovery credit or
formal certification is currently claimed.

## Witness and all hypotheses

Use the operator norm on A=M_2(C), set c=diag(1/4,0), and f(z)=I+c z.
For every center a, f(z)=f(a)+c(z-a); hence Definition 2.6 is satisfied
by a finite series, at every point of the norm-open unit ball.
Also ||f(z)|| <= 1+||c|| ||z|| < 5/4, so f is bounded.

Write T=c z. For ||z||<1, ||T||<1/4. For every vector v,
||(I+T)v|| >= (1-||T||)||v|| > 3||v||/4, and the same bound holds
for (I+T)* because ||T*||=||T||. Consequently f(z)*f(z)>=I/2 and
f(z)f(z)*>=I/2 in the literal positive-semidefinite order, uniformly.
Alternatively, T+T* >= -2||T|| I >= -I/2, and T*T, TT* are
positive. Expanding both products gives these same lower bounds directly.
Thus delta=1/2 works. The Neumann series also shows every f(z) invertible
with ||f(z)^(-1)|| <= 4/3. The failure below concerns the specified local
power-series class, not invertibility or boundedness of the reciprocal.

## No local source-analytic right inverse

Suppose a function g on the unit ball satisfies f(z)g(z)=I and has the
required expansion at 0 on some radius r>0. Let its coefficients be b_n.
At zero b_0=I. Set

    N = [[1,1],[-1,-1]].

Then N^2=0, ||N||=2, whereas

    cN = [[1/4,1/4],[0,0]],
    (cN)^2 = [[1/16,1/16],[0,0]] != 0.

Choose a real t with 0<t<min(r/2,1/2). Both +/-tN lie in the expansion
ball and the unit ball. Since (tN)^n=0 for n>=2, the convergent expansion
literally gives g(+/-tN)=I+/-t b_1 N. The two right-inverse identities are

    t(cN+b_1N)+t^2 cN b_1N=0,
   -t(cN+b_1N)+t^2 cN b_1N=0.

Subtract and divide by 2t to get b_1N=-cN. Add and divide by 2t^2 to get
cN b_1N=0. Together these imply (cN)^2=0, contradicting its (1,1) entry
1/16. Thus not even a locally source-analytic right inverse exists. The
asserted pair of left/right solutions in Conjecture 3.2 therefore cannot
exist. This argument uses exact nilpotence, no interchange of derivatives
or infinite sums, and no assumption about uniqueness of power coefficients.

## Eligibility and prior-art risks — unresolved

This is a complete mathematical obstruction, but acceptance is NOT proposed.
The mechanism is the failure of the source's local left-power-series class
to be closed under reciprocals in noncommutative algebras. That limitation
is closely related to classical A-differentiability and may make this an
uncountable formulation correction or immediate old corollary under the
campaign's strict standard. An independent substantive decision is required
before any heavy Lean/manuscript investment. Shortness alone does not settle
that decision, nor does an open source label establish new content.

Primary predecessors fetched: Cook arXiv:1708.04135 and Cook–Freese
arXiv:1708.04136. Cook's Theorem 5.10 and surrounding discussion explicitly
warn that products of A-differentiable maps need not be A-differentiable in
noncommutative algebras. His historical discussion points to Rosenfeld's
rigidity results for simple algebras. These have NOT been cleared as
subsummers. The 2025 article *A-Differentiability over Associative Algebras*
(Mathematics 13,1619) was found, but its body fetch was blocked (403/429);
search excerpts are not a theorem-body review. No global novelty claim.

Initial targeted web searches found the source and no explicit refutation.
The retained trureturing Problems/Library checkout contains no matching
Corona problem (the Krishna hit is the distinct HIGHERMEAN entry); this is
bounded local registry evidence only. No external posting or communication.

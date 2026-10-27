# A variance proof of Davis's rational-function bound

Status: prospective resolution of MathDB319187 / Davis2009 Conjecture3.1.
Discovery credit **0**. Full mathematical argument and exact finite certificates
are below. The complete literal universal endpoint is proved in Lean: fresh isolated strict
replay PASS,100 declarations/19 modules, all types/axioms read and module logs
empty. A three-page manuscript exists. Independent final review and extracted
packet replay are still required. No assertion of worldwide priority.

## Exact target and source

Donald M. Davis, *Maximizing a combinatorial expression arising from crowd
estimation*, arXiv:0910.5725v1, p5 and p12. The current author-hosted copy
<https://www.lehigh.edu/~dmd1/fredpaper.pdf> has the same conjecture, visually read
on p12. The author's publication list identifies International Journal of Modern
Mathematics5 (2010),129–148. The author-hosted PDF is a preprint, **not** an
independently retrieved typeset journal body.

Write f_i(x)=x(x−1)…(x−i+1), f_0=1, and

    P_d(x) = Σ_{i=0}^d f_i(x)^2 f_{d−i}(x)^2 / (i!(d−i)!).
    q_d(x) = 2x²/(d+1) − 2dx/(d+1) + d/2.
    R_d(x) = P_{d+1}(x) − q_d(x)P_d(x).

Lemma1.6 identifies q_d as the polynomial quotient. Conjecture3.1 asks, for
every integer d≥5 and every real x≥(d+√(d+2))/2, that

    −R_d(x)/P_d(x) ≥ (199/200)(d−2)/(2x+d−2).

The proof below actually gives strict inequality. The source's more ambitious
Conjecture3.9 about critical points and asymptotic series is not claimed.

## 1. A positive distribution and two exact identities

Set w_i=f_i(x)^2 f_{d−i}(x)^2/(i!(d−i)!), Z=Σw_i=P_d(x).
All weights are nonnegative. Since x>d/2, the central term i=⌊d/2⌋ is positive:
both falling factorials only contain factors x−j with j<d/2. Thus Z>0.
Let expectations use probabilities w_i/Z, and put

    D=d/2, a=x−d/2, u=i−D, V=E[u²], M=E[u⁴].

Symmetry w_i=w_{d−i} gives E[i]=d/2. The identities below involve only
polynomial products and sums. In particular they remain valid when some weights
vanish at integer x; no division by a falling factor occurs.

For degree d+1 weights w'_j,

    (i+1)w'_{i+1} = (x−i)²w_i.

Summing and using symmetry of w' gives

    P_{d+1}/P_d = 2/(d+1) E[(x−i)²]
                = 2/(d+1)(x²−dx+d²/4+V).

Consequently

    −R_d/P_d = (d−4V)/(2(d+1)).                         (1)

For the second identity, use rates

    λ_i=(d−i)(x−i)²,       μ_i=i(x−d+i)².

Direct cancellation of factorials, with no division by x−j, gives
λ_i w_i=μ_{i+1}w_{i+1} for 0≤i<d; λ_d=μ_0=0.
Therefore the weighted sum of

    λ_i[(u+1)²−u²]+μ_i[(u−1)²−u²]

vanishes by index shifting. Since

    λ−μ = −2u(2Da+a²+u²),
    λ+μ = 2(Da²+Du²+2au²),

expansion yields

    2M + B V = D a²,
    B=4Da−D+2a²−2a.                                    (2)

Finally M≥V², because E[(u²−V)²]≥0. Thus

    2V²+B V ≤ D a².                                    (3)

## 2. All d≥43: a single polynomial certificate

Our domain gives a≥√(d+2)/2>1 and 4a²≥d+2. Define

    T=d/4−199(d+1)(d−2)/(800(a+d−1)).

Using (1), the desired strict bound is exactly V<T. Both B and T are positive.
For T this follows from the useful simplified numerator

    T = (200da+d²−d+398)/(800(a+d−1)).

An exact calculation gives

    2T²+B T−D a² = N(d,a)/(320000(a+d−1)²),

where, with K=d²−d+398,

    N = 800 K (a+2d−2)(a²−(d+2)/4)
        + a L(d) + K(201d²+599d−402),
    L(d)=400(2d⁴−105d³+902d²−1197d+1194).

Every summand is nonnegative and the last two are positive for d≥43. Indeed,
putting t=d−43≥0 gives

    L(d)=800t⁴+95600t³+3818000t²+51998400t+42755200>0.

Hence 2T²+BT>Da². Since V≥0, T>0 and B>0, (3) forces V<T. This proves the
entire infinite range d≥43 without numerical approximation.

`formal/TailBound.lean` proves this scalar comparison. `Weights.lean`,
`Moments.lean` and `QuotientBridge.lean` prove the exact literal finite-sum
identities, normalized moments and remainder bridge. `SourceTail.lean` discharges
all scalar premises and proves the literal source inequality for every d≥43.

## 3. The finite range 5≤d≤42: 912 positive integers

Let S_d=d! P_d, an integer polynomial. Define the integer polynomial

    H_d = {200(2x+d−2)[2x²−2dx+d(d+1)/2]
           −199(d+1)(d−2)} S_d −200(2x+d−2) S_{d+1}.

It equals 200(d+1)d! times the cross-multiplied desired difference

    [(2x+d−2)q_d−(199/200)(d−2)]P_d −(2x+d−2)P_{d+1}.   (4)

For each of the 38 integers d=5,…,42, put

    m_d=1000d+⌊1000√(d+2)⌋,   r_d=m_d/2000,
    F_d(x)=f_{⌈d/2⌉}(x)²,    G_d(x)=H_d(x)/F_d(x).

The division is exact over the integers (F_d is monic), and r_d is at most the
source threshold. For N_d=deg G_d, **every coefficient** of the polynomial

    2000^{N_d} G_d(y+r_d)

is a strictly positive integer. All 912 integers are recorded in
`certificates.json`. This proves G_d(x)>0 for every x≥r_d; F_d(x)>0 on the
source domain, so H_d(x)>0. As P_d and 2x+d−2 are positive, (4) proves the strict
source bound.

`certificate.py` reproduces this entire finite certificate using only Python's
arbitrary-precision integers: falling products, binomial convolution, monic exact
division, integer Taylor shift, integer square root, and coefficient positivity.
An earlier, separately implemented SymPy rational-polynomial calculation with
even slightly weaker thresholds r_d confirmed positivity for the same 38 cases.
These two supplementary implementations are not the Lean certificate. The Lean
checker instead constructs the full integer polynomial 2H_d, and checks its
cleared-denominator translated coefficient list: positive constant and all other
coefficients nonnegative. All list-operation/evaluation identities and the
source-polynomial bridge are proved internally; all38 finite checks use
`decide +kernel`. No external certificate data is trusted.

## Scope, novelty limits, remaining work

The derivation is a proposed full mathematical resolution of Conjecture3.1,
not a new proof of the source's established half-unit bound. The substantive
step is the fourth-moment identity and its uniform quadratic comparison; the
finite range has exact certificates rather than point samples. Prior-art work
so far: exact live MathDB record has no posted solutions; arXiv has only v1;
author-hosted current body retains Conjecture3.1; author publication list checked;
OpenAlex identifies the exact work W1568649730 and returns zero indexed citers;
three targeted web queries found no resolution. These are bounded searches,
**not** a novelty certificate. No subscription-index search or actual final
journal-body comparison has yet been completed.

Completed formal endpoints: `Davis.source_strict_bound` (all d≥5 and every
real x in the exact source domain) and `Davis.source_conjecture_319187` (closed).
Fresh full100/19 receipt SHA:
f499f8723b77920a42950167832268ca47700702919d580cd3f10fdbceabc0d4.
Only propext/Classical.choice/Quot.sound occur; some integer-only declarations
use fewer. All100 types/axioms inspected, all19 module logs empty.

The author-hosted revised2010 journal-style manuscript fredijmm.pdf was also
retrieved and its p12 Conjecture3.1 visually checked: exact same statement.
Its blank volume/page header means it is not asserted to be the final paginated
publisher copy. No source-access limit is silently converted into a proof.

Still required: independent adversarial source/math/formal/novelty/manuscript
review; deterministic packet and fresh extracted strict replay. Tally stays18/30.

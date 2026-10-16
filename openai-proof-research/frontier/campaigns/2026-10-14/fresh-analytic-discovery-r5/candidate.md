# Analytic discovery r5: strict BV continuity remains unresolved

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Date: 2026-10-16. This is research, not a manuscript, independent review,
acceptance, campaign increment or publication.

**Disposition: NO SUBSTANTIAL COMPLETE THEOREM FOUND.** The full substantive
target B below is neither proved nor disproved. A complete Sobolev continuity
argument A is retained as a technical deduction, explicitly credited to the
actual affine-subtraction mechanism of González-Riquelme. It is not nominated
as a replacement for B. The exact flat-layer calculations below are supporting
research, not a new campaign theorem.

## 1. Original scopes and selection

`original-scope.md` fixes A before its detailed attempt. `scope-transition.md`
retains A unchanged, explains its technical classification, and fixes B before
its detailed attempt. The analytic lane's general brief, every supplied veto,
and the ownership/no-agents/no-publication constraints remain in force.

Write A_r g(x) = (pi r^2)^(-1) integral_{B(x,r)} g, and M f = sup_{r>0} A_r |f|.
All disks are Euclidean and centered at x. BV denotes integrable real functions
on R^2 with finite Euclidean vector derivative measure.

**Target B, unchanged full statement.** For every real f in BV(R^2) and every
sequence of real f_j in BV(R^2) satisfying

    ||f_j-f||_1 -> 0,     |Df_j|(R^2) -> |Df|(R^2),                 (B-in)

prove

    |D(M f_j)|(R^2) -> |D(M f)|(R^2).                            (B-out)

The local L1 convergence M f_j -> M f, proved below, gives the other part of the
strict-output interpretation. No common support, positivity, radiality,
regularity, absence of Cantor/jump part, or smoothness of approximants is
assumed. The output derivative measures need not converge in variation norm;
that stronger conclusion is not B and would fail for moving jumps. No claim
that B is an established named open problem is made.

**A, retained technical statement.** If f_j -> f in the inhomogeneous real
W^{1,1}(R^2) norm, then

    ||gradient M f_j - gradient M f||_{L1(R^2;R^2)} -> 0.         (A)

This is global vector convergence, not just convergence of gradient norms or
local convergence. The proof below covers zero input, signs, ties, contact
sets, unbounded supports and spatial tails. A is not asserted substantial.

## 2. Exact pinned premises

The user's stipulated upstream truth applies to openai/math at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The relevant manuscript is
*An Endpoint Gradient Bound for the Centered Disk Maximal Operator*,
September 26, 2026. Every path below is relative to

    preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/build/

The reproducible URL prefix is
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/ .

We use these actual, stronger-than-abstract interfaces:

* `sections/introduction.tex`, `thm:main`: W11 input has M f in W11_loc,
  with global gradient norm <= C ||gradient f||_1.
* The same file, `prop:finite-band`, and `sections/extension.tex`,
  `lem:sobolev-band`: for SIGNED real g, S_{a,b}g = sup_{a<=r<=b} A_r g
  has gradient norm <= C ||gradient g||_1 when b/a is a power of two,
  uniformly in a,b; it is Lipschitz with bound ||gradient g||_1/(pi a^2).
* `sections/extension.tex`, `eq:localized-input` through
  `eq:null-localization`: square cutoff, local mean subtraction, Poincare,
  small/large radius splitting and null-set localization. These are already
  source operations, not new lemmas claimed by this lane.
* The same file, `cor:bv-input`: for all real BV input, M f belongs to
  L2 cap BV_loc and |D(M f)|(R^2) <= C |Df|(R^2). The coarea consequence
  for indicators is also already present and is not re-proposed.
* `appendices/analytic-tools.tex`: translation, chain/product/max rules,
  planar Sobolev embedding, square Poincare and variation lower passage.

`source-contracts.json` records exact paths, labels, URLs and reading extents.
`retrieval-pinned.json` identifies the stored source bytes. The entire
preprints-tree was screened for companions: there is one centered endpoint
family here; the other maximal titles concern different operators or subjects.
No newer upstream dependency is introduced. The upstream proof is accepted,
not audited. Reading its interfaces is not an independent validation of it.

## 3. Complete proof of technical statement A

We supply details because boundedness alone is insufficient and because the
scope includes tails. The argument is credited below, not treated as novelty.

### 3.1 Signed capped envelopes

For t>0 let S_t g = sup_{0<r<=t} A_r g, retaining the sign of g.
For real W11 input it is in W11_loc and

    integral |gradient S_t g| <= C integral |gradient g|.         (3.1)

Here and below S_t need not be globally integrable. To see (3.1), take the
monotone finite envelopes S_{2^{-n}t,t}g. They converge locally in L1, since
their absolute values are bounded by M|g| in L2. The signed band estimate
and distributional lower semicontinuity first give a finite derivative measure.
To remove its singular part, repeat the source null-set localization: for a
compact null K and a dyadic u<=t, split at u. On an arbitrarily small open
neighborhood O of K, the large-radius envelope costs at most
|O| ||gradient g||_1/(pi u^2). Cover O by squares of side u, and on each use
chi_Q(g-average_{5Q}g). The small-radius gradients are unchanged there, and
the signed band bound costs C integral_{K_{6u}} |gradient g| after bounded
overlap. First shrink O, then u; this kills the singular measure on K.
Inner regularity completes the claim. The argument works for any t by using
lower bounds 2^{-n}t and dyadic fractions of t in the split. Arbitrary finite
splits are not needed.

For a square Q of side t, a vector a and an affine P(y)=a dot y+b, choose b
so that g-P has mean zero on 5Q. Put h=chi_Q(g-P), with chi_Q=1 on 3Q,
supported in 5Q and |gradient chi_Q|<=C/t. Poincare gives

    ||gradient h||_1 <= C integral_{5Q}|gradient g-a|.

Every radius <=t centered in Q lies in 3Q. Disk averages preserve affine
functions exactly, so S_t h=S_t g-P on Q. Applying (3.1) to h proves

    integral_Q |gradient S_t g-a|
        <= C integral_{5Q}|gradient g-a|.                       (3.2)

This is the strong estimate used here; there is no inference of strong
compactness from an L1 bound alone.

For any bounded K and g_j -> g in W11, (3.2) implies

    lim_{t down to 0} limsup_j
        integral_K |gradient S_t g_j-gradient g| = 0,            (3.3)

where t may be restricted to a dyadic sequence. Indeed choose a smooth phi
with ||gradient(g-phi)||_1<epsilon, tile the squares meeting K at scale t,
and set a_Q=gradient phi at the center. The sums of the 5Q errors are at most
C ||gradient(g_j-phi)||_1 plus C_K times the modulus of continuity of
gradient phi at 4t (for small t use one fixed bounded neighborhood of K).
Add integral_K |gradient g_j-a_Q| and then let j -> infinity, t ->0,
epsilon ->0. Bounded overlap controls all sums.

### 3.2 Positive lower radii

For nonnegative g in W11 define L_t g=sup_{r>=t} A_r g. It is globally
Lipschitz with bound ||gradient g||_1/(pi t^2). If g_j -> g in W11, then
L_t g_j -> L_t g uniformly and

    gradient L_t g_j -> gradient L_t g in L1(K)                 (3.4)

for every bounded K and fixed t>0. The zero limit case follows directly from
the Lipschitz bound. Otherwise L_t g(x)>0 at every x. Optimizers r_j exist:
averages are continuous in radius and tend to zero at infinity. At fixed x,
choose a radius with positive limit average; it bounds all large-j optimizer
radii above by a finite number depending on x. The lower bound is t.

For W11 input A_r g is C1 in x, with gradient A_r(gradient g), jointly
continuous for r>0. This follows by continuity of disk integrals of an L1
function, including in x and r, and the distributional convolution identity.
At every point where L_t g and all L_t g_j are differentiable, touching with
an attaining radius gives gradient L_t g_j=A_{r_j}(gradient g_j), and the
same for g. Any convergent subsequence of r_j has a limit attaining L_t g;
uniform convergence of the averages and

    sup_{r>=t} |A_r(gradient g_j-gradient g)|
        <= ||gradient g_j-gradient g||_1/(pi t^2)

show that all subsequential gradient limits equal gradient L_t g. Dominated
convergence on K, using the common Lipschitz bound, proves (3.4).

### 3.3 Joining at contact points

Assume g_j,g>=0 and g_j -> g in W11. Put H_j=M g_j, H=M g. Planar Sobolev
embedding and the strong L2 maximal bound give H_j -> H in L2. The same
holds for S_t g_j -> S_t g, since their difference is bounded by M(g_j-g).

Set E_j(t)={S_t g_j>=L_t g_j}, F_j(t)=E_j(t)^c. Sobolev equality-set and
maximum rules give gradient H_j=gradient S_t g_j on E_j(t), and gradient
H_j=gradient L_t g_j on F_j(t); ties cause no difficulty.

On F_j(t), (3.4) deals with gradient L_t g_j-gradient L_t g. The remaining
integral of |gradient L_t g-gradient H| tends to zero: the integrand is zero
a.e. where L_t g=H, by equality-set locality. Where L_t g<H, the equality
H_j=L_t g_j defining F_j(t) becomes impossible in measure, since H_j -> H
in measure and L_t g_j -> L_t g uniformly. Truncate the fixed L1 integrand
and the positive gap to justify dominated convergence in measure. Thus

    integral_{K cap F_j(t)} |gradient H_j-gradient H| ->0.       (3.5)

On E_j(t), the error is at most

    integral_K |gradient S_t g_j-gradient g|
      + integral_{K cap E_j(t)} |gradient g-gradient H|.          (3.6)

Let v=|gradient g-gradient H|. It vanishes a.e. on {H=g}. Since
S_t g down to g a.e. as t down to0, for every eta>0,

    lim_{t down to0} limsup_j
       |K cap E_j(t) cap {H-g>eta}|=0.                          (3.7)

For clarity: E_j(t) implies H_j=S_t g_j. Away from the exceptional set
{S_t g-g>=eta/2}, the two convergences in measure make that equality
impossible on {H-g>eta}. The exceptional set shrinks to measure zero.
Truncating v and then letting eta down to0 gives
lim_t limsup_j integral_{K cap E_j(t)} v=0. Combine (3.3), (3.5), (3.6).
This proves gradient H_j -> gradient H in L1(K).

### 3.4 A global tail estimate

For nonnegative g in W11 and R>0,

    integral_{|x|>4R} |gradient M g|
       <= C integral_{|x|>R}|gradient g| + C ||g||_1/R.          (3.8)

Choose a cutoff theta_R, zero in B_R, one outside B_{2R}, between zero
and one, with gradient bounded by C/R; put h=theta_R g. For |x|>4R,
any radius r<=|x|/2 sees only h=g. If any such radius attains M g, then
M h=M g at x since 0<=h<=g, so their gradients agree a.e. on that set.
The same is true at contact points M g=g, because h=g there. The integral
of |gradient M h| is at most C ||gradient h||_1, which has the claimed
bound with tail R. The left side of (3.8) uses 4R so that these disks are entirely in the
region where theta_R equals one.

Every remaining point has an attaining radius r>|x|/2. Positivity, the
interior radial maximizing identity and integration by parts give

    |gradient A_r g(x)| <= (2/r) A_r g(x)
                         <= C ||g||_1/|x|^3.                   (3.9)

These identities apply to W11 input at every positive radius: use the
continuous W11 trace on concentric circles in a compact annulus. Explicitly,
if V(r)=integral_{B(x,r)}g and J(r)=integral_{partial B(x,r)}g, then
V'=J, derivative_r A_r g=J/(pi r^2)-2V/(pi r^3), and
|integral_{B(x,r)}gradient g|<=J. These expressions have continuous versions
in r>0: one can also write J(r)=2V/r+(1/r) integral_B gradient g dot(y-x).
The identity initially holds for a.e. r and extends by this version; J is
nonnegative by nonnegative traces. At a maximizing radius the radial derivative
is zero. Touching then identifies gradient M g. Integrating |x|^{-3} outside
4R is O(1/R), proving (3.8).

For completeness positive-radius attainment fails only if M g=g (or g=0):
averages tend to zero at infinity and to g at a Lebesgue point as r down to0.
Consequently the contact and attaining-radius sets cover almost every point.
Measurability of the split follows by restricting the continuous radius
families to rational radii and using equalities of their suprema.

For a W11 convergent sequence g_j, the tail integrals of gradient g_j are
uniformly small for large j, and the L1 norms of g_j are bounded. Thus (3.8)
makes gradient M g_j tight in L1. Combine this with local convergence to
obtain global convergence.

Finally g_j=|f_j| -> |f|=g strongly in W11. The chain rule gives
 gradient |f_j|=sgn(f_j) gradient f_j a.e.; gradient f=0 a.e. on {f=0}.
From every subsequence choose one with f_j -> f a.e. Dominated convergence
applied to (sgn(f_j)-sgn(f)) gradient f, together with strong convergence of
gradient f_j, proves convergence of the absolute-value gradients on that
subsequence. The subsequence principle gives the full claim. If f=0, the
source norm bound alone suffices. This completes the proof of (A).

## 4. Actual work on B and the unpaid step

### 4.1 The lower passage is paid, the upper passage is not

Under (B-in), the planar BV embedding bounds ||f_j||_2 uniformly. The weak
(1,1) maximal estimate and |M f_j-M f|<=M(f_j-f) give convergence in measure
of the outputs. Their uniform L2 bound gives uniform integrability on every
bounded K, hence M f_j -> M f in L1(K). Distributional lower semicontinuity
therefore proves

    |D(M f)|(R^2) <= liminf_j |D(M f_j)|(R^2).                  (4.1)

One may obtain the global inequality by first using compactly supported vector
tests, or by exhaustion. The source upper bound gives only

    limsup_j |D(M f_j)|(R^2) <= C |Df|(R^2),                   (4.2)

which is not the required reverse of (4.1).

Here is a precise sufficient unpaid statement, formulated as measure
concentration rather than hidden in a compactness claim. Write nu_j=|D(M f_j)|.
For every sequence (B-in), prove BOTH

    lim_{R->infinity} limsup_j nu_j(R^2 \ B_R)=0,              (U-tail)

and, for every weak-* limit nu of any subsequence of nu_j,

    nu <= |D(M f)| as Radon measures on R^2.                  (U-sharp)

Together with local L1 convergence and (4.1), these imply (B-out): tightness
makes total masses converge along subsubsequences, and lower semicontinuity
gives the reverse measure inequality, forcing equality. Conversely B-out,
with local L1 convergence, forces tightness and equality for each cluster
measure by the same variation lower-passage argument. Thus U-tail/U-sharp
preserve ALL original quantifiers; they are not additional hypotheses being
assumed. They are not proved here.

The substantive local bottleneck in U-sharp is not an omitted application of
Vitali: the source gives a constant-C control of variation at vanishing radii,
while U-sharp requires the exact limiting output variation. An individual
bound on |D^j M f_j| does not bound the absolutely continuous part of D(M f_j)
concentrating into a limiting jump. Cantor concentration is also retained.
Even staircase approximants of a smooth contact region need a directional
calibration argument; strict BV convergence does not give
||Df_j-Df|| ->0. Accordingly this report does not claim that jumps alone are
the only remaining case. The global Sobolev tail proof above is not silently
promoted to all BV sequences either.

A concrete necessary special case of the unpaid upper passage is:
for EVERY finite-measure finite-perimeter E and every nonnegative smooth
compact probability mollifier rho, prove

    limsup_{epsilon->0} integral |gradient M(1_E*rho_epsilon)|
        <= |D(M 1_E)|(R^2).                                  (4.3)

The source norm bound and its already-proved BV corollary do not give (4.3).
This necessary special case is not substituted for B. No counterexample to B
or (4.3) has been produced.

### 4.2 Why the affine route cannot be reused as if strict were strong

In one normal variable, staircase approximants to an increasing affine ramp
have derivative measures converging weakly with the same masses. Their
atomic derivative measures and the limiting absolutely continuous derivative
are mutually singular. On an interior interval their difference therefore has
variation approaching twice the ramp variation, not zero. Here is a compact
planar realization that also verifies strictness, rather than assuming that a
transverse product cutoff preserves it. Choose a smooth compact f that equals
x_1 on a rectangle U. Choose 0<=chi<=1, smooth and compactly supported in U,
with chi=1 on a smaller rectangle Q. Set v_j(s)=floor(j s)/j and

    f_j(x)=f(x)+chi(x)(v_j(x_1)-x_1).

Then ||f_j-f||_1=O(1/j). In U the derivative equals a positive e_1-directed
measure

    e_1 [(1-chi) dx + chi (Dv_j tensor dx_2)]

plus (v_j-x_1) gradient chi dx, whose total variation is O(1/j).
The positive measure in brackets has mass tending to |U|, by Riemann sums;
outside U the derivative is unchanged. Thus |Df_j|(R^2)->|Df|(R^2).
On Q, however, Df_j and Df are mutually singular, and
|Df_j-Df|(Q)->2|Q|. Standard sufficiently fine mollification of each f_j,
chosen after j, also produces smooth strict approximants exhibiting a
nonvanishing gradient L1 discrepancy on a fixed smaller rectangle: choose
the mollifier so that the normal derivative is concentrated in strips of
width o(1/j) around the staircase sheets. Their complement has derivative
near zero although gradient f=e_1. This latter observation is not used in
any claimed theorem.

Consequently (3.2) applied with a local affine P does not have a small right
side uniformly in strict approximants. This is a failure of that proof route,
not a disproof of B.

### 4.3 Exact flat-layer calculation: the missing half cannot be ignored

These are local translation-invariant normal models, not global BV(R^2)
inputs. They describe variation per unit tangential length and may be used
only inside a region where the tested disks remain in the model patch.
They do not settle arbitrary curved jumps or full B.

For g(s)=a+(b-a)1_{s>0}, 0<=a<b, the cap-t disk envelope is

    S_t g(s) = a,                           s<=-t,
             = a+(b-a)F(s/t),               -t<s<0,
             = b,                           s>0,

where F(z)=1/2+(arcsin z+z sqrt(1-z^2))/pi for |z|<=1. This follows by
slicing the unit disk; for s<0 the averaging fraction increases with radius,
so the largest admissible radius t is optimal. At s>0 the zero-radius limit
already equals b. Its derivative has an absolutely continuous mass (b-a)/2
on (-t,0) and a jump mass (b-a)/2 at zero: total b-a. The value at zero is
irrelevant to its derivative measure. With a constant competing baseline c
in [a,b], max(S_t g,c) is increasing and its total normal variation is b-c.
The nonlocal baseline of a true full maximal function at a flat jump is at
least the midpoint. This calculation agrees with, rather than improves, the
credited Lahti--Weigt half-jump bound. When t decreases, the continuous half
can concentrate at the interface; counting only jumps loses it.

For an actual sign-crossing approximation take

    f_w(s)=max(-1,min(1,s/w)),     h_w(s)=1-|f_w(s)|=(1-|s|/w)_+,

where 0<w<t. The normal marginal of a centered disk is

    k_r(s)=2/(pi r) sqrt(1-s^2/r^2) 1_{|s|<r}.

Then S_t |f_w| = 1-inf_{0<r<=t}(k_r*h_w). Both k_r and h_w are even and
nonincreasing in |s|, so their convolution has that property. An elementary
proof writes each as a positive superposition of centered interval indicators;
the convolution is the length of the overlap of two centered intervals and
is even and nonincreasing. The infimum retains this property. Consequently
S_t |f_w| is even and nondecreasing in |s|, tends to one at both ends, and its
total normal variation is twice its deficit at zero. At zero the disk average
of h_w decreases with r: substitute s=r z and use that h_w(r z) decreases
pointwise in r. Thus, with q=w/t,

    Var_R(S_t |f_w|) = 2 (k_t*h_w)(0)
      = (8/pi) [ (q sqrt(1-q^2)+arcsin q)/2
                 - (1-(1-q^2)^(3/2))/(3q) ].                 (4.4)

Moreover the elementary bounds 1-z^2 <= sqrt(1-z^2) <=1 on [0,q] give

    (4q-2q^3/3)/pi <= Var_R(S_t |f_w|) <=4q/pi.               (4.5)

Thus this symmetric sign-crossing valley is removed as w/t->0. This is an
exact supporting calculation, not proof for arbitrary normal profiles,
tangential oscillations, Cantor layers, or arbitrary strict BV sequences.
In particular, replacing f_j by |f_j| and assuming strict BV convergence of
that sequence would be invalid: across a -1/+1 jump, |f_j| can have a valley
with variation two while |f| has no local variation. The model proves removal
for the stated profile rather than assuming it generally.

`checks.py` reproduces exact polynomial integral coefficients in (4.5), tests
the closed form (4.4) against independent quadrature, and checks the normal
step distribution. These checks do not prove B or certify an independent
proof review.

## 5. Strong primary comparison and novelty limits

**González-Riquelme, arXiv:2109.09691v1**, *Continuity for the one-dimensional
centered Hardy--Littlewood maximal operator at the derivative level* (2021
preprint; source cites JFA 2023). Theorem 1 is W11(R) -> L1 continuity. Most
decisively, Proposition 12 on pp.7--8 subtracts affine functions on intervals,
uses a local variation bound for the residual, and approximates the input
derivative. Lemmas 7--10 and Proposition 11 handle the nonlocal part. Section
4 joins by maximum/equality sets. Those are exactly the operations in A.
The planar source signed-band estimate plus square Poincare supplies their
higher-dimensional local interface. A new planar statement does not by itself
make that assembly substantial. **This is why A was rejected as a nomination.**
The paper's BV-norm continuity question is different from B's strict topology;
no claim that its question is exactly B is made.
Primary PDF: https://arxiv.org/pdf/2109.09691v1 .

**Beltran--González-Riquelme--Madrid--Weigt**, *Continuity of the gradient of
the fractional maximal operator on W11(R^d)* (primary author-hosted 2021
version, published MRL 2023). Theorem 1.1 has 0<alpha<d, not alpha=0, and
is stated for the norm of the gradient. The actual proof splits at a positive
radius, uses local estimates on good balls and a positive-order Poincare gain
to make small-radius contributions small. Proposition 2.4 gives the optimizing
ball derivative interface. None permits setting alpha=0 or passing from strong
W11 to arbitrary strict BV for free. Its positive-radius compactness/dominated
convergence operation is credited in A, not claimed new.
Primary PDF: https://jnwt.eu/publications/Continuity_of_the_Gradient_of_the_Fractional_Maximal_Operator_on_W11.pdf .

**Carneiro--Madrid--Pierce**, *Endpoint Sobolev and BV continuity for maximal
operators*, arXiv:1708.06051v1 (2017). Theorem 1 treats the uncentered
one-dimensional W11 operator; Section 5 uses lateral/one-sided maxima,
optimizer convergence and absolute-value reduction. Its BV norm in Section
1.3 is not strict convergence, and its discrete BV theorem is not a planar
continuum theorem. No transfer is inferred from their titles or abstracts.
Primary PDF: https://arxiv.org/pdf/1708.06051v1 .

**Lahti--Weigt**, *The centered maximal operator removes the non-concave
Cantor part from the gradient*, arXiv:2510.01936v1 (2025). Theorem 1.1
concerns non-concave blow-ups at Cantor points; Theorem 1.2 assumes BV_loc
regularity of Mf and gives the sharp individual jump estimate
|D^j Mf|<=1/2 |D^j f|, plus conditional removal of the Cantor part.
Proposition 4.15 proves the jump estimate by quasicontinuity, traces,
small-radius exclusion above the upper trace and continuity of a positive-radius
truncation. Theorem 4.14's Cantor conclusion retains its blow-up hypothesis.
The paper explicitly notes singular measures with only linear blow-ups, so
that hypothesis is not silently dropped here. Individual jump control is
stronger than an abstract regularity assertion but does not bound continuous
variation concentrating into a jump along a strict sequence. Applying their
conclusion to g=|f| is legitimate for a single input; treating |f_j| as a
strictly convergent sequence is not. The full source proof operations read
here do not pay U-sharp/U-tail.
Primary PDF: https://arxiv.org/pdf/2510.01936v1 .

**Hajłasz--Malý**, *On approximate differentiability of the maximal function*
(2010), the stored preprint Theorem 1.2/Remark 1.3 (published
Theorem 2/Remark 3), and the source-cited lower-radius Lemma 8 are credited optimizing
and Lipschitz antecedents; approximate differentiability is not strict BV
continuity. **Saari**, *Poincare inequalities for the maximal function*,
arXiv:1605.05176v1, Section 3.1's mean subtraction/local-nonlocal split is
already cited and used by the pinned source. Neither is claimed a new step.
Exact read extents, including parts only searched/retained, are in the source
contracts; no full reading of every stored primary article is claimed.

The search was bounded: centered continuity, strict BV maximal continuity,
fractional endpoint continuity and centered singular-gradient regularity.
`search-log.md` preserves query strings and primary leads. Several search hits
were automatically generated expositions of the pinned OpenAI papers; they
were not used as primary mathematical or novelty evidence. No database-wide
or worldwide priority certificate, and no claim that B has no antecedent, is
made. The absence of a direct hit does not prove novelty.

## 6. Handoff, reproducibility and rights

All writes are confined to this directory. Inputs/private contains pinned
sources, primary reading copies and frozen context; these retain their original
rights and are not releasable under the original-artifact licenses. No agents,
Lean files, manuscript, commits, shared-ledger edits, count changes, uploads,
messages to third parties or public submissions were made.

Run `python3 -B verify.py`. It authenticates the immutable input/output
inventories and stored receipts before executing the checks, compares the
replayed stdout byte-for-byte, and never regenerates receipts or reseals.
`seal.json` hashes both inventories; authenticate its detached hash from the
handoff. `mutation-tests.json` records tests on disposable copies only.
Checks support the elementary layer calculations, not B, substantiality,
independent proof review or upstream truth.

Parent decision requested: retain this as an unresolved research report, with
A technical and B unresolved; do not commission a manuscript/formalization or
count a result from this lane on the evidence here. A future attempt must pay
U-sharp and U-tail without adding sign, regularity, common-support or
Cantor/jump restrictions to B.

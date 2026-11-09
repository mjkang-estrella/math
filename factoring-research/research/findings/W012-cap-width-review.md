# W012 cap-width review — accepted geometry, qualified covering consequence

2026-10-08. Independent proof audit of the frozen parent derivation.
Disposition: **REVISED / ACCEPT the cap-width lemma and the explicit-cover
obstruction below.** Verified factoring-complexity improvement: **NONE**.
No candidate run, parameter/prime/depth sweep, optimizer installation, shared
code/Lean/state edit, delegation, commit or publication was performed.

The chord identity, vertical lattice period, nearest-residue argument and
strict-cap application are correct. The geometric lemma actually does not need
`m^2 <= R`. The covering conclusion needs a specified retained population,
query-domain clipping, and a fixed per-query information model. The claimed
cost of visiting every large-modulus chart is conditional on doing that
enumeration; empty charts need not be visited. These repairs preserve an
elementary `Omega(N^(1/4)/log N)` obstruction to the stated complete integer
cover with `m^2 <= R`, on a balanced block of length comparable to `sqrt(N)`.
They imply no lower bound for finding one factor.

## 1. Precise geometric statement

Let `R >= 2`, `N >= R^2` and `m >= 1` be integers, with `gcd(N,m)=1`.
Let `j` be a unit modulo `m`, and use the W012 lattice as defined by its
congruences:

    L_j = {(x,y) in Z^2 : x = j (mod m),
           y = N*j^(-1) (mod m), xy = N (mod m^2)}.

For `m=1`, this means all of `Z^2`. No basis choice is needed for this audit;
the independent review of the quotient-coordinate bijection is not duplicated.

Suppose a convex set `K` contains every point `(x,N/x)` for `x` in a connected
real interval `I` contained in `[R,2R]`, and contains no point of `L_j`.
The interval may be open, closed or half-open. Then its diameter satisfies

    diam(I) <= m*A,       A = sqrt(1 + 32*R^3/N).                 (G)

For a nonempty closed interval `[u,v]` with `u<v`, the proof gives the strict
bound `v-u < m*A`. In particular the parent's weak bound is safe. The same
conclusion holds if emptiness is only required inside `1 <= y <= N`, since
the entire hull of the relevant arc already lies inside that vertical box.

There is no restriction on `m` in (G). For large `m`, the conclusion can be
weaker than the trivial `diam(I) <= R`; this does not make it false.

## 2. Complete proof

### 2.1 The ordinate period is exactly m squared

If `x = j (mod m)`, then `gcd(x,m^2)=1`. Thus the product congruence is
equivalent to

    y = N*x^(-1) (mod m^2).

Reducing this congruence modulo `m` gives the required ordinate residue in
the definition of `L_j`. Conversely it implies both ordinate conditions.
Consequently the allowed ordinates at every such abscissa are exactly
`r_x + m^2 Z`, with least positive period `m^2`.

For any real `t`, exactly one member of this progression lies in
`[t,t+m^2)`: explicitly

    y = r_x + m^2*ceil((t-r_x)/m^2).

We will take `t=N/x`. The lower endpoint may be attained; a factor point on
the arc is an obstruction to an empty cap just as an interior point is.

### 2.2 Chord identity and the actual convex hull

For `u<v`, the chord of `f(x)=N/x` over `[u,v]` is

    c(x) = ((v-x)*N/u + (x-u)*N/v)/(v-u)
         = N*(u+v-x)/(u*v).

Subtracting `f(x)` gives exactly

    c(x)-f(x) = N*(x-u)*(v-x)/(u*v*x).                         (H)

Indeed, `x*(u+v-x)-u*v = (x-u)*(v-x)`. All denominators are positive.
Since `f''(x)=2N/x^3>0`, the set

    { (x,y) : u<=x<=v, f(x)<=y<=c(x) }

is convex and contains the arc. Conversely the chord point `(x,c(x))` is
a convex combination of the two arc endpoints, and each point on the
vertical segment from `(x,f(x))` to `(x,c(x))` is a convex combination of
those two points. This set is exactly the arc's convex hull. A convex set
containing the arc must therefore contain this whole region; no closedness
assumption on that convex set is needed.

### 2.3 Nearest residue and the width contradiction

Write `W=v-u` and `h=(u+v)/2`. The grid `j+m Z` has an element `x` with
`|x-h|<=m/2`, by rounding `(h-j)/m` to a nearest integer. If `W>=m`, this
element lies in `[u,v]`, and

    (x-u)*(v-x) = W^2/4 - (x-h)^2 >= (W^2-m^2)/4.

Since `u,v,x <= 2R`, equation (H) gives

    H(x) >= N*(W^2-m^2)/(32*R^3).                            (1)

If `W >= m*A`, then `W>m` and (1) is at least `m^2`. Choose the ordinate
from Section 2.1. It obeys

    f(x) <= y < f(x)+m^2 <= c(x).

Thus `(x,y)` is a lattice point in the hull of the arc, a contradiction.
This proves the strict version for a closed arc. Equality in (1) is enough:
the ordinate rounding error is strictly less than `m^2`. The parent's use
of a strict inequality for (1) is conservative, not erroneous.

When `W<m`, the desired bound is automatic because `A>1`. For any other
connected interval `I`, apply the closed-arc conclusion to each two
interior points, then take the supremum of their distances. This gives
the weak inequality (G) without assuming endpoint exclusion.

### 2.4 The vertical box

Every arc ordinate on `[R,2R]` satisfies

    1 <= R/2 <= N/x <= N/R <= N.

Each chord ordinate is a convex combination of endpoint ordinates and is
therefore also in `[1,N]`. The constructed point lies between arc and
chord, so it satisfies the box constraints. This argument removes the
restriction `m^2<=R` from the geometric lemma.

The parent's alternative estimate is also valid under its hypotheses:

    y < N/x+m^2 <= N/R+R <= N,

because `N>=R^2` and `R>=2` imply `N*(R-1)>=R^2`. The lower box bound
must also be mentioned, as above. Without `m^2<=R`, arbitrary rounded
ordinates need not lie below `N`; only the point forced below the chord
in the width contradiction is guaranteed to do so.

## 3. Application to an exact support certificate

Suppose the paid query minimizes `a*x+b*y`, `a,b>0`, over

    C_[L,U] intersect L_j,
    C_[L,U] = {(x,y): L<=x<=U, 1<=y<=N, xy>=N},

and has a finite exact optimum `s`. Define the **domain-clipped** interval

    I = [R,2R] intersect [L,U]
        intersect {x>0 : a*x+b*N/x < s}.                      (2)

It is connected, possibly empty: after multiplication by `x>0`, the
strict inequality is `a*x^2-s*x+b*N<0`, whose solution is an open interval
when its discriminant is positive. The outer domain intersections may
close one or both endpoints of the resulting interval.

For any closed subinterval `[u,v]` in `I`, both arc endpoints satisfy
`a*x+b*y<s`. All their convex combinations also satisfy this strict linear
inequality, and every point between the arc and chord satisfies it as
well. The arc hull is inside `C_[L,U]`, by Section 2.4. A lattice point in
it would contradict the definition of `s`. Applying (G) and taking
suprema proves

    diam(I) <= min(R, m*A).                                  (3)

This handles quadratic roots outside the balanced block and all strict
versus closed boundary issues. Lattice points on the support line itself
are not excluded, and integer roots of the quadratic require separate
factor tests. A convex query proved infeasible can likewise certify an
empty cap, but in the original small-modulus regime it cannot contain
even one central residue abscissa: Section 2.1 and the parent's box
estimate would then supply a feasible ordinate.

Do not omit `[L,U]` from (2). For a fixed exact illustration, query only
`x=2` with `N=35`, `m=1`, `a=b=1`. The minimum is `s=2+18=20`, yet
`5^2-20*5+35=-40<0` and `5` divides `35`. The inequality certifies
exclusion only within the query domain. This is a domain warning, not a
counterexample to the correctly clipped parent construction.

The optimizer implementation and its bit bound are assigned to reviewer A.
This audit needs only exact optimality and makes no further claim about
that implementation or the full-hull literature assigned to reviewer B.

## 4. Finite covering statement, including constants

Keep a **fixed** `m` and block `[R,2R]`. Let `S` be the actual finite set
of retained integer candidates in this block, all coprime to `m`.
Each counted query contributes at most one connected cap certificate
for one chart `j`, and at most `k` additional isolated candidate tests,
where `k` is an absolute constant. Require that all members of `S` are
eventually accounted for by these certificates or isolated tests.

Any interval of length `W` contains at most `floor(W/m)+1` integers
in one residue class. We can handle the integer equality case more
sharply: if a cap accounts for `n>=2` distinct abscissas, take its
smallest and largest such abscissas as closed-arc endpoints. Their
distance is at least `(n-1)*m`, while the strict closed-arc bound gives
`n-1<A`. Hence `n<=ceil(A)`; the same inequality is automatic for
`n<=1`. One cap can therefore account for at most

    D = min( floor(R/m)+1,
             ceil(sqrt(1+32*R^3/N)) )                       (4)

candidate integers. This includes query-domain endpoints, and improves
the parent's safe `floor(A)+1` by one when `A` is an integer.
For any adaptive order of queries, union cardinality is at most the sum
of the individual cardinalities. Therefore `Q` queries satisfy

    |S| <= Q*(D+k),
    Q >= ceil(|S|/(D+k)).                                    (5)

If there are `T0` additional isolated tests outside those charged to
queries, replace `|S|` in the numerator by `max(0,|S|-T0)` and pay their
cost separately. Similarly, preprocessing that removes candidates must
reduce `|S|`; the word “retained” cannot preserve the old numerator.
Overlapping caps and repeated endpoint tests only weaken their coverage.
If one paid operation emits `b` distinct caps, the relevant inequality is
`|S| <= b*Q*D + k*Q`; the one-cap query conclusion cannot be reused with
`b` unbounded. Implicit batch representations need their own cost model.

### 4.1 All integer candidates, small modulus

For the complete set of coprime integers, its exact size is

    M = sum over unit j mod m of
          (floor((2R-j)/m)-floor((R-1-j)/m)).                 (6)

There are `R+1` consecutive integers in the closed block, so

    phi(m)*floor((R+1)/m) <= M
        <= phi(m)*ceil((R+1)/m).                             (7)

In particular `M >= phi(m)*floor(R/m)`. When `m^2<=R`,
`floor(R/m)>=R/(2m)`, and `N>=R^2` gives

    D+k <= sqrt(1+32R)+1+k
         <= (sqrt(33)+1+k)*sqrt(R).

Thus the following explicit version of the parent's integer bound holds:

    Q >= sqrt(R)*phi(m)
         / (2*m*(sqrt(33)+1+k)).                             (8)

If earlier work has removed `e` of these `M` integers, the rigorous
replacement is `Q >= ceil(max(0,M-e-T0)/(D+k))`. There is no unconditional
bound with numerator `M` for an arbitrary retained subset. In particular,
an empty retained set requires zero cap queries.

An external prime-distribution or totient-density theorem is not needed
for a useful exponent statement. If the distinct prime divisors of `m`
are `p_1<...<p_t`, then `p_i>=i+1`, so

    m/phi(m) = product p_i/(p_i-1)
             <= product (i+1)/i = t+1 <= 1+log_2(m).

For `m=1` the empty product gives the same conclusion. Combining this
elementary inequality with (8) proves `Omega(sqrt(R)/log(R+2))` for the
specified complete integer cover, uniformly over `m^2<=R` and fixed `k`.
This density estimate is a proof device, not an algorithm for factoring
or constructing `m` for free.

### 4.2 Large modulus

Equation (5), with the minimum in (4), remains valid for every `m`.
For `m>sqrt(R)`, even the entire block contains fewer than
`sqrt(R)+1` integers of any one residue class. Thus a large modulus
does not allow one chart certificate to dispose of arbitrarily many
central candidates.

There is also an occupied-chart bound. Let `H` be the number of residue
classes represented by `S`. One chart query and `k` isolated tests can
account for candidates in at most `k+1` such classes, hence

    Q >= ceil(H/(k+1)).                                     (9)

For all coprime integers and `sqrt(R)<m<=R+1`, every unit class is
represented, so `H=phi(m)`. In that range (9) justifies a stronger
chart-count obstruction and, by the elementary density estimate above,
at least `Omega(sqrt(R)/log(R+2))` queries. No unnecessary enumeration of
empty classes is being charged here.

For `m>R+1`, the equality `H=phi(m)` can fail badly. A fixed exact
counterexample is `R=2`, `N=35`, `m=12`: `gcd(N,m)=1`, but none of
`2,3,4` is coprime to `12`. Thus `M=H=0`, and zero chart queries cover
all retained central candidates, whereas `phi(12)=4`. This does not
refute the literal statement “enumerating every unit residue costs
phi(m)”; it refutes treating that enumeration as mandatory.

The parent sentence for `m>sqrt(R)` is therefore acceptable only as a
cost statement about an implementation explicitly visiting all units,
or with the occupied-chart qualification just proved. Very large
moduli and prior arithmetic sieves may remove many candidates; their
construction, bit lengths and deductions require separate accounting.
This audit supplies no lower bound for all such preprocessing.

### 4.3 Constant isolated tests and prime-only preprocessing

Two quadratic endpoints, a returned optimizer abscissa and a chosen
midpoint contribute at most four isolated candidate tests per query.
Any fixed number merely changes `k` in (5) and the constants in (8).
A successful gcd that stops the search is outside the complete-cover
obligation. If a gcd is used to rule out many other candidates, that is
additional information and must be counted as such, rather than called
one isolated test. In particular a gcd of a constructed large product
is not within this information model. For a tested coordinate in the
same block, its proper divisors are below `R` except possibly the
endpoint `R` when the coordinate is `2R`, so this boundary use remains
a constant contribution.

The optional prime-count corollary is **not adopted as an unconditional
claim** here; no primary prime-distribution source was audited. The
self-contained statement is simply: for any prime-only retained set
`S`, (5) holds with its actual cardinality. Conditional on a separately
justified lower bound `|S|>=c*R/log R`, it yields
`Omega(sqrt(R)/log R)`. When `m^2<=R`, primes in `[R,2R]` are larger
than `m` and hence coprime to it; nevertheless the number of primes and
the cost/effect of obtaining that retained set are separate obligations.
The integer count (7) does not survive arbitrary composite elimination.

## 5. Computational implication and scope

For a factoring application, choose an actual block inside the factor
search range, for example `R=floor(isqrt(N)/2)` for sufficiently large
`N`. Then `[R,2R]` lies below `sqrt(N)` and `R=Theta(sqrt(N))`.
The hypothesis `N>=R^2` by itself does not guarantee `2R<=sqrt(N)`;
if using another block, clip to the search range and count its actual
remaining length and candidates.

For complete coverage of all coprime integers in such a block, with
`m^2<=R`, fixed `k`, and separately charged single-chart caps, (8)
forces `Omega(N^(1/4)/log N)` queries by the elementary density proof.
Charging at least one operation to each query already rules out an
`O(N^alpha poly(log N))` bound with fixed `alpha<1/4` for this coverage
implementation, in particular any exponent below `1/5`. An optimizer's
polynomial overhead does not undo a lower bound on the number of calls.
This is a query-count consequence; it does not multiply by an optimizer
upper bound and call that product a bit-complexity lower bound.

This says nothing universal about early-stopped factoring. A strategy
may find a factor before producing the cover, use preprocessing to
change `S`, obtain information from the optimizer beyond this single
cap, combine charts in a different primitive, or process many caps
implicitly. Adaptive slope selection alone cannot enlarge the
single-cap capacity in (4), but a factor-selective success theorem
would be a different claim. Nor is this a full-hull vertex bound.

The next useful symbolic question is a specified, paid mechanism for
batching cap information or a proved factor-selective navigation rule.
Its success and total cost must be stated without assuming complete
coverage, a supplied useful residue, or a free sparse retained set.
No numerical experiment is selected by this review.

## 6. Frozen evidence and validation

The assignment, eight local input snapshots, and their SHA-256 hashes
are recorded under the exclusive `W012-cap-width-review*` prefix.
All mathematical source reliance is on the frozen W012 brief and parent
cap note. The proof above is self-contained; no external paper result,
novelty priority claim or primary-source audit is imported from reviewers
A or B. There are no downloaded external sources for this review.

The accompanying standard-library script checks only three fixed exact
certificates: a chord/lattice obstruction, the query-domain illustration,
and the empty occupied-chart counterexample. It neither searches for
examples nor calls a factoring candidate or support optimizer. Its
source, result JSON and all deliverables are hashed in the delivery
manifest. These finite checks corroborate arithmetic only; the general
claim is established by Sections 1–4, not by the script.

The final integrity check found concurrent changes to the live
`research/STATE.md` and `research/hypotheses/W012.md`. Their frozen
copies are intact and remain the review inputs; the parent cap note
still matched its frozen copy at that check. No live source was
overwritten or silently substituted. The delivery manifest records
both frozen and delivery-time live hashes so the parent can reconcile
later revisions explicitly.

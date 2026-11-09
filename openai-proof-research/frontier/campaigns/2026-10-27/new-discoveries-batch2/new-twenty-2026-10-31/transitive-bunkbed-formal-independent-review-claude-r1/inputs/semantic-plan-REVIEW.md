# Independent ordinary semantics and proof-plan review: 382297

Disposition: REJECT the r2 reflected-fiber equality and diagonal endpoint claims. PASS the corrected ordinary Reach/state construction and reflection-DOMINANCE count route below. Recommend a narrow literal membership/Reach bridge milestone next. No Lean run or implementation; no formal endpoint certified. Credit 0; campaign remains 52/60 beyond 39. Recommendations only; root adjudicates.

## Scope and evidence verdicts

The reviewed literal model has vertices Fin n × Bool, independent fair horizontal tokens for each i<j and EACH layer, and ONE fair vertical token per index enabling both vertical directions. Reach is the actual reflexive transitive closure of Arc. All n and fixed u,v are quantified, without source averaging or additional conditions. There are n² distinct tokens. The target is card{ω | Reach n ω (u,false) (v,true)} ≤ card{ω | Reach n ω (u,false) (v,false)} over all assignments.

Proved-source verdict: root's integration record reports four new strict builds and hash matches; I accept those as inherited build evidence, not my own replay or safety audit. BunkbedCount's body supplies Fintypes only, despite its broader header. BunState supplies definitions, not Reach correctness theorems. BunReach proves indicator equations and congruence. BunBridge proves only wres, restriction and agreement. BunkbedBase supplies literal arcs, monotonicity, prefix agreement and reach_char. The actual membership bridge, fresh-token counts, count recurrence, reflection induction and endpoint remain absent from the read production bodies.

Semantics verdict: the valid-strip definitions agree ordinarily with literal Reach, with the proof and guards below. Their comments are not proof evidence. Count-plan verdict: the approved ordinary kernel/dominance route is correct; r2's proposed replacement by same-source flip equality is false. Formal-bridge verdict: UNPAID. No ordinary mathematical gap remains in the corrected route given here, but the formal obligations are substantive.

## Decisive handwritten counterexamples and corrected endpoint cases

Take n=1,u=0,j=0 and the assignment whose sole token, vtok 0, is false. startST and stf are ({0},∅). flipT fixes this vertical token; there are no horizontal tokens. Thus flipAsg fixes the assignment and stf remains ({0},∅), whereas swapping its components gives (∅,{0}). This disproves the exact proposed swap lemma. Among the two window assignments, the count fiber (1,0) has cardinality 1 and its reflection (0,1) has cardinality 0. The analogous terminal pattern TF has cardinality 1 and FT cardinality 0. Both proposed fiber equalities fail, not just their proof strategy. More generally at any valid j=u, flipping horizontal layers leaves vtok u unchanged and hence leaves startST unchanged, which is unswapped whenever that bit is false. A global graph layer flip relates source false to source true; it does not preserve the fixed-source event.

For a concrete nonempty-horizontal trace, set n=2,u=0, both vertical bits false, horizontal (0,1,false) true and (0,1,true) false. The prefix state at 1 is ({0,1},∅). After horizontal-layer flip, source state is still ({0},∅); the false-layer incoming bit is now off, so the state at 1 is ({0},∅), not (∅,{0,1}). This is a single handwritten trace, not an enumeration.

For v=u, reflexivity makes same-layer Reach true for every one of the 2^(n²) outcomes. Opposite-layer Reach holds exactly when vtok u=true, giving 2^(n²-1) outcomes (n≥1 follows from u:Fin n). A path cannot go forward and return to u; with the vertical bit false there is no layer change at index u. Thus 'both-full' is false. For v<u, neither event holds, by index monotonicity: both counts are 0. The phrases v<u and u>v denote the same case, not separate regimes. Only u<v needs the count evolution; no minimum-index workaround is needed. For n=0 there are no u,v:Fin n.

The proposed expression '(stf ...).l = true' is ill-typed: stf is a pair of Finset Nat, l is a Bool, and its components are sets, not indicators. Even a component cardinality comparison is a different proposition. Use actual membership through sval.

## Exact semantic interfaces and a complete ordinary bridge proof

The principal interface, in the notation of the read sources, is: for n:Nat, u i:Fin n, ω:Out n, j:Nat with hj:j<n, and σ:Bool,

  i.val ∈ sval σ (stf n u.val j (wres n j ω))
    ↔ (i.val ≤ j ∧ Reach n ω (u,false) (i,σ)).

In particular for j:Fin n, specialize i=j to obtain membership j.val iff literal Reach at j. The u≤j guard is unnecessary for this full-prefix interface because both sides are false when j<u; if restricting to the active recursion strip, explicitly assume u.val≤j. With general Nat source parameters require u<n, then build u:Fin n. A version for an arbitrary prefix w may quantify any ω with wres n j ω=w; extension by arbitrary outside bits always exists and prefix agreement makes the choice immaterial. res/wres_res must be used at successor levels.

Required structural interfaces for arbitrary w, valid u<n and j<n are: k∈sval σ(stf n u j w) implies u≤k≤j; when u≤j and j+1<n, membership of k≤j is unchanged under the step from res w to w; and the new-index membership at j+1 equals the corresponding Bool component of ind applied to the two actual hor values and fresV. All are immediate ordinary inductions from empty/start/insert, but must be proved formally. At a start, source false is inserted regardless of vertical bit. At a genuine step, the old sets contain no new index, so inserting it raises cardinality by precisely its indicator. For j<u both components are empty. Off-strip Nat calls are dummies: for example n=u=j=0 gives ({0},∅) with no vertex 0:Fin 0. Do not assert unconstrained Nat membership↔Reach. With valid u one could later extend j≥n by stabilization, but this is not needed or licensed by the present interface.

The exact hor interface for m<n, R⊆range m and w:Asg n m is:

  hor hm R σ w = true
    ↔ ∃ k:Nat, ∃ hk:k<m, k∈R ∧ w(fresH hm k hk σ)=true.

Extract a witness from the filtered attached range for the forward direction; conversely insert the attached k and prove the filter predicate true. Reorder conjuncts if desired. Bool-to-Prop is explicitly '=true'. Distinct proof witnesses of k<m yield the same token by proof irrelevance; coercing k to Fin n uses k<m<n. This supplies both horizontal witness transfers, rather than leaving 'hor faithfulness' as an assumption.

Here is a noncircular joint induction proof of the principal interface. Induct on prefix j, proving the support and old-membership stability interfaces along with the two semantic directions for ALL low vertices and BOTH layers. Before u, support is empty and reach_ge excludes all such endpoints. At j=u, monotone paths ending ≤u cannot visit indices other than u: same-layer source has its length-zero path and the other layer has a path exactly if the vertical bit is on. This establishes startST exactly. At a later m=j+1<n, write R,S for the preceding state at res w, and X,Y,Z for its hor/hor/vertical bits.

State→Reach: for an old member use the previous-level semantic induction. For a new false member the explicit ind formula says X or (Z and Y); for a new true member it says Y or (Z and X). A horizontal witness comes from hor and the old-state induction, then append its horizontal arc. In the second alternative append the horizontal arc into the other layer and the single enabled vertical arc at m. This uses the CLOSED formula in X,Y,Z, not circular implications between new Reach predicates. The same proof covers both layers jointly.

Reach→state: for fixed m use induction on the actual ReflTransGen derivation of a path whose endpoint index is ≤m, keeping the endpoint bound generalized. Every predecessor is also ≤m by arc_fst_le. The reflexive endpoint is u,false, present in the state. If the final endpoint is old (<m), apply the preceding-prefix semantic theorem directly to this literal path and carry membership forward by old-index stability (equivalently use reach_agree for an extension of res w). For an endpoint at m, a final horizontal arc has predecessor k<m in the same layer. By the previous-prefix theorem its literal predecessor path supplies k∈R or k∈S. The enabled arc supplies the hor witness, hence ind_fst_or or ind_snd_or supplies new membership. A final vertical arc has predecessor at m in the opposite layer. The INNER derivation induction supplies its new membership; as m was absent from the old sets this is the corresponding ind component=true. The enabled vertical bit and ind_fst_vert/ind_snd_vert then give the desired membership. Thus the vertical transfer consumes a shorter actual path, not an outer index induction at the same index. For old endpoints the endpoint bound on the induction hypothesis is essential; no path may be silently assumed prefix-contained without monotonicity. Together these arguments prove both directions and all witness transfers.

Alternative first-entry proof: when u<m every finite path to m has a first horizontal entrance from k<m, followed only by vertical arcs at m. Repeated vertical steps can be removed; the final layer is either the entry layer or its partner via the enabled vertical token. The same closed X∨(Z∧Y), Y∨(Z∧X) characterization follows. The finite RT induction above is an explicit way to avoid formalizing path lists.

reach_char by itself gives self-referential equations A↔X∨(Z∧B), B↔Y∨(Z∧A). These do NOT uniquely determine A,B: with X=Y=false,Z=true, both (false,false) and (true,true) solve the equations. Literal Reach picks the least closure (false,false). In the graph with n=2,u=0, both incoming horizontals false and vtok 1=true, neither copy at 1 is reachable; one cannot manufacture both from mutual vertical support. Thus a mere rewrite using reach_char and ind_fst/ind_snd is insufficient. The proposed inner RT induction, correctly generalized as above, repairs this genuine logical hazard. The r2 paper-verification assertion alone did not establish it.

## Actual-token fibers, integer counts and the kernel

No independence is assumed from counts. For m<n, Win n m contains (m+1)² tokens: two per ordered i<k≤m, plus the m+1 vertical tokens. For m≥1 split it by tmax<m versus tmax=m; the first part is Win n (m-1), the fresh part consists of 2m horizontal tokens (i,m,σ), i<m, and one vertical token. Projection and piecewise union give an actual assignment bijection

  Asg n m ≃ Asg n (m-1) × (Fresh_m → Bool).

All constructors are disjoint: vertical versus horizontal is a sum tag, horizontal layers are distinct even for the same i, and different i give distinct tokens. Proof fields add no tokens. Each COMPLETE old assignment has exactly 2^(2m+1) extensions. At m=0 use the singleton vertical window directly.

Now fix a complete old assignment h with state sets R,S, cardinalities a,b. They lie below m. Among the fresh tokens, a false-layer incoming tokens and b true-layer incoming tokens are active; these are disjoint even when R and S overlap. The other 2m-a-b horizontal tokens are irrelevant for the new indicators; their arbitrary assignments contribute the common factor 2^(2m-a-b). Z is a separate one-bit factor. Put A=2^a,B=2^b. OR X=0 has one assignment of its a bits, X=1 has A-1; likewise Y has counts 1 and B-1. These statements include a=0 and b=0. Actual active-bit plus Z counts for the four increments are:

  C00=2, C10=A-1, C01=B-1, C11=2AB-A-B.

For 00, X=Y=0 and Z is arbitrary. For 10 require Z=0,X=1,Y=0; for 01 require Z=0,X=0,Y=1. For 11, Z=0 allows X=Y=1, and Z=1 allows every (X,Y) except (0,0): counts (A-1)(B-1)+(AB-1)=2AB-A-B. Multiply EACH by the same irrelevant factor above. Their sum is 2^(2m+1). This is a direct finite Cartesian-product partition of one fiber, not computational enumeration.

Dividing by the extension count gives, with q=1/A,r=1/B,

  K_s(s)=qr,
  K_s(s+(1,0))=(1-q)r/2,
  K_s(s+(0,1))=q(1-r)/2,
  K_s(s+(1,1))=1-(q+r)/2,

and zero elsewhere. This depends only on (a,b), not on the chosen h. Consequently, only AFTER this calculation may old full-prefix fibers with the same counts be combined. If M_(m-1)(s) counts old assignments, then

  M_m(t)=Σ_s M_(m-1)(s)·2^(2m+1)·K_s(t).

The right side is integral by the explicit fiber formula. Normalizing by 2^((m+1)²) yields μ_m=μ_(m-1)K. It is acceptable to use rational probabilities as normalized exact finite counts; there is no measure-theory premise.

At source u the full window has (u+1)² tokens. Its state is ({u},∅) for vtok u=0 and ({u},{u}) for vtok u=1, each with exactly 2^((u+1)²-1) assignments. Other bits, including all incoming arcs at u and all earlier tokens, do not affect this source-fixed state. Thus μ_u(1,0)=μ_u(1,1)=1/2, all other masses zero. No reflected equality holds.

## Correct reflection dominance and payoff

Write ρ(a,b)=(b,a). The explicit K satisfies K(ρs,ρt)=K(s,t), because q and r swap, as do the single-layer increments. Also (a-b) changes by at most one. Therefore a transition cannot go from strictly above a>b to strictly below a<b or conversely; it may hit or leave the diagonal.

For a completely specified finite support, use squares Q_L={0,...,L}². At prefix k≥u the support lies in Q_(k-u+1). Its successors lie in Q_(k-u+2). Extend μ by zero to larger squares before pairing; both squares are reflection-stable. For an above target t in the successor square, equivariance and pairing all predecessors give

 δ(μK)(t)=Σ_s μ(s)[K(s,t)-K(s,ρt)]
           =Σ_(s above) [μ(s)-μ(ρs)] [K(s,t)-K(s,ρt)]
           =Σ_(s above) δμ(s)K(s,t).

Diagonal predecessors cancel by equivariance. In the last equality K(s,ρt)=0 by no crossing. Reflection pairs outside the true support are retained with zero μ, not discarded asymmetrically. Terms outside the successor square vanish by support; this accounts for every boundary. Since δμ_u is 1/2 at (1,0), zero at the other above states, induction proves δμ_k(s)≥0 above. This is dominance, not equality or pathwise A≥B. The abstract kernel can be defined also at reflected states with a=0, even if they cannot occur from the fixed source; its formulas are valid and normalized there, and such extensions do not change the real law.

For the next target m, the semantic bridge identifies U,V as the literal two new Reach indicators. Exactly U-V=(1-Z)(X-Y), whence in each full-prefix fiber

  g(a,b)=E(U-V|h)=(r-q)/2.

Equivalently C10-C01=A-B with the irrelevant factor gives the same normalized difference. This g is antisymmetric, zero on the diagonal, and nonnegative for a>b since 2^a>2^b. Pairing the finite distribution at k=v-1 gives

  P(Reach to (v,false))-P(Reach to (v,true))
    =Σ_(a>b) δμ_k(a,b)g(a,b) ≥0.

Use this only for u<v, so k≥u and the real initialized count process exists. The source and before-source cases were handled separately above.

Finally the full-outcome split at v is an actual bijection into window and complementary assignments. For v<n the complement has n²-(v+1)² tokens, and every prefix event has exactly the common multiplier 2^(n²-(v+1)²). Prefix agreement plus the membership bridge proves the event really is a prefix event. Multiplying the normalized inequality by the positive total 2^(n²) proves the desired actual event-cardinality inequality ordinarily. No source distribution change, post conditioning, correlated horizontal copies or extra vertical direction bits were introduced.

## Remaining obligations and qualification limits

The corrected ordinary proof has no identified unresolved mathematical step. Every displayed bridge/count identity still requires Lean implementation and checking, including Bool/Finset coercions, the generalized RT induction, assignment bijections, normalized count recurrence, finite reflection sums and exact endpoint. The next milestone should stop after the literal bridge rather than bundle all counting. Full source-extracted strict replay, origin/body/safety/axiom audit, manuscript, independent review and root acceptance remain unpaid; no build or endpoint claim follows from this review.

I read all five production bodies, CHECKPOINT, parent integration, r1 REVIEW and keyed review, r334 CANDIDATE and parent qualification in full. These are internal source/qualification evidence, not a new primary-body or literature audit. No primary manuscript was reopened because the exact approved endpoint was sufficient for this semantic task. Inherited bounded qualification and its unread Przybylowski final EJC journal version remain disclosed; no final-version equivalence, fresh registry check or global novelty clearance is asserted.

## Integrity and process receipts

First command was the exact bootstrap; its original receipt is preserved. frozen-before.json records 424/424 matches before mathematical source reads; frozen-after.json is the required final check. Integrity hashing is not source-body review. Protected active crownr11, expanded-corpus-r342 and all crown bodies were not opened, hashed, globbed or polled by this work; the supplied frozen verifier was used as directed, without exploring its paths. No network, git, install, child, Lean, solver, CAS, mathematical search/enumeration or outside-lane writes occurred.

One read command failed with exit 1 because I initially used r2/BunkbedBase.lean instead of r2/src/BunkbedBase.lean. It read the authorized integration record and then raised FileNotFoundError before reading any production body. The subsequent command used the exact src paths authenticated by that record. This was not a mathematical failure. The failed command did not reach its planned receipt write; its tool-return true exit and applied resource limits are recorded retrospectively in process-exits.json. Early metadata and verifier jobs likewise have tool exit evidence but no retrospective measured CPU/RSS invented. Later unique receipts contain actual self rusage. No receipt represents simultaneous group/cgroup peak; timeout wrapper affinity is not separately attested. All local commands were synchronous and reaped, Python -I -B, externally bounded ≤140 seconds, with ≤2 allowed CPUs, CPU≤120s and AS≤6GiB installed before reads. Metadata helpers used CPU10/AS512MiB/timeout20. No background job remains.

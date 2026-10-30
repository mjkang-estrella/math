# r193: regular triangle maximizers, full-scope question unresolved

## Primary statement and chronology

Actual primary read: Pablo Romero and Louis Petingi, *Trace-minimal graphs maximizing the number of spanning trees*, https://arxiv.org/pdf/2610.36127, v1, Conjecture 10 on p5 and the complete proof of Lemma25/Proposition26 on pp7–8. Definitions and surrounding related-work statements pp1–6, final applications and bibliography pp13–15 inspected. Abs https://arxiv.org/abs/2610.36127 lists only v1, submitted 26 October 2026 18:35:32 UTC. PDF SHA256 3e4d28a0da96775b89a8610e3553d6ad8d61bb7b8e7a9f9417c1411967110875. The PDF says a preliminary version appeared in LAGOS2025, Procedia Computer Science273(2025)177–184, with different title *Construction of infinitely many trace-minimal graphs with maximum number of spanning trees*. That publication body is unread; no journal-version equivalence asserted. The source attributes Conjecture10 to Petingi–Rodríguez, Discrete Math244(2002)351–373, *A new technique for the characterization of graphs with a maximum number of spanning trees*. It cites Gong–Yang–Wang–Chen, Discrete Math349(2026)114936, as proving degrees1–5. Those two bodies and Ábrego et al2006, LAA412:161–221, remain unread. No DOI is authenticated. Author/institutional routes returned404 or certificate failure; no TLS disabling or publisher bypass attempted.

For every finite simple d-regular G0 on n vertices minimizing the number ν of induced three-vertex paths among ALL d-regular graphs on n vertices, and every integer p≥1, G0 disjoint-union p copies of K_(d+1) must be ν-min among all d-regular graphs on n+p(d+1) vertices. Conversely every ν-min G' at that larger order must be isomorphic to H disjoint-union pK_(d+1), for some d-regular H of order n. The converse then forces H to be optimal by additivity. No connectedness, large-order, degree≤5 or trace-minimal restriction is imposed. We retain both directions and all feasible d,n,p; d=0 is trivial. The primary's Proposition26 covers only d≥3,n≥d³, not all source orders.

This is ONE fresh investigated question, zero ordinary resolutions. Saegusa Conjecture23 and the quiver height conjecture are not additional selected slots. No old Bonnet/r186 counting/r191 automorphism question reopened.

## Exact all-order reduction

Let T_d(N) be the maximum number of triangles in a d-regular graph of order N whenever that class is nonempty. Each wedge (two incident edges) is either the unique central wedge of an induced P3 or one of the three wedges of a triangle. Therefore

    ν(G)=N binom(d,2)−3τ(G).

The primary's extracted Remark11 notation is visually ambiguous, but the wedge coefficient is binom(d_i,2), not d_i²; the direct counting above fixes its meaning without changing the extremizers. ν-min and triangle-max are equivalent on regular classes.

The FULL conjecture is equivalent to this universal clique-forcing statement:

    For every d≥0 and every feasible N≥2(d+1), EVERY
    triangle-maximizer in R_d(N) has a K_(d+1) component.  (CF)

Conjecture⇒CF: choose n=N−(d+1). Then n≥d+1, and nd is even because Nd and d(d+1) are even. A simple regular graph on n exists: for even d join each cyclic vertex to offsets±1,...,±d/2; for odd d, n is even, use offsets±1,...,±(d−1)/2 and the opposite perfect matching. Thus one can choose optimal G0 at n and invoke the converse with p=1.

CF⇒conjecture: a triangle maximizer at n+d+1 contains K_(d+1); deleting it leaves an optimizer at n, since any improvement of the remainder improves the original. Hence T_d(n+d+1)=T_d(n)+binom(d+1,3), and EVERY maximizer has the required form. Repeat at n+i(d+1) for i=p,...,1: all orders at which CF is used are≥2(d+1), since the original feasible n≥d+1. This proves both source directions. Isomorphism and all multiplicities are preserved. The reduction is routine, not the missing theorem.

This changes the research task to a structural extremal lemma, rather than falsely replacing the converse by a single example. A plausible universal route is degree-preserving switching that strictly increases triangles whenever a clique-free extremizer has N≥2(d+1). The source supplies such a local-optimality consequence only strong enough for its large-order comparison, not this global switching theorem.

## Why the strongest read proof does not close CF

Read complete closest proof: Lemma25 and Proposition26 in the latest source. The argument uses the quoted Ábrego local bound: in a triangle-maximizer having no clique component, every neighborhood is missing at least two pairs, so ν≥2N. Write N=q(d+1)+r,0≤r≤d. A competitor consists of (q−1) cliques plus a feasible d-regular residual graph H on s=d+1+r vertices. Discarding even the nonnegative residual triangle contribution shows it suffices that

    2N > s binom(d,2).

The source uses N≥d³ as a convenient sufficient bound. Exact residual triangles can improve this but do not uniformly force the desired inequality. For example d=20,N=53,r=11,s=32: take complement Hbar to be K16,16 with five disjoint perfect matchings removed, so Hbar is11-regular and triangle-free; H is20-regular. Inclusion–exclusion on triples gives τ(H)=binom(32,3)−176·30+32·binom(11,2)=1440. H∪K21 has2770 triangles and ν=1760. The local bound ν≥106 for a hypothetical clique-free optimizer is far too weak to exclude it. These numbers are not evidence such an optimizer exists, or that H∪K21 is globally optimal. They isolate the exact insufficiency of the comparison method.

Moreover the local bound requires GLOBAL extremality. Take two K4s, delete01 and45 and add04 and15. This is a connected3-regular graph on8 vertices with four triangles and no K4 component. Its eight neighborhood deficits are four1s and four2s. Thus the tempting assertion that every clique-free regular graph has each local deficit≥2 is false. The graph is not a source counterexample: two disjoint K4s have eight triangles. This is an exact method countermodel only.

The complete applicable classical adaptation has therefore been exposed: wedge counting, clique additivity, deletion induction and the source's neighborhood-gap/competitor argument prove the conditional reduction and large-order range. They do NOT prove CF at all degrees/orders. No complete classical theorem read subsumes the full endpoint. We do not exclude the question by shortness or by use of classical tools. Full missing bridge: prove CF uniformly for all feasible d,N≥2(d+1), or produce an exact extremal clique-free witness with certified global optimality. A graph with many triangles alone does not refute the forward direction or certify the converse.

## Broad reconnaissance and early screening

Read current math.CO/new and cs.DM/new bytes. Three actual-body leads inspected: trace-minimal graphs2610.36127; quiver mutation2610.36179 (introduction, public theorems and concluding computational caveats); withdrawn star-forming2610.03785. The latter's current abs explicitly lists v3/v4/v5 withdrawn, latest27October2026, comments invalid conjectures. Latest PDF404 preserved; its still-visible descriptive abstract was not promoted into an unresolved target. Quiver paper's public decidability/non-semialgebraicity results are not fresh nominations. Height conjecture could be a separate future project, but no investment/slot here. One precise structural question sustained.

Corrected r1912555-record index alone was the inherited base. Refreshed actual original paths, then scanned direct campaign scientific record names with generated trees pruned. Result2564 original path bindings,1245 distinct SHA256 bodies,9 changed/new,0 missing. All inherited aliases retained, including r111–113; identical bytes deduplicated only as a hash-group view with every actual original binding preserved. No frozen history recursively copied as a new original. Exact source/title/author/statement-family screen has zero matches; broad height-bound hits were unrelated and retained. Read changed Guo review/adoption: ordinary proof retained but root excludes it by complete classical adaptation; no variant selected.

Bounded search RSS returned irrelevant200 pages, not useful negative evidence. Exact requests and bytes/hashes retained. Attempted current registry URL was blocked by this lane's inherited-URL safety filter BEFORE network access; no current registry refresh or new head authentication claimed. r191 inherited descriptors and r189 registry history are retained only as provenance, not actual fresh proof-tree coverage. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenges, UWA2014 manuscript403, Crossref/export429 and parked historical intervals were not retried. Missing predecessor bodies and unavailable current public proof registries leave material prior-art HOLD. Present primary labels this conjecture open; current bounded research cannot clear all history or worldwide priority.

## Diagnostic and disposition

checks.py exhaustively generates labeled regular base graphs through order8, mirrors complements, checks wedge identities, records triangle maxima and every optimizer lacking a clique, and compares all available clique-periodicity pairs. Independent edge-mask census through order5 verifies the full distributions against the recursive generator; explicit known labeled counts guard enumeration. The two-K4 method countermodel is checked exactly. These are finite diagnostics, never the universal proof. The initial pruning error and misleading small PASS output are preserved in checks-initial-invalid.*; repaired output supersedes it.

Zero full candidates. No PROOF.md, Lean, paper, credit, public message/upload, browser, git or shared edit. Administrative counts9additional/39total,next40 unchanged. Root alone counts/accepts/stages. Stop at the exact missing universal extremal lemma.

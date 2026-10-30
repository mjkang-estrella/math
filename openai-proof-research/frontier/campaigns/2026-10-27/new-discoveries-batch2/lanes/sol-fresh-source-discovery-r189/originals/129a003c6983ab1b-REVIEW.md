# Arithmetic156 — independent full-correctness review, round 1

Verdict: **PASS for the entire unchanged frozen theorem and author proof.** No necessary correction and no essential uncompleted correctness verification remain. This is a correctness judgment only. It assigns no contribution grade, acceptance, campaign count, or downstream authorization. The parent alone integrates and adopts judgments.

Reviewer provenance: Codex / GPT-6 Astra / high / default service tier. The authoritative 25,957-byte brief was read first and authenticated as SHA256 d48079a5e57ddd69ef44c3018d0a28803f9d6b933b3c12a50ea9f7dc2d8554a9. All operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true; this review checks their interfaces and the author's new deductions, not their truth. No author text was changed or supplemented as a condition of this verdict.

## Exact object and scope

The reviewed FROZEN.md is 1,912 bytes, SHA256 91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c. The reviewed AUTHOR-PROOF.md is 23,878 bytes, SHA256 d9c17da764f4224dd02733a09a84eba9f5c47b6a37481ab68aa9e68d6b042f3e. Both are in the exact admitted fresh-arithmetic-discovery-r156 root. Their bytes and modes are preserved.

For **every** smooth connected complex projective fourfold X and **every** nonempty smooth connected divisor D, set R = sqrt[2](X,D), using the topological stack fundamental group. In particular pi1(R) is pi1(X minus D) modulo the normal closure of the squares of all D-meridians. The entire assertion is that a smooth connected complex projective eightfold Y and a representable morphism f:Y→R exist, with coarse composite g:Y→X, such that:

1. f induces pi1(Y) ≅ pi1(R), up to base-point conjugacy.
2. The smooth general fibre of g is a product of four smooth connected genus-one curves, and has trivial cotangent bundle.
3. g*D = 2E for an effective Cartier divisor E; g is submersive at some point over a general point of every prime divisor of X other than D; f has a submersive local lift to the root chart over a general point of D.
4. If R is special in the fourfold-pair source's differential-line sense, Y is Campana-special.

Y can be taken from the source's four-factor diagonal-quadric construction with sufficiently high base twist and a general coefficient tuple satisfying the extra curve conditions in the author proof. The proof does not assert a uniform degree, index, polarization, canonical choice, simultaneous relative construction, finite or étale manifold uniformization, another root order, another boundary configuration, or another dimension. None of these excluded assertions is needed below. The root curve's finite cover is not a finite cover of R by Y.

## Sources and proof architecture

The complete tree, 13,223 entries and 4,858,136 bytes with SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b, authenticates all 42 canonical blobs in the three specified folders (12 compact, 15 two-step, 15 fourfold-pair). Git blob identities and lengths were checked, and the selected set exhausts exactly these folders. The truncated tree was not used. Authentication is distinct from reading.

Independent semantic reading covers 36 objects: the complete compact manuscript, complete two-step manuscript, their wrappers and supporting text, and the entire operative fourfold-pair main route including its differentials, transfer, quadrics, and branched sections. The alternative inertia wrapper and inertia-inputs were read to establish dependencies. The three compiled PDFs and the three remaining alternative inertia bodies were authenticated only. They are not premises of the main route. Exact private paths and extents are in private/source-reading.json and private/READING.md.

In the fourfold-pair source, prop:eightfold, the quadric construction and lem:fibres-witnesses supply the smooth projective eightfold, connected general fibre, root map, ordinary/root submersion witnesses, and the source group surjection. Proposition prop:transfer supplies specialness under precisely the four geometric hypotheses used here. These paid operations hold for a nonempty open in the independent coefficient space at sufficiently high twist. The compact theorem is a paid source theorem, not a conjecture to audit in this review. The two-step manuscript does not imply a full integral fundamental-group isomorphism and is not used to do so.

The author's additional argument is: restrict to a sufficiently ample curve; use stack Lefschetz on each one-factor surface; recover the integral vanishing cycles from local contraction discs over an aspherical cover; transport their contractions into the four-factor product; and identify the full root kernel using all upstairs meridians. Each step is checked below against the unchanged author proof, sections 2–8. The computations below reconstruct arguments already present there; they are not replacement lemmas inserted into an incomplete proof.

## 1. The same coefficient space and simultaneous genericity

Fix a sufficiently ample smooth complete-intersection curve C in X, transverse to D. A nonempty effective divisor has D.C > 0; adjunction allows genus(C) ≥ 2. Put m = # (C∩D), with reduced intersections. The curve is fixed before raising the twist M. The two kinds of coefficient sections are H0(X,M) and H0(X,M(-D)), exactly as in the source. Each of the four factors has its own two rows and four columns; no new restriction changes this parameter space.

For M sufficiently high, restriction onto C is surjective for both bundles, by vanishing of H1 of their twists by I_C. On C, a line bundle L of degree > 2g(C)-2+2 has H1(L(-Z)) = 0 for every length-at-most-two subscheme Z. Thus values and first jets used in the author's incidences can be prescribed. The finite list of such requirements and the source's global-generation bounds can all be met by one sufficiently high power. Local trivializations, including those of the nonvanishing D-section away from D, give the asserted freedom of matrix entries. At C∩D the root-chart trivialization is used; there is no demand that a coarse transverse parameter have a nonzero derivative after the squaring map.

At a fixed ordinary point, a zero column has codimension two. Two pair-minor vanishings have codimension at least two: if they share a column, that column being zero already has codimension two, and otherwise each of two other columns is constrained to its line. For disjoint pairs the two conditions are independent. Off zero columns, a given determinant's zero locus is smooth in the relevant entries; its derivative vanishing is a further independent first-jet condition. The prohibited events over the moving one-dimensional C therefore have proper images in the parameter space. Two factors having discriminant zero at the same point is again codimension two, by their independent coefficients. The same argument treats coincident first-row zeros; value and first-jet separation treats a multiple first-row zero. At the finitely many marked points, nonvanishing of all pair minors and first-row entries is a finite collection of nonempty open conditions.

Consequently the no-zero-column, no-double-minor, simple-minor, mutually disjoint discriminant, and simple/disjoint first-row conditions hold together on a nonempty open subset. Properness of C makes the incidence exclusions closed. The independent coefficient space is irreducible. Its curve open therefore meets the source's nonempty global open. This proves simultaneous genericity for every X,D in the frozen scope, including all the source's global witnesses. It is not an assumption that arbitrary source-generic coefficients automatically satisfy the extra conditions.

## 2. The one-factor surface, the first quadric, and root inertia

Over R_C = sqrt[2](C,C∩D), use V = O ⊕ O ⊕ T ⊕ T with T² = O(D)|R_C. The one-factor surface S_j is the intersection of the two sections of O(2) tensor M in P(V). A single first-row coefficient may vanish, but it vanishes simply and the other three do not vanish there. The only possible vertical singular point of that quadric is the corresponding coordinate point; its base derivative is nonzero. Thus the total first quadric Q_j is smooth. At a marked point every first-row entry is nonzero, so its fibre is smooth; passage to a root chart preserves this conclusion.

Away from the discriminant the two quadrics give a smooth genus-one curve. A rank failure with only one dependent pair gives exactly the local model below, whose total space is smooth. All pair minors are nonzero at the marked points. Thus S_j is smooth as a stack. The nontrivial root inertia acts by [z1:z2:z3:z4] ↦ [z1:z2:-z3:-z4], whose fixed loci are precisely the two coordinate projective lines. The complete intersection misses these lines because the (1,2) and (3,4) minors are nonzero. Hence S_j has trivial stabilizers and is an ordinary smooth compact surface. The source's finite square-coordinate construction applies to this one-factor restriction and supplies projectivity; the fibre curves are connected. No claim is made that the ambient P(V) or Q_j has trivial stabilizers. The stack Lefschetz theorem is applied to them as stacks.

## 3. The I2 fibre and the primitive integral relation

At a simple zero of one pair minor, row operations and relabeling put the equations in the form

    q1 = a z1² + b z2² + c z3² + d z4²,
    q2 = e z3² + f z4²,

with a,b,e,f nonzero. The other pair minors being nonzero also gives d-cf/e ≠ 0. The two planes z3 = ±sqrt(-f/e) z4 cut q1 in two smooth conics. They meet at exactly the two points z3=z4=0, a z1²+b z2²=0. Both z1 and z2 are nonzero at each point. The simple determinant zero gives a nonzero base derivative of the missing equation at both points. The surface map therefore has, in disjoint neighbourhoods, the two standard smoothing models xy=t. The fibre is reduced, and there are no other singularities by the determinant classification.

The two waist circles in a nearby elliptic curve are disjoint, parallel, nonseparating simple circles. Equivalently, normalizing the two conics gives two rational components joined at two nodes, whose dual graph is a cycle; cutting the nearby torus along both waist circles gives the two annular pieces. Either waist circle is a primitive element δ of H1(E,Z)=pi1(E)=Z². The two circles represent ±δ. A local vanishing disc has that circle as its actual boundary, once, and filling the singular disc kills δ. Thus the local total space has pi1 Z²/Zδ = Z.

This is stronger than the monodromy relation. The two positive local twists give T_δ², for which (T_δ²-I)Z² = 2Zδ. A monodromy-only quotient would leave unwanted two-torsion. The author uses the contraction discs, not that quotient; the integral primitive relation in section 3 is correct.

The actual ABKP local Morse and van Kampen discussion and Lemma 3.2 support these operations. Its global topological-Lefschetz-fibration conventions include distinct critical values and, in its sphere construction, section data. They are not imported wholesale here: the author's two disjoint Morse neighbourhoods handle the two nodes at one value, and the argument below stays over discs. Shimada's Corollary 1.1 has irreducibility and weak-section hypotheses that are not met by these I2 fibres. It is correctly excluded as a premise; Example 3.5 explicitly warns against substituting monodromy for contraction relations.

## 4. The finite orbicurve cover and positivity

Write the orbicurve group with handle generators a_i,b_i and meridians γ_l, with γ_l²=1 and product of commutators times product of meridians equal to 1. If m is even, sending every γ_l to the nontrivial element of C2 and every handle to 1 gives a surjective map injective on each local stabilizer. If m is odd, take

    a=(34), b=(13)(24), c=(12)(34).

Here a,b are involutions, ab has order four, and [a,b]=(ab)²=c; they generate a group of order eight. Send the first handle pair to a,b, all other handles to 1, and every γ_l to c. The relation holds because c^(m+1)=1. Again each local stabilizer injects. The connected regular cover of the punctured curve fills with w↦w² at every marked point. It is therefore a connected smooth curve C' with a finite representable étale Galois map to R_C, of degree N=2 or 8. Riemann–Hurwitz gives

    g(C') = 1 + N(g(C)-1) + Nm/4 ≥ 2.

This supplies a disc universal cover of C'. It makes no assertion that the four-dimensional stack R is developable or that its local inertia injects into its global group.

On P(V)|C', a Hermitian metric for relative O(2) is positive on vertical tangent vectors. Its other curvature terms are bounded on the compact total space. A positive metric on the pulled-back ample base line, raised to a sufficiently high power, makes the full curvature positive by the Schur-complement estimate. The phrase 'a positive metric on the pullback' is legitimate: one chooses a positive metric on that positive-degree line over C', rather than relying on the potentially degenerate literal pullback of a coarse-base metric at a branch point. Averaging logarithms of metrics under the finite deck group preserves curvature positivity and gives a metric descending to the stack. Restriction to Q_j stays positive.

Halpern-Leistner 1008.0891v1 was read in full, including the proof and stack Morse construction. Theorem 2.5 and Corollary 2.7 apply to a smooth Deligne–Mumford stack with compact coarse space and the indicated positive Hermitian line. Their conclusion is an isomorphism on pi_i for i < k-1 when curvature has the requisite k positive directions. No global manifold uniformization of the ambient fourfold is required. Here the projective bundle stack has complex dimension four, and the smooth Q_j has dimension three. Full positivity gives k=4 and k=3, respectively, so both restrictions induce pi1 isomorphisms. The divisors are the actual smooth zero loci already checked, and the stacks are proper, smooth, and Deligne–Mumford.

The P3-bundle projection induces pi1(P(V)|R_C) ≅ pi1(R_C), since P3 is simply connected (the fibre-sequence statement is in the stack topology). The two Lefschetz inclusions therefore give the **natural** isomorphism pi1(S_j)→pi1(R_C), not just an abstract group identification. Covering correspondence then gives connected S'_j=S_j×R_C C' and the natural pi1(S'_j) ≅ pi1(C'). The subsequent pullback W_j to the universal disc B is connected and simply connected. All these covers are topological covers of the appropriate stack or manifold; coarse ramification is not confused with stack ramification.

## 5. Disc van Kampen and the direct limit

The critical values in B form a locally finite discrete set. Take a compact disc K with regular boundary, containing the fixed regular base point and finitely many critical values. Delete disjoint small critical discs and choose leashes from the base point. The punctured base retracts onto a graph. Its pi2 vanishes, so the smooth-bundle exact sequence injects Z²=pi1(E) and has free quotient. Choosing lifts of the free generators splits it. The lifts can be chosen using nonsingular local sections near the critical fibres and the leashes; this makes them precisely the lassos killed on filling. This requires no global section of the elliptic fibration.

For each critical disc, the local computation of section 3 kills its lifted lasso and the transported primitive δ_v. The remaining monodromy differences are multiples of 2δ_v and already vanish. There is no sphere-cap relation: K is a disc, and the free lasso generators have no relation before filling. Seifert–van Kampen consequently gives, via the natural based fibre inclusion,

    pi1(W_j|K) = Z² / <δ_v : v critical in K>.

An exhaustion of B by such discs computes pi1(W_j) as the direct limit. Loops and homotopies have compact images, whose projections lie in one larger disc, so the assertion does not presuppose a finite global discriminant upstairs. Since W_j is simply connected, the transported cycles over all values generate Z² integrally. A finite subcollection generates it, since each of the two standard basis vectors is a finite integer combination. This step avoids the pi2-of-the-base obstruction seen in sphere examples and uses the actual aspherical curve cover.

## 6. Transport into the four-factor product

Let P=S_1×R_C S_2×R_C S_3×R_C S_4 and P'=P×R_C C'. Disjoint discriminants mean at most one surface map has a critical point above any base value. Base-changing that smooth total surface by the other three submersions keeps the product smooth. At marked points all maps are smooth in the root chart and the diagonal inertia is free. Properness and connected fibres over a connected base give connectedness. These are smooth five-dimensional total spaces over the curve, with four-dimensional regular fibre F=E_1×E_2×E_3×E_4.

For each finite collection of j-th vanishing cycles supplied above, take its paths in B. On any compact path neighbourhood there are only finitely many other-factor critical values. Detour around them without crossing a j-th critical value. Those other values are regular for the j-th surface, so this changes none of its transported cycles up to the based identifications being used. A thin contractible neighbourhood of a detoured embedded leash and its endpoint disc has all other three fibrations smooth. Smooth local triviality gives sections there with any prescribed initial fibre points. Multiplying the j-th contraction disc, including its transport strip, by these sections gives an actual disc in the four-factor pullback over B. Its boundary moves only in the j-th fibre coordinate. Projection to P' gives the desired null-homotopy even if the projected path in C' is not embedded.

Thus every transported δ_v dies in pi1(P'), and their integral generation kills the whole Z² of each factor. The direct product pi1(F)=Z^8 is generated by the four factors, so its entire map to pi1(P') is zero. No section over all of C', no holomorphic section, and no injectivity assumption on the fibre group in P' is used.

The source's smooth global zero locus has a unique dominating component: its general fibre is the connected product of four smooth genus-one curves. Components of a smooth variety are disjoint. The connected restriction P contains this general fibre at a point of C in the common smooth open, so the entire P lies in the dominating component Y. This identifies the discs with discs in the source eightfold of the frozen statement. Hence pi1(F)→pi1(Y) is zero. This is not a replacement eightfold or a construction only over the chosen curve.

## 7. Exactness and every upstairs divisor

Choose a nonempty Zariski open U⊂X minus D over which g is smooth proper with connected fibre F. Let Gamma=pi1(g^-1(U)), K=im(pi1(F)→Gamma), and N=ker(Gamma→pi1(Y)). Smooth proper local triviality gives Gamma/K=pi1(U), with K normal, without requiring a section or pi2(U)=0. General position in the smooth Y makes Gamma→pi1(Y) surjective, and N is normally generated by meridians of **all** divisorial components of Y minus g^-1(U). Components of higher codimension add no generators. In particular upstairs divisors whose images have codimension at least two, and exceptional divisors, remain included. It follows algebraically that

    pi1(Y) / im pi1(F) = pi1(U) / im N.

The global map f:Y→R shows that im N lies in the kernel J of pi1(U)→pi1(R). This inclusion requires no claim about where a particular exceptional divisor maps and no enumeration of exceptional multiplicities.

Conversely J is normally generated by the ordinary meridians of the removed base prime divisors other than D, and the squares of D-meridians. One first fills the ordinary divisors in X minus D, and then imposes the root relations. Codimension-two loci can be avoided by loops and discs in the smooth charts, and introduce no additional kernel generators; the same statement in a root chart is compatible with its finite stabilizer quotient. This is exactly the root-stack convention in FROZEN.md, with all conjugates retained.

At a general point of each ordinary removed prime, the source provides a submersive point in Y. A local analytic section through that point lifts a transverse base disc. Its boundary is an upstairs meridian and maps to the base meridian once. At a general point of D, the submersive root-chart lift supplies a local section in the parameter u with x=u². Its boundary is again a meridian upstairs and maps to γ_D². The chart neighbourhood maps to Y, so the lifted disc genuinely fills there. Normal generation and base-point conjugation now give J⊂im N, hence equality. This proves the full exact sequence

    pi1(F) → pi1(Y) → pi1(R) → 1.

Combining it with the zero fibre map proves the natural isomorphism in item (1). The argument does not replace the topological stack group by its rational completion, a linear image, the group of X, or a possibly incorrect coarse orbifold group. It does not assume inertia has order exactly two in the global fundamental group; relations may make it smaller.

## 8. The three other numbered assertions

The enlarged coefficient choice stays in the source open. Its smooth general fibre is therefore the actual product of four connected genus-one curves, so the cotangent is trivial, proving (2). The pullback tautological root line and section give the effective Cartier E and g*D=2E. The source's deleted-column rank conditions and lem:fibres-witnesses give ordinary submersion points over general points of every other prime, and a submersive lift in the root chart over general D. These statements apply to the dominating component Y, since the witnessed neighbourhood meets the connected general fibres. Thus (3) is retained for this Y, not merely for some other source-generic model.

For (4), prop:transfer requires exactly the even divisor pullback, smooth connected general fibre with trivial cotangent, ordinary witnesses at every other prime, and the root-chart witness. They have all been verified. The source's saturation and local-section argument is in the specified differential-line convention and yields Campana-specialness of Y when R is special. No different orbifold multiplicity convention or unproved specialness of fibres of another map is substituted. The specialness assumption is used only for item (4); none is inserted into (1)–(3).

## Review obligations and limits

Parent correctness checks 1–11 are discharged by sections 1–8 above. Parent check 12 concerns contribution and is deliberately not graded. UNRESOLVED.md names review interfaces, not additional theorem hypotheses; the ones material to correctness are all discharged here. There are no unresolved mathematical obligations within the frozen scope and no requested repair. The present reconstruction verifies what the unchanged proof already establishes.

Actual primary-reading limits remain explicit. Halpern-Leistner was read completely; ABKP section 2 and its Lemma 3.2 region, Shimada's relevant hypotheses and examples, the complete Sommese–Van de Ven text, and the specified Campana regions were read directly. The inaccessible Matsumura PDF is unused. Neither unread portions nor access failures support the verdict. Campana's orbifold exactness is a comparison: the author establishes the needed kernel directly with the paid witnesses. Sommese is not substituted for the stack theorem. Original history reading was confined to the four selected r12/r17 original intervals, not the author's entire history corpus. It does not license any novelty or exhaustive-history claim. Exact extents, late reading, output-recovery events, and prospective isolation limits are recorded privately.

All protected source, primary, original-history copies and named metadata remain local under private/. Only this exclusive review root was written. No other review, live peer, adoption/status/activity record, or forbidden completed-round body was consulted. No author or shared files were edited; no staging, commit, publication, upload, contact, browser UI, nested agent, or downstream work was performed. The selected packet and its controls establish artifact consistency only; they do not supply mathematical premises or a contribution grade.

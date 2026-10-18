# 245: conversion and annotation boundaries

Prefreeze exploratory screen, no theorem selected or proved beyond the elementary counterexample below. Actual source introduction was read completely. It specifies full annotated syntax, open contexts, arbitrary nonfunctional sort relations, beta conversion in typing, and system-wide weak/strong beta normalization. metatheory.tex lines183–280 were read: its confluence/product-compatibility proof works on raw annotated expressions for beta and is used to preserve exact expected types.

A beta-eta extension must distinguish (1) adding eta reduction to terms typable under beta conversion, and (2) replacing the typing conversion rule itself by beta-eta conversion. The latter can admit additional typed expressions. The source explicitly disclaims an eta assertion. No proof of either full extension is claimed here.

An actual primary obstruction to simply reusing the source's raw-confluence argument is Geuvers's Domain Lemma4.4.16. For distinct normal annotations A and B, and fresh y, the raw expression

    lambda y:B. (lambda x:A.x) y

beta-reduces to lambda y:B.y, while eta-reducing the outer abstraction gives lambda x:A.x. Those outputs are distinct annotated beta-eta normal forms if A,B are distinct literal sorts. The two reductions need not both be legal in the same typed context. Thus this refutes raw confluence, not typed confluence or the beta-eta normalization conjecture. The source's raw confluence lemma cannot be copied with beta replaced by beta-eta.

Actual Geuvers1993 thesis primary extraction: lines3700–3795 (Domain Lemma4.4.16 with full diagram proof, Corollary4.4.17, Key Lemma4.4.18 and proof), and6770–6840 (discussion including Conjectures8.1.2–8.1.4) were read. Greek letters extract imperfectly; the labels and surrounding text distinguish beta from eta, and no machine-parsed formula claim is made. The primary explicitly says the conversion extension introduces more typable terms. The source's profile/observation proof would require new typed confluence/subject-reduction/normal-type interfaces for that extension; none were constructed.

The broader informal idea 'add arbitrary computation rules and keep WN implies SN' is false even over simply typed lambda calculus with a base type o, constants a:o and f:o->o. Add rules f(t)->a and f(t)->f(f(t)). Every well-typed term weakly normalizes: first beta-normalize treating a,f as constants, then erase every f-application by the first rule; no new beta-redex appears, and any remaining bare f is normal. But f(a)->f(f(a))->f(f(f(a)))->... is an infinite well-typed reduction. Type expressions in this simple fragment have no reductions. This is a counterexample to the unrestricted extension only, not a PTS counterexample and not an eta counterexample.

No generic normalization theorem was silently narrowed after freeze; there was no freeze. The finite specification reduction and source nonfunctional profile mechanism are not offered as new results. Geuvers's separate1992 CR article was retrieved but not semantically read; no theorem from it is used. The full source observation and guarded diagonal proofs were retrieved but not read. No novelty claim.

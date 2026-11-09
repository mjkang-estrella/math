# Frozen theorem S183N — nonmeager hereditary path selection

Frozen after notes/01-prefreeze.md and before author-proof development. Source323 and all operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. This statement is a nominee for independent review; it assigns no grade or count.

Work in ZFC. Write non(M) for the least cardinality of a nonmeager subset of Baire space omega^omega with its product topology, and assume non(M)=aleph1.

Fix any admissible choices in the real coordinate-space construction of Source323, Sections “The norming construction”, “Infinite paths and weak-Cauchy block sequences”, and “Vectors detected at a prescribed weight”, at the specified pin. Let E=X0* be its resulting real Banach space, X0 the norm-closed span of its coordinate functionals in E*, and P_t the set of actual infinite paths of family t, including their declared weights and integer metadata; t ranges over the pure families k∈omega and the mixed family *. All norms, coordinate colors, allowed crops, coding rules, and completions here are exactly those of that source construction.

Then there are subsets A_t⊂P_t, chosen simultaneously and independently of any subspace F, with |union_t A_t|=aleph1, such that:

1. For every infinite-dimensional closed real subspace F⊂E, there are a family t, a real number d_F>0, and pairwise distinct paths P_alpha∈A_t (alpha<omega1) for which
   ||P_alpha|F-P_beta|F||>d_F whenever alpha≠beta.

2. Put W=E*/X0 and let Q:E*→W be the norm quotient. There is a bounded real-linear operator B:E*→W with ||B||≤1/10, B*(W*)⊂J_E(E), and
   closure B(X0)=closure span{QP:P∈A_t, t∈omega∪{*}}=:V_A,
   B(E*)⊂V_A.
   The closed subspace X=ker(Q-B), with its inherited norm, satisfies:
   restriction E→X* is an isomorphism;
   closure B(X)=V_A;
   dens(X)=dens(X*)=aleph1;
   X has no separable infinite-dimensional real Banach quotient.

3. For the complexification X_C=X+iX with norm
   ||x+iy||_C=sup_{theta∈R}||cos(theta)x-sin(theta)y||_X,
   dens(X_C)=dens(X_C*)=aleph1, and X_C has no separable infinite-dimensional complex Banach quotient.

Here every closure is a norm closure, dens is norm density, and a Banach quotient means the quotient by a closed linear subspace with its quotient norm, equivalently the range of a bounded surjective linear map onto a Banach space. The assertion excludes infinite-dimensional separable quotients; it makes no assertion excluding one-dimensional functional quotients. There is no uniform lower bound d_F across all F. All constructions and quantifiers are internal to the same set-theoretic universe; no ground-model preservation statement or ZFC self-consistency assertion is part of the theorem.

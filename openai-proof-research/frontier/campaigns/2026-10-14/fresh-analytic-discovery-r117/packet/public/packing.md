# Reserve-ball feasibility and its exact limits

These are prefreeze calculations, not a proposed research theorem. The finite packing input is source343 `intro:main`, with neighborhood embeddings of closed balls into an open target. Capacities are a, with volume a^n/n!, and n>=3. The pinned raw paths and exact Git blobs are in `source-register.json`.

Consider positive capacities a_i, i>=1, with S=sum a_i^n<R^n and a_i+a_j<R for distinct indices. Let t_N=sum_{i>N}a_i^n. Since a_i tends to zero, M=max_i a_i exists and M<R. Choose N so large that b=2 t_N^(1/n) obeys

    S+(2^n−1)t_N < R^n,
    b < R−M,
    b < R/2.

The finite list a_1,...,a_N,b has strict volume and pair constraints. Apply the stipulated finite theorem. Reserve the image of B(b), leaving the first N ball maps fixed. The remaining tail has volume parameter t_N=b^n/2^n, and each of its capacities is strictly less than b/2 because the tail has infinitely many positive terms. Thus every pair in the tail has sum less than b.

Inside the standard source B(b), choose a longer finite prefix and the next reserve b'=2 t_{N'}^(1/n). As N' grows, require b'<b/2 and

    sum_{N<i<=N'} a_i^n + (b')^n
       = t_N + (2^n−1)t_{N'} < b^n.

Choose at least one new index. All finite prefix pairs satisfy the b bound, and a new-prefix capacity plus b' is less than b. The finite theorem packs this batch and reserve into Int B(b). Compose with the previous reserve embedding. Continue with N_j strictly increasing. Each N_j is finite and their increasing integer sequence tends to infinity, so every requested ball is assigned once.

Every component map is defined on a neighborhood at its finite assignment stage. It is never changed afterward. Its compact image has positive separation from the finite collection of other images at that stage, including the next reserve. Every later image lies inside that reserve. Earlier images are also finitely many and disjoint. Consequently each component has an ambient neighborhood meeting no other component. Restrict its source neighborhood if necessary; the resulting union map is a symplectic embedding of the disjoint union of the closed balls, with componentwise neighborhood extensions. This uses no convergence of symplectomorphisms, no uniform derivative bound and no assertion that reserve-image diameters shrink.

The construction exactly composes the finite theorem with classical nested containers. Structural r76 `checkpoint.md` line33 already identifies this strict-volume reserve-ball induction. That antecedent was found after the displayed algebra was derived and before any freeze. This packet neither claims new priority for the calculation nor nominates it.

At total equality S=R^n the first finite load would instead be R^n+(2^n−1)t_N>R^n. That proves only that this reserve choice cannot start at equality. It does not refute countable exact-volume packing, and no equality target was frozen. The strict-slack result is not offered as a substitute.

A prescribed arbitrary prefix is a separate problem. Source343 `geo:relative-moser` starts with cohomologous Kähler forms for one complex structure and preserves the specified complex submanifolds as sets. Its `app:large` construction reserves a standard central large ball, uses two normal models and retains a closed connection-period term during the lifted coordinate change. These are stronger than merely an absolute existence headline, but they do not identify an arbitrary prescribed symplectic prefix with that model.

The primary [Siegel–Yao, 2312.13224v1](https://arxiv.org/pdf/2312.13224v1), Proposition2.4 and its proof, first shrinks the ball radius to make an interpolated form nondegenerate, then uses relative Poincaré/Moser. It is not a fixed-capacity arbitrary-prefix isotopy theorem. Section7 Lemma7.1 controls an index/energy obstruction; it is not a compatible selection of packings. Its stabilized surface-product result also has a different source and target. These are actual proof contracts, not conclusions inferred from the abstract.

The inspected I74 body already constructs fixed-capacity transport for specified shear/derivative-controlled classes, a protected toric comparison model, and fixed-slack finite-bin packing in an arbitrary open complement. Its threshold depends on the slack and actual geometry. Those operations do not supply a positive threshold uniform as slack tends to zero or a positive same-class path for every prescribed prefix. No new arbitrary-prefix construction is claimed here.

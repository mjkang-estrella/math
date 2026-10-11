# I194 — quotient sign conjecture

Status: COMPLETE written assignment, PARTIAL mathematical resolution. **Original-target verdict: UNRESOLVED at J194 below.** This is an unsealed proof-only record, written early with explicit PARTIAL status and updated incrementally. No substantial finding is nominated. No decisive new constraint in the brief's stopping-rule sense, and no verified negative instance, was obtained; this final focused attempt stops here for parent-side parking of the short-gap front. E183 remains parked.

The full proofs and gaps are in [analytic-attempt.md](../experiments/i194_quotient_sign/analytic-attempt.md). [reading-and-failures.md](../experiments/i194_quotient_sign/reading-and-failures.md) preserves unsuccessful routes and reading limits; [input-authentication.json](../experiments/i194_quotient_sign/input-authentication.json) records detached input hashes; [literature.md](../sources/i194_quotient_sign/literature.md) gives source and contribution boundaries.

## 1. Authentication and exact sign question

Before proof work, all six required detached SHA-256 anchors matched:

- I193: `e1402e6ec2561f35f3b6d0b5c67361afdb907652b5815134fb2215b6bcb59cb5`.
- I192: `ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d`.
- I168: `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31`.
- I169: `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf`.
- I170: `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096`.
- Manuscript: `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.

The brief, the five finalized parent dispositions, I191's parking disposition, I192/I193 analytic attempts, AGENTS.md, upstream metadata and relevant catalogue are also hashed. The five required reports and two analytic attempts were read in full before new deductions. Actual manuscript ranges read are 60–260, 362–718 and 794–837. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

Use the exact B-admissible domain of I168–I193: finite simple cubic bipartite planar 3-vertex-connected G,H; deletion e=uv,f=xy in facial order u,v,...,y,x,...; insertion of arms up,vq,xr,ys and square pq,qs,sr,rp. Brace steps are the restriction in which both graphs have the two-edge matching-extension property. All vector spaces are rational and all Hamiltonian/path/cover families are complete.

For short arc a=ux, let S=N10∪N01∪N11, L=diff(S), V=diff(N00), Z=diff(Pvy), W'=L+V+Z=L+U; let ell=d(G)−dim L and t=dim W'−dim L. With C0∈S,N∈N00,Q∈Pvy set r=N−C0 and z=F_Q−C0, where F_Q=Q−a+e+f is the actual two-component spanning two-factor. In the equality case t=ell−1,

    D_G=W'+<r>, r∉W', b=r+2z modulo W'.

The normalized w on D_G has kernel W' and w(r)=1. If z∉D_G, exchange already holds and w(z) is not intrinsically defined. Otherwise lambda=w(z) is independent of Q,N,C0; its affine values are 0 on S and 1 on N00, and exchange fails exactly when lambda=−1/2. The sign target is lambda≥0, not merely that one-value exclusion.

## 2. What the written investigation settles

**Exact flip connectivity.** For a simple C-alternating cycle R, remove its q C-edges from Hamiltonian C. The resulting q paths induce an endpoint matching tau; the q added edges induce beta. Suppressing those paths preserves components, so the flipped factor's component count is exactly the number of components of the 2-regular multigraph tau∪beta. A flip fails exactly when this number exceeds one. For q=2 failure is beta=tau and produces two components. This is a criterion, not guaranteed connectivity.

**A conditional fractional block extension.** In a cubic graph F△C splits into vertex-disjoint alternating cycles with increments vi. Put T_I=C+Σ_(i∈I)vi. If C∈S and nonnegative rational coefficients theta_I on Hamiltonian T_I satisfy Σ_(I containing i)theta_I=1 for every i, then

    lambda=Σ_I theta_I h(T_I)≥0.

The proof sums incidence vectors before applying w, so no undefined individual flip weight is used. The singleton condition is I193's subcase. Another settled subcase has k≥3 and every (k−1)-cycle block Hamiltonian: take all coefficients 1/(k−1). A disjoint-block certificate makes lambda integral. A sequence with Hamiltonian proper prefixes alone leaves the final disconnected jump unpaid; its earlier increments telescope, but need not each be nonnegative.

**The route fails universally even for a brace step.** The fully specified cube rail-deletion step has child C6□K2, both braces by an explicit matching-extension proof. Its complete six Hamiltonian cycles give ell=1,t=0, and its canonical F is the two layer squares. The written identity

    2(rho0+rho1−t0−b0)=C0−C1−C2−C3+X+Y

gives lambda=1/2. For EVERY surviving C, F△C is just one alternating cycle; flipping it gives disconnected F. There is no successful nonempty block and no flip order to choose. This refutes universality of those certificates, not the sign conjecture. The paid even-prism formula lambda=1/(m−2)>0 is re-derived in writing; its fractional values exclude all integral Hamiltonian-difference certificates, even signed ones. These limitations are consequences within already-paid examples, not a decisive new sign constraint.

**Three-matching decomposition.** Split F=M1∪M2 and let M0 be its complement. Then F+F01+F02=2E, where F0i=M0∪Mi. When the terms belong to the Hamiltonian affine hull,

    lambda=kappa−h(F01)−h(F02), kappa=w(2E−3C0).

If both unions are Hamiltonian, their affine values sum to 0 when e,f have opposite matching colors, and to 1 when they have the same color. Thus the missing bound is respectively kappa≥0 or kappa≥1, not supplied by matching extension. Both color phases cannot simultaneously have two Hamiltonian unions: their identical vector sums would have different w-values. This small compatibility fact neither guarantees a successful phase nor bounds kappa; it is not the decisive structural dichotomy sought by the stopping rule.

The actual manuscript operations supply existence with local prescriptions and positivity of specially chosen spoke weights. They do not supply a weight-preserving reconnection of this F or a sign for this w. Exact convex representation of disconnected F by Hamiltonian cycles is impossible by support containment; quotient-cone representation remains unpaid. Integer span and odd primitive lattice value exclude −1/2 but do not exclude negative values. The inherited pairing symmetry gives the same lambda; the central transport lambda/(1+2lambda) propagates known nonnegativity but permits formal negative inputs without a dimension contradiction.

## 3. One remaining assertion, verdict, and stopping rule

> **J194 (unpaid):** For every B-admissible short-gap step with the actual complete families above, if t=ell−1 and z=F_Q−C0∈D_G, the unique normalized functional w on D_G/W', with w(N−C0)=1, satisfies w(z)≥0. Use the symmetric terminal notation when vy is the short arc.

This assertion, including its brace restriction, is **UNRESOLVED**. No fully specified negative-value step has been obtained. The cube is a positive instance illustrating a failed method. Formal negative coefficients are not graph counterexamples. A proof of J194 would imply J193 and short-gap exchange; a negative lambda refutes the sign conjecture, but refutes exchange at that step only when lambda=−1/2.

The conditional subcases and method obstructions do not give a decisive new constraint on the remaining actual coefficients. Per the brief, stop and leave parking/integration decisions to the parent; do not propose another short-gap iteration. E183 and its named dependencies were not reopened. **Even proving the sign conjecture leaves the long-gap clauses of J192, universal exchange and Q164 open.** Neither the numerical Q164 count bound nor the stronger affine-fullness target or (T) is established here.

## 4. Source, contribution, and activity limits

Newly written here are the endpoint-matching flip criterion, the conditional fractional block proof, the direct cube obstruction with brace verification, and exact three-matching bookkeeping. They are elementary deductions at their explicit scopes; no new-to-literature theorem or substantial finding is claimed. Family 180 has one catalogue entry; no external companion theorem or external search result is used. The inherited computational claims remain finite historical evidence, not freshly verified computations.

Exactly the five assigned files were written, incrementally. Validation consists only of written coordinate comparisons, matching constructions, connectivity arguments and linear algebra against read source statements. No research code, graph/state/matching scan, test, experiment, historical replay/rebuild, source copy, snapshot, seal, further agent, ancestor/shared-ledger edit, staging, commit, task archive, publication or parent dispatch/integration bookkeeping was performed. Detached final hashes are returned outside these files, with no self-hash or seal.

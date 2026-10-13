# I341 — adaptive secret-key obstruction for PPT-composite channels

2026-10-13. Parent proposal, **unaccepted and not independently reviewed**. The pinned OpenAI/math corpus at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true. This proposes one connected result, not separate counts for a closure lemma, capacity consequence and explicit example.

## Exact claim and model

Call a finite-dimensional completely positive map PPT if its output-transpose composition is CP; equivalently its input-transpose composition is CP. No trace condition is included. Let C denote the source's represented class: normalized bipartite states

    omega=(L tensor M)(|chi><chi|),

where L and M are PPT maps of arbitrary finite input and output dimensions, and chi need not be normalized. The maps in this representation are mathematical factors, not physical operations.

**Proposed theorem.** Fix any collection of finite-dimensional channels Phi=Q composed with P, where P and Q are PPT and the composite Phi is trace preserving. The factors themselves need not be trace preserving. Starting with any finite-dimensional C state, perform any finite adaptive protocol consisting of local quantum instruments, public classical communication, and uses of these channels to send quantum subsystems in either direction. Instruments have finitely many public outcomes; their choice and channel choice may depend on the public history. Local memories may have any finite dimension, with no uniform bound over protocols. Eve purifies the initial state, receives all channel environments, and retains the complete public history. Local parties may keep all private dilation systems. Then:

1. At every public history of positive probability, the parties' joint state, including their private memories, belongs to C.
2. Any final nonempty fixed-length classical key is at unhalved trace-norm distance at least 1/10 from every ideal uniform identical key independent of Eve and public history. If the comparison has the actual public-history marginal, the bound improves to 1/5.
3. In particular the two-way public-communication assisted secret-key capacity of each such channel is zero. The same obstruction holds when a protocol adaptively switches among these channels, and for trace-norm limits of finite protocols on a fixed finite output space. No claim about arbitrary infinite-memory or nonapproximable infinite protocols is needed.

Separable initial states are included. This does not grant arbitrary zero-key resources, arbitrary PPT channels, or access between P and Q. It concerns their inaccessible serial composite. In particular the explicit source channel Theta on dimension 21 has a square Phi=Theta composed with Theta that is not entanglement breaking but, under this theorem, has zero two-way secret-key capacity. Nothing here asserts that Theta itself has zero two-way capacity.

## Stipulated source interfaces actually read

In `preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/sections/`:

- `foundations.tex`, complete: `lem:ppt-stability`, `def:represented-class`, `lem:tensor-closure`, `lem:choi-transfer`, including arbitrary rectangular maps and unnormalized chi.
- `secret-key.tex`, lines 1–140: `def:distillable-key` and complete statement of `thm:zero-key`. For each C state, every admitted local key protocol, any initial purification and every normalized Eve comparison, its bit output has unhalved trace-norm gap at least 1/5.
- `applications.tex`, complete: `prop:channel-completion` and the dimension-21 square's non-entanglement-breaking conclusion.

The new step is closure under sending a quantum subsystem through a PPT composite. Local CP closure and the Choi-state conclusion alone do not prove this adaptive claim.

## 1. Local closure and separable initial states

Arbitrary local CP postcomposition preserves a PPT representing map by `lem:ppt-stability`. On a branch of probability p>0, divide chi by sqrt(p) to normalize the represented output. Appending local pure ancillas is a CP postcomposition. A general local instrument can be dilated, retaining its private environment and conditioning only on its public outcome. Each conditioned map into the enlarged local memory is CP, so the same closure applies.

A separable state sum_j p_j rho_j tensor sigma_j belongs to C: use chi=sum_j sqrt(p_j)|j,j>, L(X)=sum_j X_jj rho_j and M(X)=sum_j X_jj sigma_j. Both maps are CP and unchanged by input transpose, hence PPT. Finite-dimensional separable states have finite such decompositions. These are ordinary measure-and-prepare maps.

## 2. Sending a subsystem: explicit reshuffling lemma

Suppose Alice's state factors through a PPT map

    L : Mat(I) -> Mat(A tensor Csend),

while Bob's factor is M:Mat(J)->Mat(B). Alice transmits Csend through Phi=Q composed with P, with P:Mat(Csend)->Mat(D) and Q:Mat(D)->Mat(Bnew), both PPT. Define

    F=(id_A tensor P) composed with L : Mat(I)->Mat(A tensor D).

This map is CP. Its partial output transpose on A is also CP, since exactly

    (T_A tensor id_D) F
       = [id_A tensor (P composed with T_Csend)]
           composed with [(T_A tensor T_Csend) L].       (1)

Both factors on the right are CP: the first uses P's input PPT property and the second L's output PPT property. No identity tensored with a bare transpose is asserted CP.

Choose fixed product bases. Define R:Mat(I tensor D)->Mat(A) on matrix units by

    R(|i,c><j,d|)
      = sum_(alpha,beta) [F(|i><j|)]_(alpha c,beta d)
                                |alpha><beta|.          (2)

The Choi matrix of R is the Choi matrix of F with tensor order I,A,D permuted to I,D,A. It is positive. Its partial transpose on the A output is the same permutation of J((T_A tensor id_D)F), which is positive by (1). Thus R is PPT. This is an explicit index reshuffling, not the assertion that a general realignment preserves positivity.

Let Omega_D=sum_c |c,c> be UNNORMALIZED. Regroup

    chi'=chi_(I,J) tensor Omega_(D,D')

as a vector on (I tensor D) tensor (J tensor D'). Direct substitution in (2) gives

    [R tensor (M tensor Q)](|chi'><chi'|)
        = (id_A tensor id_B tensor Phi)(omega),          (3)

with the harmless local ordering B,Bnew on Bob's side. Indeed the (i,j,c,d) coefficient on the left is F(|i><j|)'s (c,d) block tensored with Q(|c><d|), exactly the expansion of applying Q to F's D output; chi supplies the original I,J coefficients and M the B factor. There is no factor dim(D), because Omega_D is unnormalized. M tensor Q is PPT by source tensor closure. The output is normalized because Phi is trace preserving. Consequently it lies in C.

The same argument with the parties exchanged handles transmission from Bob to Alice. Together with local closure, finite induction proves assertion 1 for arbitrary choices adapted to public history. No commutation of operations or reduction to independent channel inputs is used.

## 3. Purification, public records and the uniform bit gap

Retain all local dilation environments in the parties' private memories until final key readout. For each public history r of positive probability, the global state on these two memories and Eve can be taken pure: initial state was purified by Eve, channels act through Stinespring isometries with their environments given to Eve, and a public instrument branch is represented by one linear dilation into the private memory. The normalized bipartite marginal belongs to C by assertion 1. Eve therefore holds a purification of that C state, with no assumption about a physically implementable representation.

Condition on r and use the source's `thm:zero-key`, with n=1, for the parties' final local bit readout. It gives, for every normalized Eve comparison sigma_r,

    ||tau_r - idealbit tensor sigma_r||_1 >= 1/5.        (4)

Any discarded private systems can be included in the source's local readout channel; they are not silently transferred to Eve. An arbitrary channel Stinespring representation works, since the source gap allows an arbitrary purification.

For the unconditional output, dephase the comparison's public register first. This is a channel fixing the actual public register and cannot increase distance. Write actual and ideal dephased outputs as direct sums with public weights p_r and q_r. Put D equal to their unhalved trace-norm distance. When q_r=0 choose any normalized sigma_r. By the reverse triangle inequality and (4),

    D=sum_r ||p_r tau_r-q_r gamma_r||_1
      >=sum_r p_r||tau_r-gamma_r||_1-sum_r|p_r-q_r|
      >=1/5-sum_r|p_r-q_r| >=1/5-D.

The last inequality follows by taking the public marginal. Thus D>=1/10. If q_r=p_r, direct homogeneity gives D>=1/5. This avoids assuming that a comparison law must have the actual transcript distribution.

For any fixed key length ell>=1, discard every key coordinate except the first. An ideal ell-bit key maps to an ideal bit, and trace norm contracts, so the same gap holds before discarding. No sequence of such outputs can have vanishing security error with any eventual nonempty fixed key length. In particular no positive key rate per channel use is attainable. The zero-length protocol supplies rate zero. Trace-norm closure of finite protocols preserves the constant lower bound by continuity; the limiting comparison may vary, since the bound is uniform over all comparisons.

## 4. Explicit example and limits

The source gives a finite PPT trace-preserving Theta on Mat(21) with nonseparable J(Theta squared). Set Phi=Theta squared. It is a channel of the required form P=Q=Theta, and the source's local-corner argument already proves that Phi is not entanglement breaking. The proposed adaptive theorem would show K_two-way(Phi)=0 without claiming its Choi state's zero key is sufficient in general. The strict gap applies even to protocols jointly using many different such composites and to C initial resources.

All additions in this note require independent checking. In particular, possible objections must address the reshuffling's exact tensor order, PPT on the required A output rather than total output, physical Eve purifications conditioned on public histories, and variable public weights in the comparison. A theorem merely about Choi states, parallel uses, entanglement transmission or unassisted private capacity does not settle these quantifiers.

## 5. Contribution boundary

The old Choi correspondence, PPT-map closures, source C zero-key theorem, and source non-EB square are fully credited. CMHW's primary paper already gives the equivalence between composite PPT maps and local products of PPT maps, so it must be checked as a potential technical reduction. The alleged new content is the arbitrary-state closure under an actual cross-party channel use and its adaptive memory-and-feedback consequence. Neither novelty nor substantiality follows merely from this being absent in a keyword search. A full contribution gate must decide whether (1)–(4) amount to a standard cone/teleportation argument rather than a substantial new theorem. No acceptance is claimed.

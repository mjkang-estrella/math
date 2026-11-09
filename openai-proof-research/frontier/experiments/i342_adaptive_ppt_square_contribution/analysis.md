# I342 mathematical audit and explicit standard reduction

2026-10-13. GPT-6.1 Sol (`gpt-6.1-sol`), high reasoning; Standard speed requested, not independently exposed by the harness. No numerical experiment or subagent. Verdict: TECHNICAL; full frozen proof PASS conditional on the stipulated source and within the specified finite model.

## 1. Exact interfaces and hypotheses

The frozen candidate SHA256 is `1e66ba9bc7c98ced6deb292c960e9e5eb731b24aefd0e0884e5647d718078e91`. Source base S is

    preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/

in OpenAI/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. `S/sections/foundations.tex`, `def:represented-class`, allows omega=(L tensor M)(chi chi*) of trace one with arbitrary rectangular PPT maps L,M and unnormalized chi. `lem:ppt-stability` gives local CP pre/postcomposition; `lem:tensor-closure` gives finite tensors; `lem:choi-transfer` gives normalized J(QP) in C even for non-TP P,Q. `S/sections/secret-key.tex`, `thm:zero-key`, gives an unhalved 1/5 bit gap for any C state, n>=1, arbitrary input purification, any normalized ideal Eve law, and admitted completed local protocols. `S/sections/transcripts.tex`, `def:protocol`, explicitly allows finite local protocols, whole-input joint processing, private memories and two-way public discussion, with the supplied input the only shared private resource. `prop:operational-extensions`, item 1, explicitly includes normalized conditioning on any positive-probability public event.

We apply these interfaces, rather than investigate the truth of their proofs. The supplied input to a simulation is the original C state together with finitely many C Choi resources; tensor closure makes this one C input, so the source's no-other-shared-resource rule is respected. No secret key or external entanglement is supplied in addition to it.

## 2. Bell contraction with arbitrary correlated memories

Let Phi:Mat(d)->Mat(e) be CPTP, and let j=J(Phi)/d. In the source's input-first Choi convention,

    j=(1/d) sum_(i,j) |i><j|_U tensor Phi(|i><j|)_V.

Let X_SC=sum_(k,l) X_kl tensor |k><l|_C be any operator with spectator S; S can contain both parties' memories, an initial Eve reference and previous channel environments. Put beta=Omega_d/sqrt(d). For K=bra beta on C,U,

    K (|k><l|_C tensor |i><j|_U) K* = delta_(k,i) delta_(l,j)/d.

Consequently

    (id_S tensor K tensor id_V) (X_SC tensor j_UV)
      (id_S tensor K* tensor id_V)
        = (id_S tensor Phi)(X_SC)/d^2.                 (B)

There is no transpose remaining on X and no covariance requirement. K*K is a rank-one projector, so this is a legitimate local trace-nonincreasing CP branch, completable by the complementary effect. TP implies that its probability on every normalized input is d^(-2), independent even of the spectator. Only Phi is physically simulated: P and Q need not be physical channels and there is no access to their intermediate output.

Suppose before transmission omega is C across (A,C):B. Since Phi=QP with PPT factors, source Choi transfer gives j in C across U:V. Tensor it with omega and group the parties as (A,C,U):(B,V). The sender applies K locally and retains A; the receiver retains B,V. Local filter closure leaves the unnormalized output represented by PPT maps. Equation (B) says that output is exactly d^(-2)(id_AB tensor Phi)(omega). Scaling the representing vector by d normalizes it and preserves C. Swapping laboratory roles proves the same fact for Bob-to-Alice transmission. Each one-use closure statement includes all correlations with existing memories.

Thus any finite protocol in the frozen model remains in C at every positive public prefix by induction: instrument branches are local CP maps, public scalars only change normalization, and any public-history selected channel use has the preceding closure. A collection of arbitrarily many possible channels causes no difficulty: each finite decision tree selects only finitely many channel nodes, and the one-use statement itself is universal.

## 3. Environment identity, not just marginal simulation

Choose the actual channel isometry V:C->Vout tensor Enew, with V*V=I, using any prescribed Stinespring realization of the **composite**. Its normalized Choi purification is

    |eta>_(U,Vout,Enew) = (id_U tensor V)|beta>_(U,C').

For any vector |psi>_(S,C), direct contraction gives

    (bra beta_(C,U) tensor id_(S,Vout,Enew))
          (|psi>_(S,C) tensor |eta>_(U,Vout,Enew))
       = (id_S tensor V)|psi>/d.                      (E)

The scalar is 1/d, so after normalization the entire spectator/output/environment vector equals the physical transmission vector. For arbitrary Choi purifications one obtains the same statement up to an Eve isometry. It is easiest to choose |eta> for the actual V from the outset; nonminimal environments cause no problem. This isometry argument does not provide Eve with a party's private shield.

Every public instrument branch with Kraus operators A_(r,k) has a dilation W_r=sum_k A_(r,k) tensor |k> in retained local memory. Acting on a pure input gives a pure unnormalized branch. Private classical controls can be purified and coherently implemented locally, with later dephasing reproducing the original classical behavior. This enlarges the local memory through CP maps and preserves C. The original output is recovered through the final local readout, including tracing unused private systems. At any fixed public record, initial Eve purification, these local dilations and the physical channel isometries therefore give the required Eve purification of the enlarged C marginal. This justifies the candidate's physical purification argument independently of the Bell reduction.

## 4. Full adaptive simulation and the parent's repair

Fix a finite bounded-depth public decision tree with finite outcomes. Associate a separate normalized Choi resource to **each possible channel-use node**, with the reference at that node's sender and output at its receiver. Multiple nodes can use the same channel but have independent resources. Tensor all resources with the initial C state. Choose product Choi purifications, together with the actual initial purification, as Eve's purification of this C input. Resources outside the chosen public path remain untouched.

Execute the original local operations; replace each reached channel node by the Bell filter above; publicly flag failure and stop when necessary. At terminal original public record r with no Bell failures, equations (B) and (E) show that the unnormalized physical block is multiplied by

    w_r=product_(v on r) d_v^(-2)>0.

Here p_r is the original protocol's probability for r, and tau_r is its normalized joint key/physical-Eve block. The unnormalized simulated block after discarding unused local resources has the form

    p_r w_r [W_r tau_r W_r* tensor mu_r],

where W_r embeds/reorders the used Eve environments and mu_r is the reduced state of the purifiers of unused resources. Both depend only on r, not on the final private key. For a fixed r, untouched resources remain a tensor factor even though which resources are untouched depends on the record. The notation W_r here denotes an Eve environment embedding, distinct from the local instrument dilation in section 3.

Naive conditioning on all Bell successes gives law proportional to p_r w_r; it is generally **not** p_r. For example, two terminal paths with one input of dimensions 2 and 3 have weights 1/4 and 1/9. This is an exact symbolic example, not a numerical scan. The flaw is in that naive reduction, not in the frozen candidate, which uses branchwise induction instead.

Let a=min_r w_r over the finite terminal tree, including any unused or zero-probability records if desired. It is positive. On a successful record r, one party makes a local rejection coin with accept probability a/w_r and publicly announces it. This is a valid input-independent scalar rule at that fixed history, independent of the private key. In a retained dilation its successful amplitude is sqrt(a/w_r), giving total amplitude sqrt(a) on every original path. The accepted unnormalized block is exactly

    a p_r [W_r tau_r W_r* tensor mu_r].

Summing gives acceptance probability a, and the normalized accepted transcript law is exactly p_r. The extra successful Bell and coin records are determined by r on the accepted event; they add no new key dependence. Finite resources, bidirectional orientation, correlated memories, adaptive channel selection and adaptive dimension selection have all been preserved. No claim of efficient or deterministic channel simulation is involved.

Complete the local simulation on every failure or rejection by producing the fixed bit zero at each party, publicly announcing failure and retaining the full record. The resulting completed finite local protocol meets source `def:protocol`. Its accepted event A is an event of the complete public record with probability a>0. Source `prop:operational-extensions` item 1 gives a 1/5 gap for its normalized accepted bit output from **every** ideal bit comparison. Exponentially small a is harmless because the source proposition is uniform over every a>0. Merely invoking K_D(j)=0 would not supply this fact.

One last information-direction check is necessary. A lower bound with additional Eve systems does not automatically survive discarding them. Here it does for a specific reason: define an Eve-only channel Lambda that dephases the physical public record, applies the known environment embedding W_r, appends mu_r and the successful public tags, and uses an arbitrary fixed extension on records with p_r=0. It is CPTP on the direct-sum physical Eve space. The accepted simulated state is Lambda(tau_original), with keys untouched. For any physical comparison sigma, Lambda sends the ideal independent key to the ideal key with comparison Lambda(sigma). Therefore

    ||tau_original-gamma_sigma||_1
      >= ||Lambda(tau_original)-gamma_(Lambda(sigma))||_1
      >= 1/5.

Unused Eve information is added by a key-independent conditional preparation, not removed by an unjustified security argument. This verifies the parent's repaired whole-run reduction, and gives a stronger constant than the frozen claim for finite trees. Its counterpart branchwise proof below already suffices for every requested statement.

## 5. Frozen reshuffling lemma checked by indices

Let L:Mat(I)->Mat(A tensor C), M:Mat(J)->Mat(B) be the representing PPT maps, P:Mat(C)->Mat(D) and Q:Mat(D)->Mat(Bnew) PPT. Put F=(id_A tensor P)L. Then

    (T_A tensor id_D)F
      = [id_A tensor (P T_C)] [(T_A tensor T_C)L].      (1)

The right-hand factors are CP by P's input PPT and L's total output PPT; the T_C occurrences cancel algebraically. The dimensions match, and F is CP. Write

    F(E_ij)=sum_(alpha,beta,c,d) f_(ij;alpha c,beta d)
                  E_(alpha beta)^A tensor E_(cd)^D.

The candidate's R is R(E_(ic,jd))=sum_(alpha,beta) f_(ij;alpha c,beta d) E_(alpha beta). If U is the permutation unitary taking I,A,D to I,D,A, then

    J(R)=U J(F) U*,
    J(T_A R)=U J((T_A tensor id_D)F) U*.

Both are positive by the CP statements, hence R and T_A R are CP. R is rectangular PPT on the claimed input I tensor D and output A. This is conjugation by a tensor permutation, not a realignment exchanging bra and ket indices.

For chi=sum_(i,k) chi_ik |i>_I|k>_J and chi'=chi tensor Omega_(D,D'), the represented output expands to

    sum_(i,j,k,l,c,d) chi_ik conjugate(chi_jl)
       R(E_(ic,jd)) tensor M(E_kl) tensor Q(E_cd).

Substitution gives exactly sum chi_ik conjugate(chi_jl) (id_A tensor Q)F(E_ij) tensor M(E_kl), reordered locally as A:(B,Bnew). This is the desired (id_AB tensor QP)(omega). The unnormalized Omega has coefficient 1 for each |c,c>, so no dim(D) factor appears. M tensor Q is PPT and composite TP makes the output trace one. All claimed new algebraic steps pass.

## 6. Branchwise comparison, capacity and limits

For every positive public record r before key readout, the enlarged C state is purified by the physical Eve systems conditional on r. Source `thm:zero-key` at n=1, with the final local first-bit readout a completed protocol, gives

    ||tau_r - gamma_(sigma_r)||_1>=delta,   delta=1/5,

for every normalized conditional comparison. Actual output is classical in r. Dephasing any comparison fixes actual output and preserves ideal-key independence, so it suffices to consider direct sums p_r tau_r and q_r gamma_r. If q_r=0 choose any normalized gamma_r. Homogeneity and reverse triangle inequality give

    D=sum_r ||p_r tau_r-q_r gamma_r||_1
      >=delta sum_r p_r - sum_r |p_r-q_r|
      >=delta-D.

The last step traces out the keys and quantum Eve systems, leaving the public marginal. Thus D>=delta/2=1/10. If q=p then D>=delta=1/5. Terms with p=0, q>0 cause no problem, and comparison coherence was dealt with by contraction rather than assumed absent. This audit validates the frozen p-versus-q step.

Keeping the first coordinate of a nonempty ideal fixed-length key gives an ideal bit by local classical channels. Its gap lower-bounds the original key gap. Every secure channel-coding sequence with positive rate would eventually produce a nonempty key with vanishing error, contradicting the dimension-independent constant. Separable initial states are C: take finite measure-and-prepare representations L(E_ij)=delta_ij rho_i and M(E_ij)=delta_ij sigma_i and chi=sum_i sqrt(p_i)|i,i>. These maps are unchanged by input transpose. The zero-length code attains rate zero. Adaptive use of a family and bidirectionality were already included in the per-node argument.

On a fixed finite output space retaining the complete public record and physical Eve information, the distance to the set of ideal independent keys is 1-Lipschitz in trace norm. For any limit tau and any comparison gamma,

    ||tau-gamma||_1 >= c-||tau-tau_n||_1 -> c.

This is uniform in comparison choice and does not require the comparisons themselves to converge. Embeddings that drop full public history or Eve purification are outside the candidate's retained-information model; the source's `prop:operational-extensions` item 3 explicitly makes the same distinction. No nonapproximable infinite protocol or infinite-memory assertion is needed.

## 7. Contribution classification and example

Source `prop:channel-completion` and `thm:main-channel` supply Theta:Mat(21)->Mat(21), PPT and TP, with nonseparable J(Theta squared) by a local corner argument. P=Q=Theta puts Phi=Theta squared within the reviewed theorem. It is non-EB yet has zero two-way assisted key capacity in this model. Theta alone does not qualify for this substitution and no conclusion about its key capacity is drawn.

The substantive uniform zero-key fact and explicit non-EB square belong to the pinned OpenAI manuscript. The old Choi transfer and PPT local-product correspondence are credited to CMHW. Ordinary postselected channel-state contraction, now independently normalized and extended to the full environment, supplies the missing cross-party closure through an ordinary local filter. The parent supplied the adaptive-weight objection and repair. The source even states the needed uniform public-conditioning extension. Thus the full adaptive result is a useful technical corollary of those ingredients, not a demonstrated independent substantial theorem. The reshuffling proof is correct but dispensable.

CMHW Section IV.B is relevant machinery, not a published full adaptive key result. Deterministic teleportation stretching cannot simply be presumed for every Phi, and key-relevant entanglement measures were not proved zero here. Repeater rate bounds do not automatically preserve this bidirectional channel model. The literature comparison and exact read scopes are in the assigned literature and reading records. No world-priority or verbatim-duplicate conclusion is made.

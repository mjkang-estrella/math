# T221R: full proof retained, technical contribution

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Parent integration,
not another independent review. Frozen author and reviewer packets are unchanged.

The independent verdicts are **PASS_FULL_T221R** and **TECHNICAL**. Both apply
to the full original scope: every fixed d>=3, beta>0, symmetric integrable
coupling and integrable field, configuration and uniform simple regular graphs,
all admissible sizes, and the infimum over every finite hierarchy depth, trial
law and exponent tuple. No narrowed replacement is adopted. T221R receives no
campaign count and no formal-support/manuscript/release escalation. The total
remains **13/20**, with seven acceptances still required; uploads stay stopped.

## Attribution and scope of the disposition

The proof review found no required objection. It relies on the stipulated
family-221 source and the external upper-bound and simplicity theorems; it
checked their interfaces rather than re-proving those external theorems.

The contribution review treats the conclusion as new to this project if the
proof holds, but rates the residual matching, variance and perturbation
bookkeeping technical. Its operation ledger credits the pinned tree,
perturbation, decorrelation and encoding arguments, Lelarge--Oulamara's
finite-depth upper bound, and the Coja-Oghlan--Perkins cavity reservoir. This
disposition accepts that verdict without a count-driven appeal. It is neither
a duplicate-theorem finding nor a novelty certificate.

Two additional credits apply to the author contribution statement in the
frozen proof, which is preserved as reviewed:

- Franz--Leone--Toninelli, cond-mat/0307367v2, section VI, especially the
  extraction lines 817--820 and 943--945, already uses degree-deficient-site
  weights for inserted perturbations and overlap identities, and discusses
  sublinear perturbation sizes. This is an antecedent of localization to
  cavity coordinates. It is not itself the full hierarchy formula proved here.
- Coja-Oghlan--Perkins, arXiv:1808.03440v1, section 6, extraction lines
  2465--2468, explicitly recognizes the completion distribution tilted by
  extension counts. The explicit mesoscopic normalization and variance
  estimates do not make the tilt operation new.

Lelarge--Oulamara's open-problem sentence at lines 97--100 concerns their
independent-set application. It must not be presented as a direct statement of
this exact spin-glass target. No worldwide novelty claim is made. Concetti's
relation between a full-RSB functional and the finite-level infimum is outside
the frozen scope; neither that identification nor its conjectural consequences
are adopted here.

## Proof precision retained for future use

The following are nonblocking clarifications from the proof reviewer, recorded
outside the frozen proof:

1. Identify Lelarge--Oulamara's free energy through section 4.1's uniform
   port-matching definition; list conditions (3)--(4), and use admissible
   dn-even sizes. The Ising factorization has a=cosh(beta J), b=tanh(beta J),
   even p=2; symmetry pays the sign condition, bounded truncations pay
   integrability before passing to the full disorder law.
2. Use s<=n in the variance comparison. Conditional on the cavity set and
   missing ports, E[W]=1, and the conditional variance of W is independent
   of that labeling.
3. The exact insertion identities are E X_bond = E X_R + E log Y_b and
   E X_star = E X_R + 2 log 2 + E log Y_star. New insertion disorder is
   adjoined as root variables. Legal ports are never frozen by the sequential
   switch; its error is O((q+1)/n), which also covers small q.
4. The bad-index estimate applies the fixed-q increment argument at every n,
   before changing q; it does not rely only on the good-index formula.
5. Family-221 decorrelation.tex lines 6--8 explicitly allow L-dependent
   sequences. The selected multioverlap moments are averaged over I, the
   cavity pool.
6. For simplicity, Janson Theorem 1.1(i) or Corollary 1.5 is sufficient and
   preferable to the sketch at Theorem 7.1. Only a positive lower bound on
   simplicity probability is needed. Fixed d satisfies sum d_i^2=O(N).
7. The two stars and d bonds have both disjoint trial labels and independent
   physical disorder. These yield the factors 2 and d after expectation.
8. Any extension to d<3 or beta=0 is uncredited: no enlarged scope is adopted.

## Identity checks and their limits

Parent read both complete review reports and reading limits, both verifiers,
the proof diagnostic and contribution controls. Parent ran the proof verifier
with all 23 copied controls and exact diagnostic replay; it checked all 26
blobs against the actual canonical tree. Parent ran the contribution verifier
with its external manifest and verifier anchors and all 14 own-packet controls
on an owned disposable copy. The original packets pass after these checks.
The JSON receipts are adjacent to this note. These checks establish byte
identity and finite replay only, not mathematical truth or contribution.

The author verifier does not inspect symlinked ancestors. It also trusts its
copied source tree: a consistently changed body, receipt, tree and manifest
can pass under a *different counterfeit anchor*. That is not a bypass of the
actual frozen external anchor. Independent comparison to the separately
anchored canonical tree rejects that counterfeit. Preserve both limits;
do not describe author verification alone as source authentication.

The author's controls put scratch inside the packet; future packets should
use external scratch. The source-path KeyError is a nonzero rejection but an
unclean error report. The unrelated family349 payloads enlarge the frozen
packet without entering the T221R proof. None is silently removed or resealed.

Parent additionally read the actual FLT lines 790--860 and 925--960, COP
2445--2485, LO 80--110, and Janson 110--200 when integrating this review.
Earlier parent source readings and author assistance remain disclosed in
source-interface-reading.json and author-side-reservoir-check.md. Parent has
not independently re-read every primary body or supplied a third proof gate.
Reviewer-specific reading limits remain in their respective packets.

## External anchors

- Author manifest: c288940c8c88f67a7374d998a7c49d822f64000abb981517303f1bf4af9739c6.
- Proof manifest: 957ad8463d57c42f8d89ba42cc29c5086dd953c4d481677011389a8831451904.
- Proof verifier: e02817776beee7e730454faf0b3a38e77d19a101546e4753aacff6ab53ad231d.
- Contribution manifest: 69ef9338acb30fbaaa072eb5e30d5cd6cfdbfba7f4eb7baebb6a09f2de8fdde5.
- Contribution verifier: 05e71ed48da8146fd79e25bef31073afc3b298357443009875eb547c3fbdcad1.

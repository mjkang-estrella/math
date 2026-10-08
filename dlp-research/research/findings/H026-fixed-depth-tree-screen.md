# H026 fixed-depth signed tree: exact coverage screen

2026-10-08. Native Sol independent initial proposal and counting screen;
root independently derived the finite sum. A separate native Astra mathematics
review COMPLETED, GO with the qualifications below. No experiment, formal Lean
claim or complete-work improvement.
Do not extend this claim to coordinate-adaptive labels.

## Literal construction and quantifiers

Fix an odd prime order q and Q=[k]G, with unknown k uniform in F_q. Every
root/jump label is an affine pair relative to (G,Q), chosen independently of k.
The tree's node at depth j is

    C + sum_(h=1..j) epsilon_h J_h,  epsilon_h in {-1,+1}.

All nodes through depth d are inspected. There are T_d=2^(d+1)-1 node records
before coincidences. One reused jump J_h is shared by the entire depth, not
chosen independently for each edge. Root and jumps may depend on public q or
independent randomness; condition on that randomness when counting. Allow M
other inspected setup/input points whose affine labels are also fixed without
secret dependence. Recovery here is through useful signed point collisions or
infinity, followed by scalar verification. Additional guessing/computations are
not implicitly covered by this channel bound.

## Finite bound

For two node depths i<=j and either sign, the first i jump coefficients in the
collision equation have at most three possibilities (0,+2,-2), and the remaining
j-i coordinates at most two (+1,-1). Root coefficient is either0 or2. Hence
each sign has at most

    S_d=sum_(0<=i<=j<=d) 3^i*2^(j-i)
       =(3^(d+2)-2^(d+3)+1)/2

coefficient patterns. Repeated patterns, equal affine labels and coefficient
reduction modulo q can only decrease the number of useful equations. A
nonzero target coefficient determines at most one k because q is prime.
Zero-target identities or contradictions yield no recovered k.

Count both signs by2S_d; tree/infinity by T_d; tree/setup collisions by
2M*T_d; setup/setup signed pairs by M(M-1); setup/infinity by M. Thus useful
secrets accessible by these channels are at most

    min(q, 2S_d+(2M+1)*T_d+M²).

This bound overcounts deliberately, including some self/tautological and input
cases. Its purpose is to upper-bound coverage, not predict a collision constant.
For d=floor((log2 q)/2), T_d=Theta(sqrt(q)); if M is polylog(q), success is

    O(q^(log2(3)/2-1)) + O(polylog(q)/sqrt(q)),

which tends tozero (first exponent approximately-0.20751875). Averaging over
independent randomness does not change the uniform bound. This literal tree
therefore cannot supply constant-success square-root search using only these
channels, even if its generation kernel is inexpensive. This is not a general
ECDLP lower bound, nor a theorem about coordinate-adaptive jump labels,
secret-dependent support sets, or some unrelated nonlinear recovery method.

## Candidate arithmetic, separately reviewed

A breadth-first schedule batches a level's shared inversions. Both children
remain full affine points except the bottom leaves, whose ordinates can be
omitted. For d>=1, proposed ordinary total cost is

    (6*2^d-7)M_field +(2*2^d-2)S_field +d*(I-3M_field),

excluding paid root/jumps, special cases, labels, storage and verification.
The normalized limit is3M_field+S_field per emitted key, but an efficient
kernel does not compensate for the counted shortage of useful equations.
The exact screen survived independent review; no numerical trial is needed.

## Independent review and disposition

Native Astra independently verified S_d, setup/infinity counts, the uniform
secret quantifiers and the regular ledger. A full paired-child level with n
parents costs7nM_field+2nS_field+(I-3M_field); an x-only bottom level costs
5nM_field+2nS_field+(I-3M_field). Summing gives the displayed formula.

It explicitly requires actual elliptic negation equality for signed x keys,
an infinity sentinel and final scalar verification. Fingerprint equality alone
does not prove a useful relation. Infinity, zero jumps, coincident/negated
operands and repeated states require paid dispatch; no uniform exception-cost
bound is supplied. These unresolved costs cannot repair the upper bound on
useful secrets accessible by the specified equation channels.

Reject this literal fixed-jump tree at the proposed depth. No experiment or
new broad Lean machinery is admitted. This is an informal mathematical result
with independent checking, not a newly formalized Lean theorem. Node-specific
paid supports, coordinate-adaptive labels and different recovery mechanisms
are outside its scope, not ruled out.

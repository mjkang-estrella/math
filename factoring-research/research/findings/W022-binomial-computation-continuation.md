# W022 parent continuation: actual cost of the binomial target

Derived while W022 B is independently audited. This does not establish its
correctness or novelty; it examines concrete ways to compute the proposed
target without supplying hidden factors.

The direct recurrence B_0=1, B_(j+1)=2(2j+1)B_j/(j+1) computes B_m=binom(2m,m)
exactly. For m=(N-3)/4 it has Theta(N) steps and the final integer has Theta(N)
bits. Reducing numerator and denominator modulo N before division is invalid
when the denominator is a nonunit. Detecting the first such denominator is
itself the existing small-factor search; batching its gcds is a comparator,
not a new way to get the central binomial residue for free.

A different attempted computation uses the algebraic generating series

    F(z)=(1-4z)^(-1/2)=sum B_j z^j.

One might hope to extract the binary digits of m with a constant-size parity
recurrence. Its even subsequence E(z)=sum B_(2j) z^j instead satisfies

    E(z)^2 = 1/[2(1-16z)] + 1/[2 sqrt(1-16z)].

This follows by squaring (F(sqrt z)+F(-sqrt z))/2 as a formal power series.
It already introduces an additional square-root layer; the informal claim
that algebraic degree stays two is wrong. Repeated parity extraction needs
an actual bound on representation growth. A short nested expression is not
an algorithm for its high-index coefficient. No general lower bound follows.

Likewise, auxiliary-prime reconstruction of the exact integer B_m needs
enough combined modulus to exceed an integer with Theta(N) bits. Knowing
B_m modulo a product P merely larger than N does not determine B_m modulo N:
B_m and B_m+P have the same auxiliary residues, generally different residues
modulo N. The reconstruction size cannot silently use N in place of B_m.

These calculations leave a specific frontier: a residue-only computation
exploiting N=4m+3, with proved cancellation of nonunits or a bounded-size
coefficient recursion. The current direct and auxiliary-CRT methods do not
supply it. This target differs from asking for an arbitrary coefficient oracle,
but no favorable acquisition cost has yet been demonstrated.

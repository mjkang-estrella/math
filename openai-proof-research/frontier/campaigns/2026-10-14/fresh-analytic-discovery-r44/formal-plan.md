# Scoped formal plan — no formal theorem claimed

Original prose: Myeongjin Kang, CC BY 4.0. Code in this packet: MIT.

The complete proof is analytic/probabilistic. No Lean certificate of
T221R, no imported axiom asserting its conclusion, and no formal-gate
pass are claimed. A useful first scoped formal artifact would certify
the finite port-completion interface, with the following public contract:

* A finite labelled vertex/port set, positive fixed degree, distinguished
  cavity vertices with one absent port each, and an even active port count.
* Uniform perfect matchings on the active set.
* An exact bijection between bond-completion inverse histories and sets
  of disjoint nonloop edges on full vertices.
* Summation of prescribed-pair probabilities giving equation (3.6).
* The one-step legal-partner switching kernel, with row probabilities
  summing to one and output exactly the uniform conditional matching law.

The executable exact-rational diagnostic checks these interfaces on
small spaces and rejects two natural wrong laws (uniform completion,
fixed missing ports with the unrestricted M_d density). It also checks
the strict scale exponents. These finite checks are not proofs for all
sizes and cannot substitute for the above formal contract or the full
mathematical review.

Remaining formal scope would include bounded-difference variance,
conditional power means, Poisson marked kernels, source prescribed-tree
identities/decorrelation as explicitly stipulated dependencies, parameter
selection and ordered limits, and uniform truncation. A finite counting
certificate alone must never be described as verifying these steps.

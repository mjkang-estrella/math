# Statement correspondence

Sources are copied as inert text in provenance. The Hetyei source is arXiv:2007.07362v2, btch-v02.tex; its numbering 5.6, 5.7, 5.8, 5.9, 5.14 corresponds to published Definition 31, Theorem 32, Corollary 33, Definition 34, Conjecture 39. Published citation: Discrete Comput. Geom. 71 (2024), 918–944, DOI 10.1007/s00454-023-00490-4. The source text and adjudication were supplied locally; this lane performed no network or new prior-art investigation.

Exact source formulas and locations:

* Lines 964–971: “The coproduct Δ is defined on the algebra Q⟨a,b⟩, whose basis is the set of all ab-words … Δ(u)=Σ_{i=1}^n u₁⋯u_{i−1} ⊗ u_{i+1}⋯uₙ.”
* Lines 978–980: “u*=uₙu_{n−1}⋯u₁, obtained by reversing the word”.
* Lines 1169–1184: M is the sum over r,s ∈ {1,2} and n−r−s−1 even, with M₁,₂,₂(u,v)=u·a·v and alternating coproduct recursion. Hetyei prints M₂,₁,₂(u,v)=u·b·v.
* Ehrenborg–Readdy, Coproducts and the cd-index, Definition 9.1, provenance/ER-coproduct.txt lines 1048 and 1062–1071: “I = {(r,s,n) : r,s ∈ {1,2}, n ≥ 2, n ≡ r+s+1 mod 2}”; “M₁,₂(u,v,2)=u·a·v, M₂,₁(u,v,2)=v·b·u”; “M₁,s(u,v,n+1)=Σ_u u₍₁₎·a·M₂,s(u₍₂₎,v,n)”; “M₂,s(u,v,n+1)=Σ_v v₍₁₎·b·M₁,s(u,v₍₂₎,n).”
* Lines 1197–1206: “the linear operator … is given by the formula I₂(u)=u+u*+Σ_u M(u₍₁₎*,u₍₂₎).”
* Lines 1235–1239: “If the homogeneous ab-polynomial u ∈ Q⟨a,b⟩ₙ satisfies u*=−u then I₂(u)=0.”
* Lines 1245–1251: “symmetric if it satisfies u*=u and antisymmetric if it satisfies u*=−u.” These spaces are denoted S and A respectively.
* Lines 1344–1347: “For each n≥1, the kernel of I₂: Q⟨a,b⟩ₙ → Q⟨a,b⟩ₙ₊₁ is A_Q⟨a,b⟩ₙ.”

MathDB 347230 literal (full raw JSON is supplied):
“Let Q⟨a,b⟩ₙ denote the vector space of homogeneous noncommutative ab-polynomials of degree n, and let I₂: Q⟨a,b⟩ₙ → Q⟨a,b⟩ₙ₊₁ be the interval transform of the second kind. Let A_Q⟨a,b⟩ₙ be the specified subspace … For each n≥1, ker I₂=A_Q⟨a,b⟩ₙ.”

| Source object | Lean encoding |
| --- | --- |
| a, b; word; empty word | false, true; Word := List Bool; [] |
| Q⟨a,b⟩ | ABPoly := Word →₀ ℚ |
| coproduct pieces | cop, indexed by List.range word.length |
| u* | star := Finsupp.lmapDomain … List.reverse |
| reversal involution | star_involution |
| Mᵣ,ₛ,ₙ | Mrs r s n, false = 1 and true = 2 |
| full index condition | rsVal, inIndex |
| finite range, proved | Mrs_eq_nil_of_large |
| M on words / polynomials | Mw / M (bilinear extension) |
| Theorem 32 operator | I2w / I2 (linear extension) |
| homogeneous degree n | deg n := Finsupp.supported … {w : w.length = n} |
| antisymmetric Aₙ | anti n := deg n ⊓ ker(star + id) |
| conjecture, all n≥1 | KernelConjecture |
| negation | kernel_conjecture_false |
| non-vacuity control | kernel_equality_degree_two |

Two source slips are explicit adjudicated interpretations, not hidden assumptions. First, M₂,₁,₂ is read as v·b·u, following the cited original ER Definition 9.1 and root's supplied ruling. The source's printed u·b·v contradicts its own Corollary 33. Second, the printed degree n+1 codomain is a slip: Theorem 32 preserves degree. The kernel of the restriction is expressed as deg n ⊓ ker I2 in the ambient free vector space. This does not encode a fictitious degree-raising operator. The endpoint refutes the intended ER reading under root's explicit adjudication.

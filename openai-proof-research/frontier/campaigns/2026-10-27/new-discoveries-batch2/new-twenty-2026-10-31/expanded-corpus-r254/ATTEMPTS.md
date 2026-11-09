# Sustained ordinary attempts

Zero credit. No Lean work or computational search was performed.

## 331498: exact coefficient certificate route

Primary bodies: Albert–Bousquet-Mélou, arXiv:1312.4487, Section 6.3, property P2 on printed page 32; source arXiv:1510.00777, Section 4, Conjecture 4.1. The source's a,b,c,d in that line are inconsistent with its preceding r,l,u,d notation. The original P2 removes the ambiguity: fix an arbitrary Dyck vertical word V with n N's and n S's; allow **all** horizontal Dyck projections with m E's and m W's. Count adjacent factors NW and ES. Require coefficientwise nonnegativity after x = y - 1. A witness must satisfy this original interpretation; do not exploit the notation error.

Let F(i,e,w,L) be the polynomial enumerating prefixes with the first i vertical steps of V used, e E's, w W's, last step L. Restrict 0 <= w <= e <= m, and use every vertical step in its prescribed order. Initialize F(0,0,0,empty)=1. Append E if e<m with weight 1. Append W if w<e with weight x exactly when L=N. Append V[i] if i<2n, with weight x exactly when L=E and V[i]=S. All other weights are 1. Add contributions arriving at the same state. Sum terminal last states to get G(x).

Proof of recurrence: deleting the last step gives a unique admissible shorter prefix. Every admissible path stays in the quarter plane because its horizontal height is e-w and its vertical height is the corresponding Dyck prefix height. Conversely every loop with vertical projection V has exactly one transition sequence. Only an appended step can create a new adjacent factor, and the two indicated cases are precisely NW and ES. This proves the recurrence by induction on i+e+w. Therefore a negative integer coefficient of G(y-1) is a complete ordinary refutation of P2, not numerical evidence.

If G(x)=sum a_j x^j, the target coefficient is b_k=sum_{j>=k} (-1)^(j-k) binom(j,k) a_j. An exact certificate consists of V, m, all state coefficient vectors, and k with b_k<0; alternatively store vectors directly in y, applying multiplication by y-1 as shift minus identity. The certificate checker needs only integer addition and finite induction, no floating point, polynomial root isolation, or exhaustive path list. Size at most 5(2n+1)(m+1)^2 vectors of length 2n+2m+1.

The constant term alone is weak: signed-peak parity and the source's results explain positivity at -1. Search coefficients k>=1. Neither the signed-peak theorem nor equality of parity distributions implies all b_k>=0. No sign-reversing involution for general V was found. Restricting V=N^n S^n is a poor first target: the source's final open-question discussion proves a fixed-pair special case there. Prefer several alternating runs in V.

Complete **textual** negative-example inventory of original Section 6.3: N1 gives nonloops 2a+1 at endpoint (-1,2) and 15a+12 at endpoint (5,0); N2 fixes BOTH projections (EWEWEW,NNNSSS), yielding 62a^3+292a^2+390a+180; N3 uses V=SSNN outside the positive vertical domain, giving 4a^2+6a+5. None is a P2 witness. The secondary source gives G1=x^2+12x+15 at r=l=4,u=d=2 as an example separating toggle-buildability from positivity, not a refutation. No witness is proposed here. Figure-level inventory of every cited paper and latest journal bodies remains a gate before credit or significant search investment.

## 331097: full ordinary representative lemma, probably ineligible routine bridge

Source Definition 2 and Conjecture 13, arXiv:1508.02432, printed page 7. Distinct compressed vertices identify equal annihilator ideals. Do not treat two representatives of the same class as distinct vertices. The edge criterion in the literal record, taken alone, is simply ab in I iff some n_alpha divides ab, because I is their union. The interesting source clause is that products of basis divisors represent **all** vertices.

Here is a full ordinary proof of that clause. Let a not in I represent a nonzero zero divisor, and factor nonzero a into finitely many primes. For each prime p dividing a, let

    e_p = max_{alpha} min(v_p(a), v_p(n_alpha)).

This maximum exists: its values lie in the finite set {0,...,v_p(a)}. Omit primes with e_p=0 and put d=product p^e_p. Each retained p^e_p divides some n_alpha attaining the maximum. Moreover p^e_p is not in I, since it divides a and I is an ideal. Thus it is a permitted nonassociate divisor in the source basis, up to a unit. We have d|a. For every alpha, gcd(d,n_alpha) is associate to gcd(a,n_alpha): valuations agree for primes in a by the maximum definition and vanish for other primes. By unique factorization,

    n_alpha | a z  iff  n_alpha/gcd(n_alpha,a) | z
                   iff n_alpha | d z.

Taking the union over alpha gives az in I iff dz in I, for every z. Hence the residue classes of a and d have the same annihilator; d not in I, and its annihilator is nonzero because a represents a zero divisor. It represents the same vertex. Replacing prime powers by the selected basis associates changes d by a unit, preserving its annihilator. This proves the required product representation without finiteness of Lambda, minimal-union uniqueness, or Noetherian hypotheses. The adjacency statement then follows from membership in the union. The cases of an empty graph require no construction.

This is a complete ordinary route under the usual nonzero-generator reading of the source. A zero principal summand can be removed when I is nonzero; I=0 has no zero-divisor vertices in a domain. I=D likewise gives no vertices. No finite computation is necessary. However, this is a direct UFD divisor-truncation argument plus the definition of compressed adjacency. It is strongly exposed to the campaign's routine-annihilator/source-bridge exclusions, in particular 343057 and the 364079/334207 precedents. Recommend ZERO CREDIT and root significance adjudication before assigning any Lean implementation. Later quotient-UFD literature and the journal body are not cleared. Do not call this a new significant solution.

## 331779 and 331780: valuation dynamics, precise remaining barrier

Source arXiv:1511.04315, Sections 1–3. The exact arithmetic rule is Z(a,b)=ab/gcd(a,b)^2, so for every prime p, v_p(Z(a,b))=|v_p(a)-v_p(b)|. An induction gives the correct reduction to a triangle beginning with v_p(1),v_p(2),... . A certificate for a square on the left edge at row R therefore needs only one prime and R initial valuations, followed by R-1 exact adjacent-absolute-difference rows and terminal value >=2. No huge integer factorization of the triangle is needed. Recovering the arithmetic claim is a proved valuation bridge, not a heuristic.

Two obstructions prevent pretending this is a full route. First, zero/one entries evolve by XOR, but heights >=2 do not superpose linearly; replacing the full valuation word by parity discards the very obstruction sought. Second, a connected high-valuation region meeting another region is not by itself a refutation of 331779 unless they have distinct source seeds p^g and the source's geometric connectivity is matched. The source literally says powers 'larger than two', then discusses powers 'less than two'; the intended exponent threshold must be settled from its figures and Section 3 before implementing connectivity for odd p. Do not conflate numeric p^v>2 with v>=2.

The p=2 case is already proved by the source, and its isolated-seed/periodic squarefree model does not establish the full odd-prime valuation triangle. A proof for all p needs a confinement lemma bounding each seeded high-level component away from the western edge and from other seeds for all times. No such lemma was obtained. Its p=2 word recursion is not valid unchanged for odd p. Park rather than run a large triangular sweep. Source Figure 1 and its first 15 edge entries, Figure 2 (p=13,17, exponent 14), and Figures 3–7 plus their tomography constructions are source-owned controls, not discoveries.

# 373070 — author full ordinary construction; scientific HOLD, zero credit

Exact literal: originals/373070.jsonl, raw/token/decoded bindings in provenance.json. The full target is: for each integer m>=2 there is K_m such that every integer n>=K_m has more than 2^(m/2) MSTD m-subsets of Dic_(4n). No parity restriction on n. Source: Mandal–Neetu 2602.09073v1, Definition1.1, Lemma1.3 and explicit normal forms pp2–3; Conjecture6.2 p18. Product set is AA, difference set is AA^{-1}, with ALL ordered pairs, repetition allowed. This is not the distinct MSTD-versus-MDTS majority conjecture6.1.

Put r=m-1>=1 and K_m=max(3,2r+1,2^m). Fix n>=K_m. Use a of order2n and b with b²=a^n and ba^i=a^{-i}b. For each j in Z/(2n), set
A_j={a,a²,...,a^r} union {a^j b}.
The two normal-form cosets are disjoint, and a,...,a^r are distinct because r<2n. Thus |A_j|=r+1=m. Distinct j give distinct sets, since their unique nonrotation elements differ. There are exactly2n members of this family.

Compute products by pair type, without enumeration:
(1) rotation–rotation gives {a^u:2<=u<=2r}, of size2r-1 (also valid r=1).
(2) the nonrotation squared is a^n. Since n>2r, it is not in that interval. Thus the rotation part of A_j A_j has size2r.
(3) rotation–nonrotation and nonrotation–rotation give respectively {a^(j+i)b:1<=i<=r} and {a^(j-i)b:1<=i<=r}. Their exponent sets are disjoint modulo2n: equality would force i+i' divisible by2n, but 2<=i+i'<=2r<2n. Each has r distinct elements. The nonrotation product part has size2r.
Consequently |A_j A_j|=4r.

For inverse-products:
(4) rotation–inverse-rotation gives {a^u:-(r-1)<=u<=r-1}, of size2r-1, since its width2r-2<2n. It already contains1. The nonrotation–inverse-itself adds only1.
(5) (a^j b)^{-1}=a^(j+n)b, so the mixed inverse-products give {a^(j+n+i)b:1<=i<=r} and {a^(j+i)b:1<=i<=r}. They are disjoint modulo2n: i'-i cannot equal n modulo2n because |i'-i|<=r-1<n. Each has r elements.
Thus |A_j A_j^{-1}|=(2r-1)+2r=4r-1<4r, and EVERY A_j is MSTD.

It follows that S_Dic_(4n)(m)>=2n. Finally n>=2^m, so 2n>=2^(m+1)>2^(m/2) for m>=2. This proves the full printed assertion, with an explicit threshold, by ordinary symbolic mathematics only. All integer n, including even n, are covered; all m>=2, including2, are covered. No sampled computation, enumeration, CAS or formal execution was used. The mechanism is a one-element cardinality excess, not a count inferred from one example or from generic group translation (which need not preserve MSTD in a nonabelian group).

Source-own comparison: Theorem1.4 proves m=2; Theorem1.6 proves m=3 for odd n. Neither supplies the all-m argument. Theorems1.8–1.9 concern m=2n, a moving-size regime with a length-n rotation progression and n nonrotations, not this fixed arbitrary-m regime. They do not furnish a complete all-m target bridge merely by changing notation. The original explicitly proposes6.2 for every m>=2. Actual source body passages read; no final/correction equivalence or absence established. No material figure is used in this proof; source tables were text-read, not independently recomputed or visually certified.

Prior reconciliation:869 exact completed allowlisted unprotected files read after component filtering. Exact source-neighbor373069 concerns dihedral majority counts and bounded historical experiments; it is NOT this target and no old experimental artifact was opened or reused. 338640 concerns a different source and is separate. All prior accepted scopes are trusted; no certificate audit. No exact target historical disposition authenticated. This is bounded documentary comparison, not a full96-family independent mathematical review.

Actual Ascoli etal2210.00669v1 pp2–4: generalized dihedral semidirect-product law and formula(3), Theorem1.8 (fixed-size MSTD vs MDTS abundance), small-size Lemmas2.1–2.2 statements and large-size Lemma2.3 proof read. Generalized dihedral groups have involutive flips; the dicyclic b²=a^n shift changes the mixed inverse-products. The excerpted theorem does not itself settle the present all-n dicyclic target. No complete routine adaptation exclusion established from that work; full Section3 abundance proof and final2026chapter unread. No claim that no related arithmetic-progression construction is printed elsewhere.

SPECIFIC PRIOR HOLD: Shankar (search metadata authorship only), Sum and Difference Sets in Generalized Quaternion Groups, PJMS27(4)(2024)773–780, DOI10.17777/pjms.2024.27.4.021, is concretely relevant: search reports a2^(2n) MSTD lower bound. Actual proof, parameter convention (generalized quaternion versus all dicyclic n), subset-size distribution and construction are UNREAD. A total-subset bound does not alone imply the fixed arbitrary-size assertion, but its unread construction may directly subsume this one. DOI request redirected to HTTP; guard rejected BEFORE target dispatch; logger then failed. Entire identified work is now closed to ALL new deliveries, including metadata. No retry/HTTPS upgrade/indirect recovery. NETWORK-STOP.json and get_quaternion.receipt.json preserve this. NO novelty clearance, NO public/routine exclusion justified from search snippets.

Strongest significance case FOR: this proves a deliberate all-m/all-large-n source conjecture with a uniform explicit construction and odd/even coverage, not merely an isolated instance, endpoint repair, or conjecture6.1. Strongest objection: it may be a routine sparse-regime instance of the specifically identified2024 construction; it has no majority/asymptotic proportion conclusion. Shortness alone is not an exclusion. Independent significance adjudication remains unpaid; author assigns no credit.

Current public proof registry ROOT metadata artifacts are inherited504-closed and were NOT retried/reconstructed. Three native searches9queries include actual target and registry terms; no matching search result is not worldwide novelty. Chronology: actual downloaded2026source header dated February9,2026; actual2022dihedral header October3,2022;2024quaternion date only search navigation. No authenticated final/correction/current-head completeness. No independent review or Lean execution. Scientific HOLD; not a qualified survivor; no dispatch or acceptance.

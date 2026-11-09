# Full source question and outcome

Outcome: UNRESOLVED; credit zero. This is research on one fresh lead, not a proposal to count any of the calculations below.

Pierre C. Bellec and Tobias Fritz, *Optimizing over iid distributions and the Beat the Average game*, arXiv:2412.15179v5 (12 September 2025), Conjecture 5.1, PDF pp19–20:

Let M be all Borel probability measures on [0,infinity). For each mu in M let X1,X2,X3,X4 be independent with common law mu. Put

    C = sup_{0<p<1} p(2-p)/(1+p+p²+p³).

The assertion is sup_{mu in M} P(X1+X2+X3<2X4)=C. Strict inequality, independence, common distribution and nonnegativity are essential. There is no continuity, density, moment, finite-support or bounded-support hypothesis on mu. C is approximately 0.4006953723, not exactly the decimal 0.400695. Proposition 4.1 supplies the lower bound; the unproved task is the universal upper bound. The unique maximizing p is the root in (0,1) of 2-2p-3p²-4p³+p⁴=0. Its derivative is negative on (0,1), so the root is unique. The source already gives this optimization.

The source's other general attainability and fair-coefficient questions are not claimed solved or investigated as separate outcomes. No correction of the printed repeated X2 in Problem 5.3 is pursued.

# Exact source and chronology

The initial arXiv submission was 19 December 2024. The accessible history lists v2 on 22 December 2024, v3 on 29 March 2025, v4 on 1 April 2025 and v5 on 12 September 2025. The current unversioned PDF is byte-identical to explicitly pinned v5 (501269 bytes, SHA256 c2745940a67673619e78901de9ad1bbf14b681c7540bf1805aebae9205555a3e). The abstract metadata oddly says “v6: incorporated referees' suggestions”, while its submission history and version URL say v5. Both explicit v6 abs and PDF return 404. Thus “latest” here means latest accessible primary version, not an assertion that a sixth body was read.

The published article is *On Maximizing the Probability of a Linear Inequality between iid Random Variables*, DOI 10.1080/00029890.2026.2702871, online 7 August 2026. Search-accessible publisher abstract reports the same 0.400695–0.417 bounds and conjecture; direct full-body HTTP returns 403. No bypass was attempted. Published-body equivalence is NOT certified.

MathOverflow question 474916 and complete fetched answer page contain the authors' edited December2024/April2025 bounds and Vincent Yu's answer 484853 optimizing p away from 1/2. That improvement is already in v5. The author-hosted 2026 optimizing_iid.pdf slides still state this conjecture and the same bounds. Bellec's 13 December 2025 comment on Tao's primary blog page describes the existing upper-bound certificates and suggests stronger MILP searches; it supplies no limiting proof. The superficially promising “three-atom optimizer” claim in that blog is explicitly corrected after Tao points out its incompatibility with known bounds. It is not adopted as a public resolution. These public bodies predate this lane; none of their constructions is a new result here.

# Early history and classical screens

Before downloading the source, work.py queried complete retained original SUMMARY/discovery/PROOF/review/DECISION bodies for 2412.15179, DOI suffix2702871, Bellec, Fritz, and the exact title. Zero hits in 1025 unique bodies. A second expanded complete-body pass, including Beat the Average, 474916, 484853 and400695, returned zero in1029 bodies. The increase reflects concurrent new/changed originals, not a fresh massive inventory. Both passes query the complete ledger and prior-campaign-context too. Paths, hashes, changed paths, and no-cutoff receipts are retained.

Coverage reuses r137's original-role aliases, themselves qualified by r133, and refreshes immediate batch lane originals. It includes retained r111–r113 scientific reports and imposes no entire-lane exclusion. New nested reports outside the retained set and new old-campaign reports outside immediate batch lanes are not covered. Filename/format/role filtering is not semantic completeness; Unicode aliases, paraphrases, source-only mentions and unlisted scientific formats may escape. A zero lexical result establishes no worldwide freshness. No prior matching body existed to reopen under these patterns. The r137 receipt and r133 alias archive hashes are recorded as dependencies, not independently rebuilt.

Alon–Yuster, *The 123 theorem and its extensions* (1995), actual author PDF Theorems1.1–1.3, Lemma2.1, Corollary2.2 and Proposition2.3 were read. Their argument deletes a point with maximal local neighborhood mass, derives the pair-count bound, and averages over iid samples. Kovačec–Moreira (2014), actual preprint Theorems1–2 and Proposition2, rewrites the corresponding two-variable inequalities as copositivity of a quadratic matrix kernel and uses an interval-neighborhood partition. These are genuine methodological antecedents, not the same four-variable theorem. Neither inspected theorem has coefficients or a reduction that supplies the quartic bound below. No claim that all classical subsumers are excluded is made.

# Mathematical investment and precise obstruction

Write S(nu)=P_nu(X1+X2+X3<2X4), E(nu)=P_nu(X1+X2+X3=2X4). Source Proposition3.3 proves that, for every nu and epsilon>0, an iid law mu achieves at least S(nu)/(1-E(nu))-epsilon when E(nu)<1, by using a sufficiently separated series of independent copies. Thus a finite rational law with S/(1-E)>C would refute the full conjecture, even if its direct S is below C. This is why the experiments optimize that ratio. The renewal argument is SOURCE mathematics, not credited here.

For finite support a0,...,an and weights w_i>=0 summing to1, put

    T_C(a,w)=C*(sum w_i)^4
       - sum_{i,j,k,l} (1[a_i+a_j+a_k<2a_l]
                       +C*1[a_i+a_j+a_k=2a_l])*w_i*w_j*w_k*w_l.

A full proof would follow from T_C>=0 for every n, every nonnegative real support a, and every nonnegative w. Conversely the conjecture and Proposition3.3 force this inequality, including its equality term. Hence this is an equivalent finite-support certificate target, not an established certificate.

To justify passage from finite support to arbitrary laws without silently excluding atoms: sample m iid points from mu and let nu_m be their empirical law. In sampling four indices from nu_m, the probability of repeated indices is at most6/m. Conditionally on four distinct indices the corresponding sampled points are iid mu. Therefore E[S(nu_m)] >= (1-6/m)S(mu). A universal finite-support S<=C implies S(mu)<=C on letting m tend to infinity. This is the source's sampling principle in another form; no compactness or continuity across the strict boundary is needed.

I attempted an atom-deletion induction in the style of Alon–Yuster. The quartic kernel's derivative is a cubic that mixes a point's three roles on the left with its role on the right. Maximal interval-neighborhood mass does not compare those contributions. Unlike the pair-distance argument, there is no supplied cover of those cubic threshold regions by a fixed collection of smaller regions with the required sharp algebraic coefficient. Writing a stationary equation or noting quartic copositivity does not establish its sign.

For a concrete alternate-support attack, set a0=0, a_i=1-2^{-i} for1<=i<=N, w0=p and sum_{i>=1}w_i=s=1-p. Let T_k=sum_{j=k}^N w_j. Direct classification gives

    S=p³s+3p²s²+3p*sum_k w_k*(s²-T_k²)
      +w1³*sum_{k>=3}w_k
      +3w1²*sum_{j>=2}w_j*sum_{k>=j+2}w_k,
    E=p⁴+3p*sum_k w_k³
      +w1³*w2+3w1²*sum_{j=2}^{N-1}w_j*w_{j+1},

with empty sums and missing w2 equal to zero. Explanation: with one zero, min(i,j)<k is exactly the winning condition for the positive pair against a_k. With no zeros, the left triple must contain at least two copies of a1=1/2; the remaining index j wins precisely when k>=j+2. Equality occurs at k=j+1, plus the all-same positive triple with one zero. This separates genuine finite all-positive wins from the author's asymptotic construction rather than dropping them as small.

Seven complete rational fourfold enumerations (N=2,...,8, p=47/100) verify both S and E formulas exactly. These involve 15316 ordered tuples in total. Thirteen additional rational formula evaluations use p=474346/10^6 and N up to1024; large N values use the formula, not brute-force enumeration. In particular N156 exceeds2/5, recovering a known source effect rather than refuting the latest conjecture.

The floating search optimizes the full quartic ratio on four fixed dyadic supports of sizes6,10,16,24 and twelve seeded integer supports of sizes6,8,10, three starts each,140 mirror-ascent updates with bounded backtracking. Support comparisons and monomial incidence are exact rational/integer; optimized weights and objective evaluation are floating. The best observed ratio is0.39677767404588604. This is only a finite local search, with no global-optimality guarantee and no search over all support cells or growing-depth geometry. No finite check is called a proof.

Strongest objection: the desired sharp all-support quartic inequality remains completely unproved. Good dyadic asymptotics and local optimization cannot exclude a different multiscale support or an entirely different law. The classical quadratic proofs do not close this bridge.

Explicit falsifier: supply finite nonnegative rational support and rational probability weights for which the exact S/(1-E) exceeds C, verified with an isolating interval for the algebraic C. Source Proposition3.3 then supplies an ordinary full-scope refutation. No such data were found. Alternatively a universal, support-independent certificate for T_C would close the upper-bound bridge. No such certificate is supplied.

# Registry observation and access limits

Omega observed at23:44UTC: a19a578cd06b57a4ea4d287cb0df92f9085117ae. Compared with last qualified aa026efa802f4361758b827d6b68231ac353948f: ahead6, behind0, merge-base equalsbase, all6 commits returned, but300 files means the comparison is capped. This failure is preserved in registry-delta-receipt.json and not reclassified as uncapped.

To recover bounded relevant-body coverage without rebuilding a400k-file inventory, a direct nonrecursive-tree traversal compares only changed hashes in Blueprint,Library,Problems, plus rootREADME.md. Fourteen tree requests, none truncated, identify exactly three changed Markdown paths in those scopes. Their pinned actual bodies were fetched and read: SphereBrouwerObstruction, SphereOrthogonalityCover, and feldmanwilce2026spherecovers. They concern noncontractibility and orthogonality-free sphere covers, not iid linear inequalities. This closes that fixed interval ONLY for those source-facing Markdown scopes. It excludes Meta digest atoms, formal code, non-Markdown and other root directories; it is not repository-wide semantic clearance. Full historical body coverage is inherited only with the r133/r136/r137 qualifications; no new blanket historic clear is asserted.

OpenAI observed SHA7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, unchanged from supplied qualified observation. Its head is an observation, not a body-clearance proof. Searches using source ID, authors, exact conjecture label, and registry domains yielded no exact new resolution; snippets and search absence are discovery aids only. We do not chase a later head after this fixed observation.

All successful raw HTTP bytes, full URLs, real retrieval UTC, byte sizes and SHA256 values are in http.jsonl and provenance.json. Access failures (publisher403, v6 and unused author/publications URLs404) remain explicit. PDF text extraction can lose typography; no figure-dependent or OCR-based mathematical assertion is used. Search-result metadata is not represented as locally hashed primary bytes.

Initial broad shell inventory output and some combined reads were truncated; they do not support absence or completeness claims. The actual history queries read entire bodies without match cutoffs; focused later reads supply the stated theorem/proof scopes. Initial NumPy/SciPy import failed with an OpenBLAS allocation error under unchanged AS cap; checks-first-failure.log is preserved. The successful replacement uses only Python standard-library arithmetic and mirror ascent.

The helper guard is unchanged. AS and sampled process-group RSS512MiB, CPU210s, wall230s; nominal40ms samples can miss between-sample peaks and exclude processes that leave the monitored group. No cap was raised. Ledger/prior snapshots are frozen context; context-NEXT.md is a mutable planning snapshot, excluded from scientific-freeze but included in finalmanifest. No external source assertion depends on NEXT remaining byte-identical.

No PROOF.md, Lean, manuscript, count change, git operation, child, public mutation or browser tab. Root investment clearance is not requested: full ordinary resolution is absent.

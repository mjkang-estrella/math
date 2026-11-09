# Literature verification — status of the multiplicative persistence conjecture (base 10)

**Subagent D (literature verifier).** All items verified against primary sources fetched on **2026-10-19**.
Each section: VERDICT → exact quotes → URLs → synthesis.

**Two corrections to the task brief (from Perez–Styer, Involve 8 (2015) 439–446):**
> "Sloane [6] in 1973 showed, however, that no number less than 10^50 has persistence 12; this was extended in 2001 by Carmody [2] to 10^233, and in 2010 Diamond [3] extended it to 10^333, while we extend it to 10^1500."

1. The 10^50 → 10^233 → 10^333 → 10^1500 lineage is **Sloane (1973), Carmody (2001), Diamond (2010), Perez–Styer (2015)**. **No "R. Spira" appears anywhere** in OEIS A003001, MathWorld, Wikipedia, BCGN, or Fonga — the remembered name appears to be a conflation (likely with Sloane himself).
2. The 10^233 bound is **Phil Carmody (2001, NMBRTHRY mailing list)**, per MathWorld: "There is no number < 10^233 with multiplicative persistence > 11 (Carmody 2001; updating Wells 1986, p. 78)."

---

## 1. OEIS A003001 — VERIFIED

**URL:** https://oeis.org/A003001 (entry version `%I A003001 M4687 #203 Jun 28 2026 15:47:49`)

Sequence (%S–%T): `0, 10, 25, 39, 77, 679, 6788, 68889, 2677889, 26888999, 3778888999, 277777788888899`.

**Conjecture attribution:** author N. J. A. Sloane; first comment is `%C A003001 Probably finite.` The origin is Sloane's 1973 note (%D: "N. J. A. Sloane, The persistence of a number, J. Recreational Math., 6 (1973), 97-98"). **Not Erdős** — MathWorld: "Erdős suggested ignoring all zeros and showed that at most c ln ln n steps are needed to reduce n to a single digit, where c depends on the base (Guy 1994)" (the zero-*ignoring* variant).

**Verification bounds (verbatim):**
- Chaffin, Sep 29 2016: "The following are true of all p(n) < 10^20000:" … "All p(n) between 10^140 and 10^20000 have a persistence of 1, meaning they contain a 0 digit. (End)" — with "The largest p(n) with P(p(n))=10 is 2^4 * 3^20 * 7^5. The only other such p(n) known is p(a(11))=2^19 * 3^4 * 7^6."
- Radcliffe, Mar 22 2019: "Benjamin Chaffin's comments imply that there are no more terms up to 10^20585."
- Tim Peters, Sep 19 2023: "New lower bound: if a(12) exists, it must be > 2.67*10^30000." … "A long computer run checked N=30000, a bit over 36*10^12 candidates." Also: "the digit products all contain at least one zero in their last 306 digits."

**Synthesis.** The current entry (edited as recently as June 2026) still flags the sequence "Probably finite", i.e. the conjecture is open. The record bound is Peters' 2.67×10^30000; Chaffin's 10^20585 (via Radcliffe) and the peer-reviewed 10^1500 of Perez–Styer are the earlier rungs. Note the entry's reduced-number table: only **2** reduced numbers of persistence 10 and **2** of persistence 11 are known, both ending in digit 0.

## 2. Wikipedia "Persistence of a number" — VERIFIED

**URL:** https://en.wikipedia.org/wiki/Persistence_of_a_number

Exact claim: **"In base 10, there is thought to be no number with a multiplicative persistence greater than 11; this is known to be true for numbers up to 2.67×10^30000."** and "such numbers are believed not to exist, and would need to have over 30,000 digits if they do exist."

**Cited sources for the claim:** [1] Sloane (ed.), "Sequence A003001", OEIS; [2] Eric W. Weisstein, "Multiplicative Persistence", MathWorld. Bibliography includes: "Guy, Richard K. (2004). *Unsolved problems in number theory* (3rd ed.). Springer-Verlag. pp. 398–399. … Zbl 1058.11001."

**Synthesis.** Wikipedia states the conjecture as a *belief* ("thought to be") with a *proved* verification bound 2.67×10^30000 — consistent with OEIS. The two inline citations are exactly OEIS + MathWorld.

## 3. Brier–Clavier–Gutsche–Naccache (arXiv:2110.04263, v1 8 Oct 2021) — VERIFIED

**URLs:** https://arxiv.org/abs/2110.04263 · https://arxiv.org/html/2110.04263v1

**EXACTLY what is proved (abstract, verbatim):** "This paper proves that the conjecture holds for all odd target values: Namely that if Δ(n)∈{1,3,7,9}, then Ξ(n) ≤ 1 and that if Δ(n)=5, then Ξ(n) ≤ 5." Plus: "Naturally, we overview the difficulties currently preventing us from extending the approach to (nonzero) even targets."

**Method.** Backward "antecedent trees" A_d per terminal digit d; they prove the candidate graphs B_d are complete for odd d by reducing completeness to finitely many exponential Diophantine equations of the shape 2^h·(10^{a₀} + 18·Σ c_i·10^{a_i}) + τ_h = 3^u·7^w, solved by a modular-lifting algorithm (residues mod m₁₂ = (10^12−1)/(3³·7), then lifted to m₂₄, m₄₈). This is where the **2-adic valuations of infinite families** (fixed digit multiplicities + arbitrarily many 1s) enter.

**Left open.** Nonzero even targets d ∈ {2,4,6,8} (their §5, verbatim): "Given that each a_i is defined modulo 12, it seems totally out of reach to exhaust 12^30 ≃ 2^107 tuples in the most favorable case." Complexity table (their Table 3): d=2: 33 vertices/1117 equation families/30 terms; d=4: 9/1062/32; d=6: 84/6377/37; d=8: 51/4774/45. Their approach "led to … Conjecture 2" (the uniform-v₂ conjecture). Footnote: "The particular case d=0 can not be treated by our method."

**Synthesis.** BCGN settles *odd terminal digits only*; terminal 0, 2, 4, 6, 8 remain open — and the record trajectory 277777788888899 → … → 0 ends in 0, so the headline conjecture P ≤ 11 is not yet covered even for the known record. Note BCGN itself is, per Fonga's bibliography, still an arXiv preprint (no journal version cited).

## 4. Fonga, "The Multiplicative Persistence Conjecture: Resolving the 2-Adic Obstruction for Nonzero Even Targets" (arXiv:2608.27802) — VERIFIED (the critical item)

**URLs:** https://arxiv.org/abs/2608.27802 · https://arxiv.org/html/2608.27802v1

**Status:** single author **Patrick Nyadjo Fonga** (Dept. of Mathematics and Statistics, Bowling Green State University, Ohio); **v1 only, submitted Fri 28 Aug 2026**, 14 pages, math.NT (MSC 11A63; 11A07, 11Y16). **No journal reference ⇒ unrefereed preprint** (as of 2026-10-19).

**PRECISELY what is proved.** BCGN's Conjecture 2 ("Conjecture B"): for the family 𝒜₁₀(ν) of decimals with fixed digit counts ν₂,…,ν₉ of digits 2–9, arbitrarily many 1s, and no 0s, "there exists a constant C such that v₂(n) ≤ C for every integer n in this family." Verbatim: "In this paper, we provide a proof for Conjecture B; see Corollary 3.2." Concretely:
- **Theorem 3.1** (general): for base b ≥ 3, prime p | b, sup_{x∈𝒜_b(ν)} v_p(x) < ∞, with explicit bound v_p(x) ≤ ⌊ρ_p(ν)·λ^q + log_p B(ν)·(λ^q−1)/(λ−1)⌋, λ = log_p b / v_p(b), B(ν) = 1+(b−1)Σ(d−1)ν_d.
- **Corollary 3.2** (base 10, p=2): v₂(x) ≤ ⌊ρ·c^q + ((c^q−1)/(c−1))·log₂B⌋ with c = log₂10, ρ ∈ {0,1,2,3} by which even digits are present.
- **Theorem 4.1**: an exact *finite recursive procedure* (𝔙) computing the optimal max v_p for each digit multiset (worked example D={4,4,7} → max v₂ = 7, attained at 111744 = 2⁷·3²·97).

**Is the full conjecture resolved? NO — only reduced to a finite computation.** Abstract: "In base 10, combining our bound with the method of Brier, Clavier, Gutsche, and Naccache yields a finite algorithm for a further analysis of each nonzero even terminal digit." Body (§5): BCGN's candidate backward graphs B_δ would give the persistence bounds *if* complete; "its completion would determine whether the proposed backward graphs are complete." And the decisive sentence: **"The purpose of the present work is to provide the missing theoretical bound and to reduce this verification to a finite, terminating procedure. Although carrying out the full computation lies beyond the scope of this paper, the formulation developed here is intended to make that next step accessible."**

**Synthesis.** This paper resolves the *2-adic obstruction* (BCGN Conjecture 2) in full generality (every base b≥3, every p|b) and makes the even-target case a finite computation per terminal digit — but **it does not prove the conjecture, does not prove B_δ = A_δ for any even δ, and did not run the computation**. Terminal 0 is not addressed at all. Anyone citing "the conjecture is resolved" from this preprint would be over-claiming; it is a genuine but partial advance, unrefereed, seven weeks old.

## 5. Senge & Straus (1973) and Stewart (1980) — digits of powers — VERIFIED

**URLs:** https://link.springer.com/article/10.1007/BF02018464 · survey quote: https://irma.math.unistra.fr/~bugeaud/travaux/Ribfinal1.pdf (Bugeaud–Cipu–Mignotte)

**Citations (from the survey's reference list):** [12] H. G. Senge and E. G. Straus, "PV-numbers and sets of multiplicity", *Period. Math. Hungar.* **3** (1973), 93–100. [13] C. L. Stewart, "On the representation of an integer in two different bases", *J. reine angew. Math.* **319** (1980), 63–72.

**Statement (survey, verbatim):** "In 1973, Senge and Straus [12] proved that the number of integers, the sum of whose digits in each of the bases a and b lies below a fixed bound, is finite if, and only if, a and b are multiplicatively independent. Their proof rests on the Thue–Siegel–Roth theorem and, hence, is ineffective. Using Baker's theory of linear forms in logarithms, Stewart [13] succeeded in establishing an effective version of Senge and Straus' theorem." Stewart's effective form bounds integers m > 25 with digit sum ≤ c in *both* bases via log log m ≲ 2^{c+1}·log log log m; his "Theorem S" gives, for linear recurrences U_n (incl. 2^n), ≥ ~log n / log log n nonzero digits in base b.

**Consequences.**
- **KNOWN:** 2^n has *unboundedly many nonzero decimal digits* (2^n has one nonzero digit in base 2; Senge–Straus/Stewart force the base-10 nonzero-digit count to → ∞, effectively).
- **UNKNOWN:** whether 2^n *contains the digit 0* for all sufficiently large n. OEIS A007377: "It is an open problem of long standing to show that 86 is the last term."

**Directly relevant to our project** — de Faria & Tresser (arXiv:1307.1188), Conjecture 1: "There exists a positive integer k₀(q) such that, for all k ≥ k₀(q), the base q expansion of any product of k digits greater than 1 for base q has at least one digit equal to zero." Their Conjecture 1a (base 3, zeros in 2^k) is "reminiscent of a conjecture by Erdős". This is the literature form of our SPEC's zero-digit reduction: the conjecture hinges on zero digits appearing in 7-smooth numbers.

**Synthesis.** Unboundedly many *nonzero* digits is a theorem; *presence of a zero digit* is not provable by these methods and is precisely the open gap. Our master reduction (conjecture ⇔ "every 7-smooth number's chain hits a zero-digit product") sits exactly on this known/unknown boundary.

## 6. M. Sghiar, "Persistance d'un nombre" (IOSR-JM 2017, HAL hal-01445353) — VERIFIED

**URLs:** https://hal.science/hal-01445353 · PDF: https://hal.science/hal-01445353/document

**Confirmed claim (abstract, verbatim):** "For a radix of 10, I will show that there is no number with a multiplicative persistence ≥ 12." ("Je démontre qu'en base 10, il n'existe aucun nombre dont la persistance multiplicative est supérieure ou égale à 12.")

**Venue:** "Journal Articles IOSR Journal of Mathematics(IOSR-JM) Year : 2017", Vol. 13, Issue 1, Ver. III (Jan.–Feb. 2017), **PP 39–40** (2 content pages); HAL hal-01445353 v4, 21 Feb 2017. IOSR-JM is a pay-to-publish outlet not indexed by MathSciNet/ZbMATH.

**The fatal step (verbatim, final page):** "Si n ≤ … alors ϕ₁₁(n) ≤ 9. **(Testé sur ordinateur)**. D'où le résultat." — the finite case of the "proof" is justified *only* by "(Tested on computer)", with no code, bound, or certificate; earlier lemmas are disposed of with "Preuve : Facile à voir" ("easy to see").

**Why the community does not accept it:** it is cited by **nobody** in the subsequent literature — the full reference lists of BCGN (2021), Fonga (2026), Perez–Styer (2015), Lamont-Smith (2021), de Faria–Tresser (2014) contain no Sghiar; OEIS A003001 and MathWorld still present the problem as open; and DeepMind's formal-conjectures repo lists it as an open conjecture (item 9). A 2-page note whose decisive case is an undocumented computer test cannot carry the claim.

**Synthesis.** The paper exists, claims the full conjecture, and is formally "published", but it has zero scholarly traction and contains a proof gap disguised as a computer test. Our project should treat the conjecture as open and Sghiar's note as a cautionary example of exactly the reporting standard SPEC ground rule 3 demands.

## 7. T. Lamont-Smith, J. Integer Seq. 24 (2021), Article 21.6.7 — VERIFIED

**URLs:** https://cs.uwaterloo.ca/journals/JIS/VOL24/Lamont/lamont5.html · https://cs.uwaterloo.ca/journals/JIS/VOL24/Lamont/lamont5.tex

Verbatim: "In base 10, the largest persistence that has been found is s = 11 for the number n = 277777788888899, which is given in A003001." Its Table 15 ("Persistence in base 10") lists rows s = 1…11 with **11 → 277777788888899**; its Table 4 ("Maximum persistence and number of digits for different bases") gives **b = 10 → s_max = 11 (k = 15 digits)**, vs e.g. b=11 → 13, b=13 → 15, b=19 → 18, b=23 → 19.

**Synthesis.** A peer-reviewed (JIS) secondary confirmation that base 10's max *found* persistence is 11, with the per-base table the task asked about. The paper also studies *absolute* persistence (unbounded across bases) — no contradiction with the per-base conjecture.

## 8. Guy, *Unsolved Problems in Number Theory*, §F25 — VERIFIED

- OEIS A003001 (%D): "R. K. Guy, Unsolved Problems in Number Theory, Springer, 1st edition, 1981. See section F25."
- MathWorld: "Guy, R. K. 'The Persistence of a Number.' §F25 in *Unsolved Problems in Number Theory, 2nd ed.* … pp. 262–263, 1994."
- Perez–Styer (2015): "intrigued by the mention of the problem in Richard Guy's Unsolved Problems in Number Theory book (**Problem F25** in [5])", [5] = "Guy, Richard, Unsolved Problems in Number Theory 3rd edition, Springer 2004".
- Wikipedia bibliography: 3rd ed. (2004), **pp. 398–399**, Zbl 1058.11001 (same page range is cited by Sghiar's reference list).

**Synthesis.** The problem is §F25, "The Persistence of a Number", in all three editions (1st 1981, 2nd 1994 pp. 262–263, 3rd 2004 pp. 398–399) — an *Unsolved Problems* book presenting it as open; BCGN likewise cite it as the source of the "famous conjecture". VERIFIED open in the 3rd edition, pp. 398–399.

## 9. Sweep for 2022–2026 claimed proofs/disproofs — VERIFIED: still open

- **arXiv full-text search "multiplicative persistence"** (API, 2026-10-19): 20 results total; the only math.NT-relevant ones are de Faria–Tresser 2013 (1307.1188), BCGN 2021 (2110.04263), Fonga 2026 (2608.27802). No other claimed proof or disproof in 2022–2026. (http://export.arxiv.org/api/query?search_query=all:%22multiplicative+persistence%22)
- **MathOverflow #455497** "Multiplicative Persistence — Highest persistence found?" (2023), answer: "First, to your direct question: 'Is the record still 11', the answer is 'yes', according to a variety of sources (MathWorld, Wikipedia, OEIS A003001). … The comments in OEIS claim various lower bounds on the size of a number of persistence 12: a comment in 2019 claims 10^20585, and a comment in 2023 claims 2.67×10^30000." (https://mathoverflow.net/questions/455497)
- **google-deepmind/formal-conjectures issue #7184** "Formalize the multiplicative persistence conjecture" — open conjecture slated for formalization (2025/2026). (https://github.com/google-deepmind/formal-conjectures/issues/7184)
- OEIS A003001 still edited **June 2026** with "Probably finite"; Kevin McElwee's Medium post titled "Multiplicative persistence is solved" (2019) is in fact an *algorithm* write-up (OEIS links it as "An algorithm for multiplicative persistence research") — not a proof.

**Synthesis.** Outside item 4, no accepted (or even seriously proposed) resolution of the full conjecture exists in 2022–2026. The ecosystem still treats it as a canonical open problem.

## 10. Largest known power of 2 with no digit 0 — VERIFIED (cross-check for zero_free_scan)

**URLs:** https://oeis.org/A238938 (the powers) · https://oeis.org/A007377 (the exponents) · https://oeis.org/wiki/Zeroless_powers · https://blog.tanyakhovanova.com/2011/02/86-conjecture/

- **A007377** (exponents k with 2^k zero-free): 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 24, 25, 27, 28, 31, 32, 33, 34, 35, 36, 37, 39, 49, 51, 67, 72, 76, 77, 81, **86** — 36 terms. Comment: "It is an open problem of long standing to show that 86 is the last term." Example (Sloane, Feb 10 2023): "Here is 2^86, conjecturally the largest power of 2 not containing a 0: **77371252455336267181195264**" (26 digits).
- **A238938**: "Powers of 2 without the digit '0' in their decimal expansion", a(n) = 2^A007377(n); "Conjectured to be finite and complete." (b-file: 36 terms, Daniel Mondot.)
- **A020665**: "n^a(n) is (almost certainly) the largest power of n not containing a zero" — table gives a(2) = 86 (also a(4) = 43, a(8) = 27, consistent since 4^43 = 8^27 = 2^86).
- **Khovanova, "The 86-conjecture"** (Feb 2011): "Currently, it has been checked up to the power 4.6·10^7" (per MathWorld's Zero page), i.e. no zero-free 2^k for 87 ≤ k ≤ 4.6×10^7; heuristic expected count beyond → ~0. MSE Q4113204 independently checked to 10^5.

**Synthesis.** The record to beat/cross-check is **2^86 = 77371252455336267181195264**, and its status is *conjectural*: proving 86 is the last zero-free exponent is "an open problem of long standing". Our zero-free 7-smooth sweep should reproduce 2^86 as the largest zero-free pure power of 2 found and note that zero-free 7-smooth numbers are a strictly larger class (products of digits, not just powers of 2) — matching de Faria–Tresser's Conjecture 1 rather than the 86-conjecture alone.

---

## State of the art as of today (2026-10-19)

The base-10 multiplicative persistence conjecture — every positive integer reaches a single digit in ≤ 11 digit-product steps — **remains open**, with record 277777788888899 (persistence 11, OEIS A003001) and no persistence-12 example known. Computationally, none exists below **2.67×10^30000** (Tim Peters, Sep 2023, ~36×10^12 candidate digit strings; peer-reviewed rungs: Sloane 1973 → 10^50, Carmody 2001 → 10^233, Diamond 2010 → 10^333, Perez–Styer *Involve* 2015 → 10^1500). The strongest theory is Brier–Clavier–Gutsche–Naccache (arXiv:2110.04263, 2021), which proves the conjecture for **odd terminal digits** (1,3,7,9 → persistence ≤ 1; 5 → ≤ 5) via backward graphs plus exponential Diophantine equations, leaving even targets 2,4,6,8 (and 0) open behind their 2-adic "Conjecture 2". Fonga (arXiv:2608.27802, v1, 28 Aug 2026, **unrefereed**) proved that 2-adic conjecture in general (explicit and computably optimal uniform v_p bounds for digit-multiset families in any base b ≥ 3, p | b), thereby **reducing each nonzero even terminal digit to a finite computation that nobody — including the author — has carried out**; the conjecture is *not* resolved. Structurally, the open core is a zero-digit statement about products of digits (7-smooth numbers, de Faria–Tresser's Conjecture 1): 2^86 = 77371252455336267181195264 is the largest known zero-free power of 2 and proving it is the last is "an open problem of long standing" (A007377), while the only claimed full proof (Sghiar 2017) is a 2-page IOSR-JM note whose final case reads "(Testé sur ordinateur)" and is cited by no one.

# Source-to-claim map

The paper is standalone: Sections 2–4 prove the integral assertion directly. References are credited for their mechanisms and for the precise boundary of the conclusion. Neither proof-review PASS, contribution-review SUBSTANTIAL, finite controls, nor a catalogue summary is a premise. `source-to-claim.json` provides all 14 interfaces, original paths, exact file and slice hashes, and primary URLs. `checks/input-audit.json` authenticates all 13 inherited source slices. All external PDF/TXT files and the full inputs tree remain excluded from the public ZIP.

## Mathematical interfaces

| Paper location | Source interface | Exact role and limits |
| --- | --- | --- |
| Abstract; §1; §3, (3.3)–(3.4) | Bryant–Kovács 1972, full three pages; Lemma (ii)–(iii), pp. 134–135; author archive link in references | Classical regular-summand criterion and product separating witness. The source assumes a field and uses injectivity of KG in (ii). No integral injectivity is inferred. Formula (3.3) is proved equal to J^{-1} pi_D q^B on every input by a unique basis-preimage argument. |
| §2 | Pinned cyclic `specht-tools.tex`, lines 57–89, `lem:polytabloid` | Inherited ordered alternating blocks. Source is over C. The paper gives its own integral bijection of tabloid and content-word bases, fixes inverse-permutation signs and both actual tableaux, and justifies the triple embedding using freeness over Z. |
| §4, (4.1)–(4.2) | Pinned cyclic `dominance.tex`, lines 126–192, `dom:pair-letter-map`, `dom:square-minimum`, `dom:noncancellation`, `dom:permutation-quotient` | Inherited sum-letter and full square-deficit mechanism. Source scalar is (-1)^H product r!. The paper retains the argument, refines the output by a, and filters a=c; it proves a unique surviving triple with coefficient +1. |
| §3 beta; Lemma 2 and its proof | Ikenmeyer arXiv:1410.6549v2, §§4–5, local text lines 277–420; especially (5.2), lines 360–409 | Entire triangular labeling and row/column uniqueness are inherited. The induction is supplied in full and used after the deficit step. The optional second-use simplification is not substituted. |
| §5 first paragraph | I21 §2.1, lines 45–59; full project-note SHA-256 `607c2c3296b6e020d8f0ae12526ee593ba3369e00fa5c4f393e53ee5b6936b6a` | Previously established complex repeated-row orbit is M^rho. Its factorial scalar is explicitly credited; no unit scalar is inferred over Z. The argument is summarized sufficiently to make the comparison understandable without that internal note. |
| §1; §5 | Harman–Ryba 2023, full text; Thm 1.1; Thm 2.4 local lines 115–163; §3 local lines 176–245 | Published complex occurrence; M^mu tensor S^mu contains M^{C(mu)} over C, with C(rho)=(1^N); already yields complex regular containment when combined with I21. §3/Remark 3.3 already gives every characteristic-2 PIM as a summand. Regular multiplicities are distinguished from occurrence. |
| §5 stipulated square context | Pinned cyclic `dominance.tex`, lines 45–49, `thm:cyclic-saxl` | Every complex irreducible occurs in the specified row/column cyclic square. This is accepted as stipulated upstream context, not proved anew and not used in the integral proof. |
| §5 companion comparison | Pinned universal `introduction.tex`, lines 14–22, `thm:main`; `preliminaries.tex`, `eq:block-specht`, `thm:cyclic-input` | Complex support statements only. Their truth is stipulated; none is promoted to an integral splitting. |
| §5 modular context | Bessenrodt–Bowman–Sutton 2021, pp. 1028–1029/local lines 255–334; §5/local lines 1300–1389, Thm 5.2 | Characteristic-2 projectivity and strengthened square conjecture; earlier framework for HR. No new square theorem is asserted. |
| §5 square boundary | Bessenrodt–Bowman arXiv:2202.03066v3, §3/local lines 330–479, Thm 3.7 | Symmetric/exterior square multiplicity identity, not integral regular cube splitting. |
| Theorem 1 and its proof | Original synthesis of the above, with all steps in §§2–4 | For every m >= 1 the specified tensor has a split regular integral orbit. Functoriality preserves P I = 1 under every commutative unital base change, even nonflat. No saturation, modular semisimplicity, or integral branching premise is used. |

All pinned files use OpenAI math commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Their complete raw URLs appear per interface in the JSON map. Their exact SHA-256 values and quoted source locators are inherited without changing the original contract bytes. The path remapping only identifies the current local copies.

For completeness, inherited contracts for cyclic `band-quotient.tex` lines 32–68 (`lem:sector-induction`) and universal `balance.tex` lines 33–114 (`lem:balance-separation`) are retained and authenticated. These are complex coordinate-sector antecedents inspected for scope; neither is required by the proof. The regular-word isomorphism in §3 is proved directly from a bijective word with distinct letters.

## Frozen provenance and continuation

The candidate, full proof review, and contribution review have respectively the SHA-256 values stated in `source-to-claim.json` and the task brief. Every frozen input still matches `input-manifest.json` (41 entries). The proof and contribution reviews concern the candidate, not this newly typeset manuscript. Independent manuscript review and formal-coverage integration remain pending.

The GLM parent disposition was read as bounded checking history only. Its b-word prose correction is honored: b(i,j)=j is the increasing identity, not reversal. A dropped-coordinate codomain mismatch alone is not claimed to prove regularity failure; the paper makes no such claim. The parent separately demonstrated orbit collisions at m=2,3. No GLM checker is imported or rerun here, and none of its checks is a general proof premise.

No withdrawn arXiv claim is cited as a theorem or proof. This package makes no exhaustive-literature or worldwide-priority assertion. The complex regular conclusion and characteristic-2 PIM occurrence are credited antecedents. The asserted contribution is one integral/every-ring regular-summand package.

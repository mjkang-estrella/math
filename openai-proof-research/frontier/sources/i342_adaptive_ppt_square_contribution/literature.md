# I342 source and contribution comparison

2026-10-13. Reviewer GPT-6.1 Sol (`gpt-6.1-sol`), high reasoning; Standard speed requested, not independently attested. No subagents. Verdict TECHNICAL, not a certificate of a published verbatim duplicate.

## Stipulated OpenAI source and companions

Repository [OpenAI/math](https://github.com/openai/math), immutable commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, commit timestamp from sources/upstream.json `2026-10-08T05:20:00Z`. Author credit from source main.tex: OpenAI; manuscript date September 27, 2026. Source prefix:

    preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/

[foundations.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/sections/foundations.tex), complete: `lem:ppt-stability`, `def:represented-class`, `lem:tensor-closure`, `lem:choi-transfer`. SHA256 `37739b9ff820dd1ed8552073b44f518904c9ee00f8c27f1e83e439034444901c`, 9971 bytes. Non-TP rectangular representing factors and unnormalized vectors are explicit.

[secret-key.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/sections/secret-key.tex), read scopes 1–141, 230–379: `def:distillable-key`, complete `thm:zero-key` statement, complete `prop:operational-extensions` and its proof. SHA256 `54bc7899533396704dc24d06a3208398b488f0648367380164f0ec58374329a4`, 17082 bytes. The theorem covers every C input, arbitrary purification, all normalized comparisons, joint local processing and complete public information. Item 1 of the proposition retains the unhalved 1/5 gap after any positive-probability public conditioning. This explicit source interface is the strongest response to exponentially unlikely Bell simulation; ordinary zero asymptotic key alone is insufficient.

[transcripts.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/sections/transcripts.tex), read 1–65 and 77–220, including FULL `def:protocol` 77–196. SHA256 `06800154e1ad69c0e07edfa56f2e6780acb08bf62bb69288773659fa35df4b6e`, 33090 bytes. This is the actual operational model, not just a catalogue abstract.

[applications.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/build/source/sections/applications.tex), complete: `prop:channel-completion`, proof of `thm:main-channel`. SHA256 `8ba7427a5bfc4bc3e82d446bb322cfbaa6ce2c51b2984acfdae95d77ed2750c4`, 6658 bytes. The source owns the Mat(21) PPT TP Theta with non-EB square. Theta squared is the reviewed zero-key channel; Theta itself is not claimed zero-key.

Catalogue result 272 lists one manuscript. Its companion state, pair, channel and projection constructions are inside the same source, identified through introduction/main/applications. No separate listed companion states the full adaptive channel conclusion in the passages read. This is bounded coverage, not an exhaustive negative novelty assertion. Source geometric/arithmetic proofs were neither needed nor audited under stipulated truth.

## Primary standard machinery

[Christandl–Müller-Hermes–Wolf, *When Do Composed Maps Become Entanglement Breaking?*, arXiv:1807.01266v2](https://arxiv.org/html/1807.01266v2), Annales Henri Poincaré 20, 2295–2322 (2019). Read Lemma I.1(2), IV.A and FULL IV.B (HTML IV.1/IV.2, web lines 462–508), with nearby cone-duality statements. It supplies the transpose-adjoint Choi identity and serial-composite/local-product equivalence with rectangular maps. This deserves credit but does not itself state the adaptive secret-key obstruction. The old equivalence plus Bell filtering removes the need for a new reshuffling operation.

[Xin Wang–Mark M. Wilde, *Resource theory of asymmetric distinguishability*, arXiv:1905.11629v3](https://arxiv.org/html/1905.11629v3#A1.SS2), Phys. Rev. Research 1, 033170 (2019). Read FULL Appendix A.2. It explicitly describes Choi channel realization via postselected teleportation, equations (69)–(70) in HTML. The independent audit converts its unnormalized contraction to normalized Choi/Bell objects, derives probability 1/d^2, amplifies it by arbitrary spectators and proves the actual Stinespring environment identity. The companion channel-box paper, 033169 / arXiv:1907.06306, was an initial lead and is not the credited appendix.

## Alternative comparison routes and limits

[Eneet Kaur–Mark M. Wilde, *Amortized entanglement of a quantum channel and approximately teleportation-simulable channels*, arXiv:1707.07721v3](https://arxiv.org/html/1707.07721v3). Read Definition 1, Section 2.5/Proposition 8, adaptive protocol and purification excerpts, Section 3.4 and Proposition 13. Their amortized input permits arbitrary correlated memories, and deterministic resource simulation can reduce adaptive codes. Those results do not establish deterministic Choi simulation for every channel here or a vanishing key-relevant measure. The exact postselected filter argument uses the source's stronger uniform conditioning property instead.

[Stefan Bäuml–Matthias Christandl–Karol Horodecki–Andreas Winter, *Limitations on Quantum Key Repeaters*, arXiv:1402.5927v2](https://arxiv.org/html/1402.5927v2), Nature Communications 6, 6908 (2015). Read Results resource model and equations (11)–(13). These concern two shared links, a third-party repeater and secrecy after giving its remaining information to Eve. General PPT rate bounds need not vanish and are not a proof for arbitrary adaptive bidirectional inaccessible channel composites. No full supplementary proof audit or direct duplicate is claimed.

## Contribution and parent credit

The full adaptive obstruction is reduced explicitly in analysis.md, preserving initial C states, finite unbounded memories, both directions, arbitrary public-history channel/dimension choices, actual channel environments and every ideal comparison. The parent authored `frontier/iterations/i341-parent-postselection-objection.md`, including the warning about dimension-dependent success weights and terminal acceptance equalization. Both were independently checked here. The simulation ingredients are standard; the decisive uniform zero-key and conditioning theorems and the non-EB example are upstream OpenAI results. I341 supplies a correct alternate proof and useful adaptive interpretation, but no new substantial operation survives the explicit standard reduction. This is the affirmative reason for TECHNICAL, without declaring world priority or an exact published duplicate.

No new full external source body was retained. Full retrieval hashes and exact read limitations are in input-authentication.json and reading-and-failures.md.

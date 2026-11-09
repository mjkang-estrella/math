# Prior-art and registry searches (lane expanded-corpus-r127, 2026-11-03 UTC)

These are web searches through the harness WebSearch tool. Result lists are summarized; "no hit" means only that
these queries returned no resolution.

| # | Query (abridged) | Mode | Relevant finding |
|---|---|---|---|
| 1 | sinkless rotor bidirected cycle recurrent configurations conjecture Chan Levine gcd | standard | only the source; no resolution |
| 2 | rotor network bidirected cycle recurrent component weight conjecture proved | extended | no resolution |
| 3 | "sinkless rotor" "gcd(n,m" OR "Conjecture 8.3" Abelian networks IV | extended | source, AMS Memoir pages, Chan's 2019 Cornell thesis; no resolution |
| 4 | Chan Levine rotor-routing cycle roots of unity 2023–2025 | standard | Chan thesis (fetched: `sources/prior/chan-thesis-2019.pdf`); it has no Conjecture 8.3 and no proof |
| 5 | "strongly e-positive" claw net free conjecture | standard | FHM 2019 (EJC 26(3) P3.51), twinning counterexamples (arXiv:2010.14312; a different FHM conjecture) |
| 6 | "(claw, net)-free" e-positive 2024–2026 | extended | arXiv:2607.21508 (Matherne–Morales, July 2026): claw-free line graphs that are not Schur-positive; both contain nets (their Remark 2.3), so they do not touch 340073/340074. Also arXiv:2607.26364 (Prajapati), WZZ arXiv:2607.27166 (Stanley–Gasharov family) |
| 7 | FHM "net-free" e-positive counterexample 10 vertices / strongly e-positive 2026 | extended | no resolution |
| 8 | strong geodetic K_{m,n} Conjecture 2.4 e(m,n) < 2 | standard | Gledel–Iršič arXiv:1810.04004 (exact formula, Theorem 2.4); no explicit treatment of Conj. 2.4 |
| 9 | discrete cubical homology vanishing without 3- and 4-cycles | standard | Barcelo–Greene–Jarrah–Welker arXiv:1909.02901 (SIAM J. Discrete Math. 35 (2021) 35–54), Theorem 1.1, proves 338749 |
| 10 | Renaudineau–Shaw spectral sequence second page | standard | Chenal arXiv:2312.11919 (Épijournal Géom. Algébrique 10 (2026)): special cases plus a criterion; the general conjecture is open |
| 11 | Katthän Lecture Hall polynomials polynomial | standard | no resolution |
| 12 | Davis state polytope P(l,0,…,0) Delannoy | standard | no resolution |
| 13 | extremal reciprocal algebraic integers octanomial | standard | Stankov (Exp. Math. 2021); no resolution |
| 14 | unimodular eternal Galton–Watson tree dimension α/(α−1) | standard | source only (EJP 2021); no resolution |
| 15 | Ehrenborg conjecture spanning trees bipartite 2024–2026 | standard | **arXiv:2603.17997 (Boon Suan Ho, March 2026): full proof of Ehrenborg's conjecture, formalized in Lean 4** |

Registries
- OpenAI/math `commits/HEAD` = 4eaee87548250b2682affda7d05d947c05554bae (2026-10-30T00:35:35Z), unchanged.
  Screened the cached complete preprints listing `fresh-corpus-r10/sources/registry-preprints.json`
  (sha256 6ac178a0…0305): no rotor, abelian-network or sandpile preprint, and no claw/net e-positivity preprint.
  The one chromatic-quasisymmetric preprint (pinned README and intro fetched to `sources/registry/`) is about
  unit interval graphs.
- Omega trureturing `commits/HEAD` = 6ffa76e4424ce4c0d1048e56afb0724762ed8285 (2026-11-03T09:43:33Z). That commit
  touches only BajnokBeattyOddWrapGaussian* files. Screened root's cached complete D5/Problems trees at b576c901
  (`pdtar-parent-final-r1/registries/omega-D5.body` sha256 e06bf51c…4690, `omega-Problems.body` sha256
  d41f738d…d9f): no reserved ID and no relevant topic. The only "rotor" hits are unrelated word-combinatorics files.
  Limitation: commits between b576c901 and 6ffa76e4 were not enumerated, because this lane is limited to
  /commits/HEAD.

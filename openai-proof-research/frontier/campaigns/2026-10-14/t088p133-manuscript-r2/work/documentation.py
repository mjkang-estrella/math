from pathlib import Path
import shutil,json
r=Path(__file__).resolve().parents[1];p=r/'packet/public';old=r.parent/'t088p133-manuscript-r1/packet/public'
for name in ['README.md','COVERAGE.md','HANDOFF.md','PROVENANCE.md','RIGHTS.md','source-reading-records.json']:
 shutil.copy2(old/name,p/'provenance'/('r1-'+name))
readme=(old/'README.md').read_text()
readme=readme.replace('manuscript round 1','manuscript round 2').replace('This is a complete mathematical **draft implementation**, not an independent manuscript review, acceptance-ready package, portable release, or publication. Formal integration is pending.', 'This is the **final-manuscript implementation for independent review**. The completed independently reviewed scoped formal support is integrated. This is not an independent manuscript review, acceptance-ready package, portable release, or publication.')
readme=readme.replace('final draft PDF','final implementation PDF').replace('a later immutable draft; no active formal files are read here','independent final manuscript review and later parent decisions')
readme=readme.replace('`main.tex`, `references.tex`, `witness-tables.tex`','`main.tex`, `references.tex`, `witness-tables.tex`, `formal-appendix.tex`')
readme=readme.replace('`source-reading-records.json`: source hashes and actual read extents; body files remain private.', '`source-reading-records.json`: current source hashes and read/reuse extents; unchanged r1 records are separately labelled historical; body files remain private.')
readme=readme.replace('The bootstrap fetches', 'For this round the authenticated r1 engine and populated cache were copied locally, preserving their metadata/rights; no download was needed. The optional bootstrap fetches')
readme += '''
## Reviewed formal support and portable reproduction

`formal/implementation/` and `formal/review/` contain UNCHANGED public sources, notices, pins, coverage, historical scripts and receipts. `formal/origin.json` records every origin/hash; `formal/historical/` retains the original FINAL/MANIFEST/outsideREPORT. Pending-at-submission statements inside these unchanged records are historical. Current coverage is Appendix C and COVERAGE.md: 21 support declarations (3 definitions/18 theorems), 20 controls, 15 independent contracts/use-site declarations. Only propext, Classical.choice, Quot.sound occur. The parent adopted PASS_SCOPED_SUPPORT with no repairs; no full theorem is formalized.

From a fresh writable copy of this manuscript root:

```sh
python3 -B packet/public/support/formal_reproduce.py \\
  --lean /absolute/path/to/lean-4.34.1/bin/lean \\
  --cache /absolute/path/to/trusted/.lake/packages \\
  --output "$PWD/build/work/formal-fresh"
```

This NEW relative wrapper copies only supplied source/pins/rebuild.py into its own build/work package, compiles support/controls/audit and prints all actual types/axioms. It also repeats the ten exact rational checks and two added-premise type-contract mutations. It was tested in a separate copied context containing no manuscript/author/private inputs. Historical inventories are metadata only and are not execution dependencies. The unchanged `formal/review/replay.py` hardcodes the original project/implementation path and historical source archive: it is NOT standalone portable reproduction and is not called by the new wrapper. Likewise original verifier/inventory scripts describe their own original seals, not this manuscript's enclosing seal.

Supply trusted Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 plus eight pinned auxiliaries. Only own sources are rebuilt. No clean-source dependency rebuild or complete binary-cache authentication is claimed. No cache binaries or private bodies are bundled in public support. New compilation receipts are under qa/formal/; historical receipts remain attributed under formal/.

The full probability/geometry proof, all 248 coefficients, zero/repeated/nonsimple strata and simplex iff equality are preserved. The scalar-majorization audit assumes its scalar premise; it does not prove expectation-to-mixture comparison. See the complete exclusions in COVERAGE.md. The r1 PDF's all-page QA and same-cache byte identity are historical implementer observations; the parent intake was sampled layout only. New all-page QA and tested-engine/cache reproduction are documented separately for this PDF. No clean offline release is claimed.
'''
(p/'README.md').write_text(readme)
c=(old/'COVERAGE.md').read_text();c=c[:c.index('Formal support is **pending**.')]+'''## Integrated independently reviewed deterministic support

The parent adopted PASS_SCOPED_SUPPORT with no author repair. Exact reviewed coverage is 21 support declarations (3 definitions/18 theorems),20 implementation controls and15 independent semantic/type/use-site declarations. See Appendix C, unchanged `formal/implementation/COVERAGE.md` and `formal/review/review.md`; all 56 actual types and axiom reports are printed by the new relative wrapper. Only propext, Classical.choice and Quot.sound occur.

At Proposition B, equations (Sn), (mixture), (two-brackets) retain their original source labels `eq:Sn`, `eq:mixture`, `eq:two-brackets`. New Appendix C labels `eq:formal-hypotheses`, `eq:formal-bound`, `eq:formal-residuals` state the exact mapping. For ALL real alpha,beta,p,q,d,P,N with alpha,beta>0,sum2,0<p<1,q=1-p,d>=0,P,N>0,2dp²<P,2dq²<=N, `T088P133.rational_mixture_lt_one` proves (1+d)[p alpha/(alpha+P/p)+q beta/(beta+N/q)]<1. Non-strict wrapper, moment conversions, positive denominators and reduced p=0,p=1 expressions are included; d=0 is covered. `one_sided_lt_one` correctly needs no d>=0. The paper's Cauchy-Schwarz proof remains; Lean gives the equivalent residual/square decomposition.

The independent audit proves the original normalized bracket mapping and scalar-majorization composition with an EXPLICIT assumed scalar premise. It does not prove that premise for an expectation. The exact type contracts reject both reviewed added-premise mutations. Ten exact rational configurations and both historical eleven-case integrity suites passed; new wrapper reproduces the former two semantic checks and ten configurations, and new manuscript copy-only integrity controls are separate. No source repairs were made.

ENTIRELY UNFORMALIZED: actual-facet geometry and nonzero middle coefficients; mixed-volume attainment/coarea/Gamma-Dirichlet; distributions/log-concavity/HNBUE and expectation-to-mixture majorization; the ten-pattern certificate and probabilistic interpretation; continuity/zero/repeated-knot assembly and derivation of strict moments; simplex equality and every-six-facet geometric strictness; the full projection-body theorem. Algebra is support, not a substitute for these proofs.

Trusted Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 and eight auxiliaries. Only own source files rebuilt. No clean dependency-source rebuild or complete binary-cache authentication. Unchanged historical replay requires its original project inputs; the new relative wrapper runs from supplied copies and explicit trusted dependencies without them. Historical pending text remains only in attributed unchanged originals. Full independent manuscript review and all parent acceptance/count/release decisions remain external. Count18/20 unchanged; publication stopped.
'''
(p/'COVERAGE.md').write_text(c)
(p/'HANDOFF.md').write_text('''# Parent handoff: final-manuscript implementation round 2

Completed independently reviewed scoped formal support has been integrated with no author formal repair, and no change to the full mathematical theorem/proof. The original r1 manuscript and formal packages remain immutable; their pending-at-the-time statements remain historical.

1. Authenticate this new FINAL/MANIFEST/outsideREPORT using the detached handoff hashes and trusted read-only verifier. Public verifier covers the exact packet only, not private evidence/caches or mathematical gates.
2. Dispatch independent review of this complete final manuscript: all mathematics, all248 sparse coefficients, exact formal use-site mapping/exclusions, bibliography/rights/PQ1-PQ5/provenance and all-page layout. This implementation is not that review.
3. The NEW relative wrapper has been tested in a separate copied context. Review its actual logs and trust limits: 56 declarations, supplied pinned compiler/precompiled dependencies, no clean dependency rebuild/full binary-cache authentication. The unchanged historical review replay still needs original project files and is labelled accordingly.
4. Any later portable local release and verification belongs to a separate parent-owned step. No source/private/history body, derivative, render of those bodies, dependency cache or engine binary belongs in its public payload without appropriate rights. This root is not a release.
5. Parent alone decides integration and later gates. No acceptance/count change:18/20. Publication/uploads/submissions/contacts/browser UI STOPPED. No old/shared-root edits, git or nested agents.

The parent r1 intake authenticated1046 original entries and12 copied cases, with exact support; its layout check was sampled, not an independent manuscript gate. Original all17-page QA and same-cache PDF identity remain r1 implementer observations. New all-page QA and reproduction are separately recorded here.
''')
prov=(old/'PROVENANCE.md').read_text()
# Keep full historical provenance intact in separate file; current document explicitly attributes it.
(p/'PROVENANCE.md').write_text('''# Round-2 integration provenance and limits

Runner as assigned: Codex / GPT-6 Astra / high / default service tier. Author Myeongjin Kang, no affiliation or contact. No nested agents. Count18/20 unchanged. Publication/uploads/submissions/contacts/browser UI STOPPED. No git/staging/commits or active fresh-structural-discovery-r137 content read. All writes, copied evidence/caches, builds, renders and scratch are confined to this r2 root.

`provenance/r1-PROVENANCE.md` is the unchanged complete prior provenance, attributed to r1, with its historical pending status. Its detailed source rights, source/primary/history read limits, prior provider failures and chronology remain in force; this integration does not rewrite history. `provenance/input-anchors.json` authenticates original r1/formal/review/author/correctness anchors supplied independently in the role brief. `formal/origin.json` binds every unchanged formal copy. The parent formal adoption/disposition and manuscript intake are preserved under `provenance/parent/`.

The original author sketch and exact certificate predate the recorded freeze2026-10-20T17:21:32Z. Author FINAL seal17:31:58.711847Z conflicts with notes drafting/packaging17:36-17:45Z. Both remain, with no preferred detailed chronology. Late companion/acceptance reads and temporary /tmp history-list deviation stay disclosed. Earlier network/usage failures were not mathematical verdicts; the missing-V checker was corrected and its spot samples were distinct-only, not full proof checks. No auxiliary best constant or positive all-n threshold claim is adopted. Negative coefficients reject a certificate, not an inequality; the separate existing corner proof remains.

The current full mathematical proof is preserved from r1. A source-preservation check binds its core section bytes and all original theorem/proof environments, plus unchanged witness tables and exact support files. Only the status, formal use-site note, new formal appendix/references and current provenance wording change. Historical source-reading claims in the paper are now attributed to r1; current actual rereads/reuse are recorded separately in source-reading-records.json. No new global/project priority or open-status search, new downloads or upstream truth audit occurred. The original SourceP/FHLX/r132/classical credit and PQ1-PQ5 remain. Klefsjo primary bodies are unread; Brannen/CFLXX bodies remain unavailable. Copying/hash checks alone are never labelled body reads.

The parent adopted scoped formal PASS, no repairs. Reviewed Lean bytes are unchanged:21 support(3 definitions/18 theorems),20 controls,15 independent audit declarations. Only propext,Classical.choice,Quot.sound. Exact normalized/type/scalar-use mapping is supported, with the scalar premise still assumed. Entirely unformalized: actual-facet geometry,mixed-volume attainment/coarea/Gamma,distributions/log-concavity/HNBUE/expectation majorization,ten-pattern certificate and interpretation,continuity/zero/repeated-knot assembly and strict-moment derivation,simplex equality and full theorem.

Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 plus8 auxiliaries are explicit trusted dependencies. Only own sources compiled, no clean-source dependencies or full cache-byte authentication. The NEW relative wrapper uses supplied code/pins and explicit --lean/--cache; its extraction/copy test has no hidden manuscript/author/formal input roots. The original historical review replay.py remains unchanged and hardcodes its original companion implementation path/archive. Metadata-only historical inventories are not required execution inputs for the new wrapper.

Formal implementation development corrections (deprecated import/tactic separator, unsupported pp.width), independent audit's corrected initial tactics and historical provisional22-entry versus final24-entry seal distinction remain disclosed in unchanged formal PROVENANCE/limits. These are prior development observations, not unresolved formal repairs. New wrapper/PDF development outcomes are recorded in REPORT.md and work/notes.md.

The original r1 public52-file/seven-directory seal and separately FINAL-bound36 named private files authenticate; its public verifier does not audit private evidence. Parent intake authenticated1046 originals and12 copy cases/exact support but only sampled layout. R1's all17-page QA and same-cache byte identity remain implementer observations. This round's fresh layout/build/control results are separate and do not imply an independent manuscript gate or clean offline release. Private evidence/cache inventories here are separately FINAL-bound and explicitly outside public verifier coverage.
''')
rights=(old/'RIGHTS.md').read_text().replace('this draft','this manuscript implementation')
rights+='''
Reviewed formal support is copied UNCHANGED from the completed implementation and independent review. Both original packages license their Lean/Python code MIT and original prose CC BY4.0; their LICENSE-CODE/NOTICE/PROVENANCE or limits are retained. No notices are removed or source relicensed. `formal/origin.json` identifies original paths and hashes. New wrapper code is MIT under the enclosing license. Historical metadata inventories are provenance, not body redistribution rights. Historical r1 prose copies retain their CC BY4.0 attribution. Private r1 evidence was copied locally only and remains outside the public packet under original rights. TeX engine/cache copies retain original metadata and upstream rights and are excluded from the public artifact.
'''
(p/'RIGHTS.md').write_text(rights)

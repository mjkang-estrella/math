from pathlib import Path
import json,re,hashlib,datetime
D=Path(__file__).resolve().parent
load=lambda p:json.loads(p.read_text())
def write(n,o):(D/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
dis=load(D/'dispositions.json');prov=load(D/'source-provenance.json')
versions={}
for e in prov:
 if 'path' in e:
  t=Path(e['path']).with_suffix('.txt').read_text();v=re.search(r'arXiv:'+re.escape(Path(e['path']).stem)+r'v\d+',t);versions[Path(e['path']).stem]=v.group() if v else 'not identified'
write('source-coverage.json',dict(record_statement_reads=50,selected_primary_passage_records=29,whole_body_reads=0,successor_proof_body_reads=0,full_dependency_audits=0,registry='unavailable HOLD',sources=versions,scope_counts={k:sum(d['statement_scope']==k for d in dis) for k in sorted({d['statement_scope'] for d in dis})},limits='HTML bytes and derivatives bound before content search. Selected passages are not whole-paper, local proof, dependency or registry clearance. No promising eligible full-scope route survived, so no successor hunt or proof investment. Prior-context matches are administrative leads only.'))
write('failures.json',dict(failed_checks=[dict(stage='first HTML extraction',exception="ModuleNotFoundError: No module named 'bs4'",exit=1,resolution='Retained extract-failed-bs4.py; replaced parser with Python standard-library HTMLParser, within unchanged guard.')],stopped_routes=['MathDB inherited HTTP429: zero requests','AIM/Kourovka/EGRES/AIProofWatch parked: zero requests','DMGT TLS parked','ProjectEuclid challenge parked','ResearchGate HTTP403 parked','OEIS A274199/internal HTTP403 r542 parked: no retry or alternate route'],other_limits=['Current public proof registry unavailable; HOLD, no absence-of-hits claim','No Google/GitHub API/raw/codeload/diff, ScienceDirect, browser, preview or TLS bypass','No PDFs downloaded or visually inspected; no PDF extraction'],procedural_deviations=['No access or resource-cap deviation. bs4 extraction failed before reading source content; failure retained. Initial SHA256 and size lists precede intake administrative content; flat binding completed before scientific statements.']))
(D/'SUMMARY.md').write_text('''# r576 breadth handback

Read all 50 assigned literal MathDB record statements, including quantifiers; dispositions.json contains exactly 50 individual judgments, exact UTF-8 statements, statement hashes, canonical record hashes, original chunk paths and 1-based lines. This is record review, not 50 complete self-contained mathematical statements. Scope flags: 23 non-self-contained, 2 incomplete (386396 dangling reference, 387650 malformed integrals), 6 scope-ambiguous, 19 under standard conventions. These flags do not inherit the intake's optimistic “full” tag.

Zero proposals and zero credit. No new full-scope proof/counterexample was established. The literal entropy bound in 386283 follows routinely from data processing and pair independence; source intent remains unqualified. In 387832 the nonzero-sine example fails derivative normalization, an excluded easy subquestion that leaves the intrinsic classification unresolved. Source updates for 387490 and 387625 report earlier answers, but the cited proof bodies were not audited. No current registry clearance is available.

Four lawful primary arXiv HTML documents were fetched, bytes bound before extraction, and text derivatives bound before search. Selected question/definition/update passages were inspected for 29 records; no whole-paper proof/dependency audit or closest-successor proof-body clearance is claimed. source-coverage.json gives exact versions; source-provenance.json gives requested/final URLs, UTC, SHA256 and sizes. selected-passages.json retains exact derivative offsets. No PDFs or browser tools were used. Sources are not newly verified open/closed statuses.

Integrity: independently checked intake exact payload/hash/size, every directly listed original/copy pair, the r301 manifest against intake, all 20 original corpus chunks IN PLACE and all 8 separately listed frozen_inputs. Flat references only, no corpus or historical tree copying. Three reserved 50-ID sets are mutually disjoint, disjoint from the 5,333 baseline record reviews, and avoid protected IDs. r504 and r574 reservations unchanged. r304 exclusion/disposition references, r363 Cayley decision and r575 adjudications were bound and checked before any promotion; no promotion occurred. No assigned-ID text matches in the four prior administrative files unless recorded in prior-context-check.json.

Historical qualifications preserved: 344924 ellipsized, r568's 24 conservative source/definition judgments and r572's 30 non-self-contained judgments remain outside this assignment. 366370 is excluded as a routine restriction; 365437/365439 remain parked for journal/prior qualification; 372522's claimed-proof gap is not an identity refutation. Retirements 338290/339564/372627 and parked 337963 remain unchanged. Counts remain 9 additional /39 total /next40. The baseline remains 5,333 reported record reviews; root may reconcile this separate 50-record report, without construing either as complete technical corpus coverage.

The fixed helper guard was used for every Python operation with requested single-thread environment, python3 -B, and unchanged 512MiB AS/groupRSS, CPU210s and wall230s. One extraction attempt failed because bs4 was absent; its script and failure are retained. Standard-library extraction succeeded. No numerical sweep, Lean/manuscript change, shared index/ledger edit, git operation, or external mutation occurred. failures.json preserves access holds including OEIS A274199/internal, without retries.

Run the independent read-only verifier from this lane with:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py
```

The manifest covers every lane payload and verifier, excluding only itself and final-verification-receipt.json. The separate receipt binds manifest SHA256 and size. Bounded synthetic negatives confirm rejection of hash mutation, size mutation and extra files; originals were not mutated. Integrity PASS is not mathematical or novelty PASS.
''')
print(versions)

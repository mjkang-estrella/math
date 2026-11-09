from pathlib import Path
import json,hashlib,shutil
D=Path.cwd(); R=D.parent/'grid-manuscript-r1'
p=D/'paper.md'; s=p.read_text()
s=s.replace('DRAFT · MathDB 343536','REVISION 2 DRAFT · MathDB 343536')
s=s.replace('The supplied Lean endpoint is unconditional. This draft does not replace the separate root replay.','The supplied Lean endpoint is unconditional. Root reports a separate successful replay; acceptance remains a separate decision.')
s=s.replace('all three sentences', 'all three sentences')
# Preserve all mathematical arguments; update only evidence/status and disclosure text.
s=s.replace('## 8. Correspondence with the six formal rounds','## 8. Current endpoint and historical proof rounds')
s=s.replace('Round | Added proof content | Endpoint boundary at that round','Historical round | Added proof content | Boundary then (not current)')
s=s.replace('Audit6 reports 742 LOCAL declarations,', 'Audit6 reports 299,549 inventoried and audited declarations (equal sets), including 742 LOCAL declarations,')
s=s.replace('The supplied round-6 validation [5] reports strict serial compilation', 'The supplied round-6 validation [5] reports strict serial compilation with lean -j1 -M3500 -DwarningAsError=true')
s=s.replace('Enumeration in the earlier adversarial review [4] is diagnostic and is not the certificate of the quantified statement.', 'The final fidelity review independently enumerated all degree-compatible partitions and full adjacency-preserving permutations, then all subgroups, for 1×n (1 ≤ n ≤ 6), 2×2, 2×3, 3×3 and 3×4. It compared the actual partition sets with subgroup orbit sets and compiled separate kernel-decided sanity witnesses. These finite checks are diagnostic, not a proof of the quantified statement.')
old='This manuscript lane did not run Lean, lake or leanchecker.'
start=s.index(old); end=s.index('\n\nThe dossier contains',start)
s=s[:start]+'''This revision lane did not run Lean, lake or leanchecker. It reused the source ZIP byte-identically and tested safe extraction, rejecting unsafe names, links, duplicates and compiled artifacts. Serial document checks use the inherited capped runner: two CPUs, sampled process-group RSS 6 GiB, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2, with lane-local temporary/cache paths. Orientation reads preceded input binding; short setup/authoring calls were affinity/CPU limited but not all RSS-sampled. No perfect all-call enforcement is claimed.'''+s[end:]
s=s.replace('The current root-replay and fidelity status is given on the final page and in results.json.', 'Final root-replay and fidelity records are summarized on the final page and in results.json.')
s=s.replace('Its bounded search of citing works and the authors\' follow-ups found no earlier proof for finite grids.', 'The earlier review\'s bounded search of citing works and the authors\' follow-ups found no earlier proof for finite grids; the fidelity review performed no new literature search.')
s=s.replace('This lane read cached arXiv source text and local review records only.', 'This lane used cached source material and local review records only. The fidelity review read cached arXiv v1/v2 text and local records, performed no new literature search and did not refresh public registries.')
s=s.replace('The SIADS journal body, Brito–Manoel body and Godsil body were not read here, and the earlier review likewise states body-access limits for those works.', 'Neither this lane nor the fidelity review read the SIADS, Brito–Manoel or Godsil bodies. The earlier review likewise records body-access limits.')
start=s.index('Draft status at the final local check:'); end=s.index('\n\n## Bibliography',start)
s=s[:start]+'''Final received records: grid-fidelity-r1/REVIEW.md and review.json give A–C PASS and D–E QUALIFIED_PASS. Its interrupted Audit6 run was excluded and rerun; auditor import warnings and historical resource qualifications remain disclosed. The separate decisive root receipt grid-parent-final-r1/replay-result.json reports PASS: 47/47 modules strictly compiled and explicitly leanchecked, 4/4 controls rejected, Audit6 inventory = audited (299,549; LOCAL 742), and standard axioms only. Root corrected its counter to include the first PASS line. Its registry-refresh.json reports CLEAN at Omega bc417b2d, within the path-screen scope above. Campaign status is 29/40 beyond 39; this revision adds zero accepted credit. Root reads the paper and decides.'''+s[end:]
p.write_text(s)
(D/'PROOF.md').write_text('# Consolidated ordinary proof - REVISION 2 DRAFT\n\nZero accepted credit. Root alone accepts. Historical partial-status material is archived evidence only.\n\n'+s.replace('---PAGE---','\n'))
p=D/'STATEMENT-CORRESPONDENCE.md';p.write_text(p.read_text()+'\nFinal fidelity verdicts: A-C PASS, D-E QUALIFIED_PASS. All six gate-E editorial requirements are mapped in gate-E-map.json. Root\'s separate corrected receipt reports 47/47 modules and 4/4 rejected controls. Acceptance remains pending root\'s paper assessment.\n')
p=D/'REPRODUCE.md';s=p.read_text();s=s[:s.index('\nLate root receipt:')]
s=s.replace('scripts/collect.py documents source copying and safe extraction;', 'scripts/extract.py performs the source-only safe-extraction test;')
s=s.replace('Failed dependency, extraction-count and layout experiments are retained in receipts, not counted as validation.', 'Round-1 receipts and failed experiments are preserved as historical records under inputs/grid-manuscript-r1-receipts. Current receipts are under receipts/.')
s=s.replace('with provenance in receipts/raw-record.json','with provenance in inputs/grid-manuscript-r1-receipts/raw-record.json and hashes in receipts/raw-record.json')
s=s.replace('scripts/collect.py','scripts/extract.py')
s+='''\nRevision-2 workflow: run scripts/extract.py, scripts/check_math.py, scripts/render.py, then pdftoppm through scripts/run.py sequentially. Inspect every PNG before creating qa/receipt.json. Finally run scripts/package.py through scripts/run.py. The final packager verifies the before/after bindings, source-copy hashes, archive identity, PDF QA binding, ZIP CRC and every member hash. It never runs Lean.\n\nCorrected root receipt: inputs/grid-parent-final-r1/replay-result.json reports PASS, 47/47 strict builds and explicit-module leanchecker passes, 4/4 controls rejected, Audit6 299,549 inventoried = audited and LOCAL 742, with only the three standard axioms. Its correction note explains that the old counter missed the first PASS line. The failed initial extraction attempt preceded compilation; executable permission repair changed no script bytes. registry-refresh.json reports CLEAN at Omega bc417b2d within complete-tree path screening only.\n\nThe final fidelity records are now present (A-C PASS, D-E QUALIFIED_PASS). Its replay-driver interruption and detached-child cleanup are disclosed in REVIEW.md; the interrupted Audit6 invocation is excluded and a capped serial resumption completed. Strict flags do not mean warning-free auditor imports. Neither those records nor the successful root replay accept the manuscript. Campaign 29/40 beyond 39; zero new accepted credit.\n'''
p.write_text(s)
items={
'1':{'location':'paper.md section 1, Theorem 1; sections 6-7','applied':'Retained all three positive-dimension sentences and natural orbit-map order/lattice isomorphism in every free case.'},
'2':{'location':'Abstract; section 10','applied':'Retained candidate novelty only for sentence 1, m,n >= 2; known paths, classical group, consequential lattice statement, modest significance and unresolved Godsil channel.'},
'3':{'location':'sections 1-4, 7-8','applied':'Retained Definition 5.1, literal box product, refinement, full-group stabilizer, Setoid/count/multiset bridge, explicit positive-layer/non-backtracking/conjugation hypotheses and exceptional 7/9 versus >=10 cardinality argument.'},
'4':{'location':'section 8; STATEMENT-CORRESPONDENCE.md','applied':'Historical round/boundary table labels strengthened; stale partial claims remain only in immutable historical source copies, not current status.'},
'5':{'location':'sections 8-10; REPRODUCE.md','applied':'Endpoint/hash/pins, strict flags and explicit-module checks, inventory 299549/LOCAL 742, lexical scan, standard axioms, final independent finite checks, corrected decisive root replay and resource overlap disclosed.'},
'6':{'location':'section 10','applied':'No SIADS, Brito-Manoel or Godsil body access by fidelity review; no new fidelity literature search; bounded prior-art limits and correct arXiv:1908.05797 (2019/journal 2020) provenance retained.'}}
(D/'gate-E-map.json').write_text(json.dumps(items,indent=2)+'\n')
(D/'root-status.json').write_text(json.dumps({'root_replay':'PASS','modules':'47/47','controls_rejected':'4/4','inventory_equals_audited':299549,'LOCAL':742,'registry':'CLEAN path screen; Omega bc417b2d','accepted':False,'credit':0},indent=2)+'\n')
(D/'results.json').write_text(json.dumps({'status':'REVISION_2_DRAFT_NOT_ACCEPTANCE','mathdb_id':343536,'endpoint':'GridFinal6.mathdb_343536','campaign_count':'29/40 beyond 39','accepted_credit':0,'root_alone_accepts':True,'root_replay':'PASS_47_OF_47','root_controls':'4/4_EXPECTED_FAILURE','fidelity_verdicts':{'A':'PASS','B':'PASS','C':'PASS','D':'QUALIFIED_PASS','E':'QUALIFIED_PASS'},'gate_E_items_applied':[1,2,3,4,5,6],'source_archive_sha256':'a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953','lean_executed_here':False,'math_content_changed':False,'page_qa':'See qa/receipt.json','input_integrity':'See receipts/input-integrity.json','no_child_agents':True,'no_external_access':True},indent=2)+'\n')
(D/'SUMMARY.md').write_text('''# Revision 2 DRAFT - MathDB 343536

Zero accepted credit. Campaign 29/40 beyond 39. Root reads the paper and decides.

Changes from round 1 (all mathematical arguments retained):

1. Corrected the root receipt to 47/47 strict builds and explicit-module leanchecker passes; 4/4 controls rejected. Explained the missed-first-PASS counter correction; removed the obsolete incompleteness qualification from current prose/status. Added root Audit6 inventory = audited 299,549, LOCAL 742, and standard axioms. Refreshed exact root receipt and registry-refresh.json (CLEAN path screen at Omega bc417b2d).
2. Replaced pending/absent fidelity statuses with final REVIEW.md and review.json: A-C PASS, D-E QUALIFIED_PASS. Added final independent full-Aut finite enumeration, kernel-decided sanity checks, and the fidelity interruption/excluded Audit6/resumption disclosure.
3. Retained the entire positive-dimension theorem, natural orbit-map strengthening, Definition 5.1, literal box product, refinement order, full-group stabilizer, Setoid/count/multiset bridge and explicit propagation/transport hypotheses. Retained exceptional cardinality proof. gate-E-map.json maps all six items.
4. Strengthened historical labels on the six-round table; current PROOF.md and correspondence give the unconditional endpoint. Archived partial-status documents are historical evidence only.
5. Made strict compilation flags explicit; retained pins, source archive hash, declaration/forbidden-token audits, standard axioms, Bound.Attribute rebuild and round-6 overlap. Successful replay remains separate from acceptance.
6. Clarified that fidelity made no new literature search or registry refresh and read none of the SIADS, Brito-Manoel or Godsil bodies. Retained candidate novelty only for sentence 1 with m,n >= 2, known paths, classical group, consequential lattice result, modest significance, unresolved compact-graph channel and corrected 2019 arXiv/journal-2020 provenance.
7. Updated draft/version labels, campaign count, current reproduction/packaging scripts, manifests, evidence-copy index, before/after bindings, results and receipts. Kept inherited receipts separately labelled as round-1 history. Re-rendered the paper; every final page is covered by qa/receipt.json. Reused the Lean source ZIP byte-identically and repeated safe extraction without running Lean.

The exact raw MathDB line and cached source/retrieval evidence are retained. No new literature clearance is claimed. Input orientation preceded the baseline; binding is before revision/copy, not before first read. Short setup/authoring calls were CPU/affinity limited but not all RSS-sampled; heavy document/check/package invocations use the serial capped runner. No perfect all-call enforcement claim is made.

No child agents, Lean/lake/leanchecker, git, network/browser, external messages, publication/upload, shared-ledger or other-lane writes. All revision outputs and temporary files are in this lane. All commands are synchronous; no running lane jobs remain at handback. DOSSIER-MANIFEST.json inventories the full ZIP; delivery hashes and package-validation.json are outside it to avoid self-reference.
''')
# Bind exact copied evidence to original sources using inherited provenance, then current overrides.
old=json.loads((R/'SOURCE-COPIES.json').read_text()); idx={}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((D/'hashes/inputs-before.json').read_text())
for q in sorted((D/'inputs').rglob('*')):
 if not q.is_file(): continue
 rel=str(q.relative_to(D)); orig=old.get(rel,{}).get('original')
 if rel.startswith('inputs/grid-manuscript-r1-receipts/'):
  orig=str(R/'receipts'/q.relative_to(D/'inputs/grid-manuscript-r1-receipts'))
 if rel.startswith(('inputs/grid-fidelity-r1/','inputs/grid-parent-final-r1/')) and not q.name.startswith('REVIEW-initial'):
  candidate=D.parent/q.relative_to(D/'inputs')
  if candidate.is_file() and sha(candidate)==sha(q): orig=str(candidate)
 if not orig: raise ValueError(rel)
 idx[rel]={'original':orig,'sha256':sha(q),'historical':('initial snapshot' in orig or 'grid-manuscript-r1-receipts' in rel)}
 # Add any original not already covered to baseline after checking its inherited immutable hash.
 candidate=Path(orig)
 if candidate.is_file() and str(candidate) not in b:
  assert sha(candidate)==sha(q); b[str(candidate)]=sha(candidate)
(D/'SOURCE-COPIES.json').write_text(json.dumps(idx,indent=2)+'\n')
(D/'hashes/inputs-before.json').write_text(json.dumps(b,indent=2)+'\n')
raw=D/'mathdb-343536.raw.jsonl'; assert raw.read_bytes()==(R/raw.name).read_bytes()
(D/'receipts/raw-record.json').write_text(json.dumps({'file':raw.name,'sha256':sha(raw),'bytes':raw.stat().st_size,'byte_identical_to_round_1':True,'upstream_provenance':'inputs/grid-manuscript-r1-receipts/raw-record.json'},indent=2)+'\n')
print('revised paper and current dossier metadata; mathematical proof unchanged')

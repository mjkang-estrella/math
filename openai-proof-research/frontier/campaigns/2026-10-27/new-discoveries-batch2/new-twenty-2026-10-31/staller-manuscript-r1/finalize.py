from pathlib import Path
import json,hashlib,zipfile,re,datetime
R=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(n,v):(R/n).write_text(json.dumps(v,indent=2)+'\n')
f=json.loads((R/'frozen-inputs.json').read_text())['files'];assert len(f)==213
checks={p:{'expected':h,'actual':sha(p)} for p,h in f.items()};assert all(x['expected']==x['actual'] for x in checks.values())
dump('integrity-after.json',{'count':213,'all_match':True,'bindings':checks})
assert sha(R/'proof/Game.lean')=='d544e48fd0285dc5a132518f429d2108c2f04866b1ee1b67aaf977bac82e5b50'
bridge=R.parent/'staller-fidelity-review-r1/extracted/Bridge.lean';assert sha(bridge)==sha(R/'proof/Bridge.lean')
for x in (R/'proof').iterdir():assert sha(x)==sha(R/'replay'/x.name)
assert 'warning:' not in (R/'tex-build.log').read_text().lower()
dump('pdf-qa.json',{'pages':8,'render_command':'pdftoppm -scale-to 1400 -png paper.pdf render/page','all_pages_visually_inspected':list(range(1,9)),'overflow':False,'missing_math_glyphs':False,'final_tex_warnings':False,'lower_table_kept_on_one_page':True,'method':'Direct image inspection of every final PNG, no browser','pdf_sha256':sha(R/'paper.pdf')})
receipts={p.stem:json.loads(p.read_text()) for p in (R/'replay').glob('*.json') if p.stem.startswith(('strict-','all-declarations','leanchecker-','negative-'))}
dump('results.json',{'mathdb_id':355140,'status':'DRAFT_MANUSCRIPT_AND_DOSSIER_COMPLETE_FOR_ROOT_REVIEW','credit':0,'accepted_new':3,'target_new':20,'previous_accepted':39,'ordinary_math':'PASS','source_fidelity':'PASS_scoped_cached_primary_bodies','published_comparison':'PASS_scoped','strict_Lean':'PASS_fresh_extracted_both_modules','novelty':'qualifiedPASS_bounded_independent_review','significance':'qualifiedPASS_bounded_independent_review','global_priority_certification':False,'root_paper_review':'separate_pending','root_final_replay':'separate_pending','root_acceptance':'separate_pending','winning_number':4,'claimed_bound':3,'minimum_degree':2,'edges':['01','05','12','16','23','34','45','56'],'endpoints':['MathDB355140.winning_number_four','MathDB355140.source_refutation'],'reviewer_supplement':'Review.number_le_iff; unchanged, separately attributed to fidelity reviewer','declarations':{'Game':63,'Bridge':1,'total':64,'anonymous_positive_examples_checked':5},'axioms':['propext','Classical.choice','Quot.sound'],'upper_certificate':{'nodes':70,'leaves':26,'root':3},'lower_certificate':{'positions':35,'completions':105},'frozen_bindings':213,'frozen_before_after_all_match':True,'original_game_sha256':sha(R/'proof/Game.lean'),'bridge_sha256':sha(bridge),'original_zip_sha256':'fb77568d66a9cab5e73b0fc3ea205d3fd2c5e2ce79a4a0b235e89aa20ca4897a','new_proof_zip_sha256':sha(R/'355140-proof-source.zip'),'replay_receipts':receipts,'trust_limitations':['External upstream cached oleans trusted; source-to-olean correspondence unproved','No standalone dependencies or full upstream rebuild','leanchecker uses same Lean kernel','25ms sampled RSS cap, not aggregate cgroup guarantee'],'scope_limits':['Only clause (i) refuted, conjunction consequently false','Clause (ii) separately unresolved','No minimality, infinite family, asymptotics, general-bound or second-credit claim','Bounded literature, registry/history and inaccessible live solution state limitations preserved'],'no_jobs_left':True,'external_actions':False})
dump('evidence-references.json',{'note':'Full frozen path/hash references, not recursively duplicated historical trees. Selected primary PDFs, complete independent reports and receipts copied under evidence/.','frozen_bindings':f,'supplement':{'path':str(bridge),'sha256':sha(bridge)},'original_zip_is_distinct_from_new_two_module_packet':True})
(R/'SUMMARY.md').write_text('''# MathDB355140 manuscript/dossier handback

**Draft only; zero credit. Count remains 3/20 beyond 39.** Root paper review, final root replay and acceptance are separate pending gates. No publication or global priority certification.

The seven-vertex simple connected bipartite theta has branches 1-0-5, 1-6-5 and 1-2-3-4-5, edges 01,05,12,16,23,34,45,56, and minimum degree 2. Its exact Staller-start winning number is 4 > ceil(7/2)-2+1 = 3. This refutes Bujtas-Dokyeesun Conjecture 7.2(i) and the MathDB conjunction; clause (ii) remains separately unresolved. It attains the unrestricted ceiling at degree two. No minimum-order, family, asymptotic, general bound or second credit claim.

- `paper.tex` / `paper.pdf`: eight-page manuscript, exact definitions/source scope, graph figure/neighborhood table, all 26 terminal upper histories (70-node tree) and 35-row lower completion table covering all 105 possibilities. Corrected reviewed prose used. The ordinary proof stands independently of Lean compilation.
- `355140-proof-source.zip`: source-only two-module packet with unchanged Game.lean and separately attributed unchanged reviewer Bridge.lean, all-declaration audit, finite ordinary verifier/tree, pins and instructions. Distinct from the frozen original one-module ZIP.
- `355140-full-dossier.zip`: paper, proof packet, selected primary/review evidence, complete replay/axiom logs and resource receipts, references and hashes. No recursive historical tree/cache duplication.
- `results.json`, `manifest.json`, `integrity-before.json`, `integrity-after.json`, `environment-verification.json`, `declaration-audit.json`, `pdf-qa.json`: machine-readable scope and verification.

Fresh safely extracted sanitized strict builds PASS for Game and Bridge; both module leanchecker checks PASS. All 63 main declarations plus the supplement's sole retained declaration are audited with full explicit types/values/proof terms and individual axiom reports. The five anonymous controls compile but are not retained declarations. Only propext, Classical.choice, Quot.sound occur. Negative controls reject a false three-move win, absent module and corrupt module. Game build 6.61s / 3.83GiB sampled RSS; Bridge 1.52s; audit 33.20s. Every invocation stays under the explicit two-CPU, 6GiB sampled RSS, 12GiB AS, 120 CPU/140 wall-second limits, -j1 and MALLOC_ARENA_MAX=2. No job remains.

Lean4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned. External caches remain trusted; hashes do not prove source-to-olean correspondence. Same-kernel leanchecker is not an independent foundation. No upstream rebuild or standalone dependency distribution claimed. Both independent complete reports and root integrations are retained; novelty/significance remain qualifiedPASS with literature/access/history limitations. No new network retries.

All 213 frozen bindings match before/after. Game bytes and original ZIP match requested SHA256s; Bridge is unchanged. Every final PDF page rendered and visually inspected; final TeX build has zero warnings, no overflow or broken math glyphs. The final table transcription independently verifies against exact game sets (`python3 verify-paper.py`).

To reproduce formal checks, extract the proof ZIP into a new directory and run `python3 replay.py`; then `python3 ordinary-proof.py`. See its README and pin-evidence.json. `build-paper.sh` rebuilds/render the PDF with an available Tectonic installation and resource bundle; the local preparation used an existing cached installation, offline. Source/reference pin manifests are included; the TeX tool distribution is not bundled. All writes confined to this lane; no git, child agents, shared/frozen edits, external communication or uploads.
''')
# Every delivery member except self-referential digest files/archive, cache, and freshly built binaries.
exclude={'manifest.json','delivery-receipt.json','355140-full-dossier.zip','fix-figure.py'}
files=[]
for p in sorted(R.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(R)
 if rel.parts[0]=='tex-cache' or p.name in exclude or p.suffix in ['.olean','.ilean','.pyc']:continue
 files.append(p)
dump('manifest.json',{'algorithm':'SHA256','excludes':'manifest itself, full archive, delivery receipt, TeX cache and local generated binary caches','files':{str(p.relative_to(R)):sha(p) for p in files}})
files.append(R/'manifest.json')
with zipfile.ZipFile(R/'355140-full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:
  i=zipfile.ZipInfo(str(p.relative_to(R)),date_time=(2026,11,1,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,p.read_bytes())
dump('delivery-receipt.json',{'paper_sha256':sha(R/'paper.pdf'),'proof_zip_sha256':sha(R/'355140-proof-source.zip'),'full_dossier_sha256':sha(R/'355140-full-dossier.zip'),'manifest_sha256':sha(R/'manifest.json'),'frozen_bindings_verified':213,'full_archive_members':len(files),'credit':0})
print((R/'delivery-receipt.json').read_text())

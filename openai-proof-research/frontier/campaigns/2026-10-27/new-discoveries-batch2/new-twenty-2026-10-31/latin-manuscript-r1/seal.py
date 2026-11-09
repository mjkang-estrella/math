"""Seal selected dossier payload; never mutates frozen originals."""
from pathlib import Path
import json,hashlib,zipfile,shutil,datetime
L=Path(__file__).resolve().parent; B=L.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,d):(L/n).write_text(json.dumps(d,indent=2)+'\n')
f=json.loads((L/'frozen-inputs.json').read_text());bad=[p for p,h in f.items() if H(Path(p))!=h];assert len(f)==277 and not bad
write('integrity-after.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':len(f),'mismatches':bad,'all_unchanged':True})
r=json.loads((L/'replay-result.json').read_text());assert r['status']=='PASS'
E=Path(r['directory']);prov=json.loads((E/'dependency-provenance.json').read_text())
write('lake-manifest.json',prov['manifest']);(L/'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
(L/'requirements-paper.txt').write_text('reportlab==4.4.9\npillow==13.0.0\ncharset-normalizer==3.5.2\n')
fonts=[Path('/usr/share/fonts')/x for x in ['liberation-serif-fonts/LiberationSerif-Regular.ttf','liberation-serif-fonts/LiberationSerif-Bold.ttf','liberation-mono-fonts/LiberationMono-Regular.ttf']]
write('pdf-qa.json',{'pages':7,'render_command':'pdftoppm -scale-to 1250 -png paper.pdf render/page','visually_inspected_pages':[1,2,3,4,5,6,7],'final_verdict':'PASS: no clipping, overlap, missing glyphs or unreadable notation after final rerender','paper_sha256':H(L/'paper.pdf'),'fonts':{str(p):H(p) for p in fonts},'source':'paper.py','reportlab':'4.4.9'})
# Tiny exact input excerpts, not unrelated dossiers or source PDF copies.
shutil.copyfile(B/'expanded-corpus-r40/raw/347712.jsonl',L/'evidence/347712.jsonl')
s=(B/'expanded-corpus-r40/PROOF-ATTEMPTS.md').read_text();(L/'evidence/author-exact-entry.md').write_text(s[s.index('## 347712'):s.index('## 347913')])
receipts=[]
for lane in ['expanded-corpus-r40','latin-source-significance-review-r1']:
 for p in sorted((B/lane).glob('*receipts.json')):
  try:d=json.loads(p.read_text())
  except ValueError:continue
  def walk(x):
   if isinstance(x,dict):
    if any(term in str(x.get('url','')).lower() for term in ['2008.11448','haystack','rsa.21114','icalp.2021.58','1811.09040']):receipts.append({'original_receipt':str(p),'original_receipt_sha256':H(p),'record':x})
    else:
     for v in x.values():walk(v)
   elif isinstance(x,list):
    for v in x:walk(v)
  walk(d)
write('source-receipt-excerpts.json',receipts)
result={'mathdb_id':347712,'task':'draft manuscript, package and fresh replay; not independent acceptance','scope':'Exact finite Definition 3 field / independent uniform-target interpretation only','status':'DRAFT_DOSSIER_AND_FRESH_REPLAY_PASS','accepted_credit':0,'campaign_accepted_context':'2/20 beyond39 unchanged','root_acceptance':'pending','root_final_replay':'separate, pending','endpoint':'MathDB347712.source_refutation : ¬MathDB347712.SourceClaim','supplement_endpoints':['LatinFidelity.restricted_refutation','LatinFidelity.ordinary_partition_counterexample'],'fields':[290,302],'uniform_probabilities':['29/60','151/300'],'gap':'1/50','target_totals':[[58]*5,[62,62,62,61,55]],'worst_target':['58/120','55/120'],'author_sha256':H(L/'Latin.lean'),'supplement_sha256':H(L/'Supplement.lean'),'fresh_replay':r,'frozen_before':277,'frozen_after':277,'frozen_mismatches':0,'pdf_pages':7,'pdf_visual_qa':'PASS all pages after final rerender','review_verdicts':{'source_significance':'qualified PASS; bounded novelty, no worldwide priority','fidelity_formal':'qualified PASS Definition3; HOLD unqualified/worst-target'},'caveats':['No worst-target refutation; raw MathDB distribution omitted','No exact optimum, minimal n, necessity direction, nonexistence-of-optimal-Latin, or asymptotic claim','Probability normalization ordinary, not formal probability theorem','Imported package oleans trusted, no full upstream rebuild attestation','Bounded inherited novelty review, no new global priority certification','Frozen institutional published bytes; no current Wiley authentication or complete errata search'],'no_children':True,'no_external_mutations':True,'no_running_jobs':True}
write('results.json',result)
(L/'SUMMARY.md').write_text('''# MathDB 347712 manuscript handoff

Completed: seven-page self-contained draft `paper.pdf`, reproducible ReportLab
source `paper.py`, transparent 120-permutation certificate, unchanged two-module
`proof-source.zip`, strict safe extracted replay and source-only `dossier.zip`.

Fresh replay PASS: 22 author + 17 supplement local-origin declarations, including
generated helpers, audited with full types and transitive axioms; only propext,
Classical.choice, Quot.sound. Both strict Lean compiles and both leanchecker runs
exit 0. Both deliberate negative controls rejected (exit 1). Every Lean/checker
process used <=2 CPUs, 8 GiB AS, 100 CPU seconds, 110 wall seconds; Lean -j1 and
warningAsError=true. Full logs and dependency provenance retained in replay-*/.
No author replay.py was executed. No upstream own-project objects imported.
Imported dependency olean-cache trust remains; no full upstream rebuild claim.

Finite Definition 3 field / uniform-target scope only: fields 290 < 302;
probabilities 29/60 < 151/300, gap 1/50. Both partitions nonempty and Latin.
Worst-target comparison goes the other way: 58/120 > 55/120. This does not settle
that objective or every interpretation of the raw MathDB wording. Probability
normalization is ordinary mathematics. No optimum, minimal n, necessity-direction,
nonexistence-of-optimal-Latin, asymptotic, or worldwide priority claim.

Both independent reviews remain qualified PASS; fidelity's unqualified/worst-target
HOLD is retained. Root final replay and acceptance are separate and pending.
Accepted credit **0**, context **2/20 beyond39 unchanged**. All **277/277** frozen
bindings match before and after. Both Lean sources byte-identical to frozen pins.
All seven final PDF pages visually inspected; unsupported glyphs corrected and
rerendered. No children, git, shared/author/review edits, browser tabs, external
messages, publication or uploads. No running jobs at handoff.

See README.md for exact commands, review links, source provenance, package contents
and caveats. External manifest.json binds the PDF, both ZIPs and authoritative
frozen source originals. package-manifest.json is the internal payload manifest.
''')
# Explicitly select the package; do not recursively copy historical trees.
names=['README.md','SUMMARY.md','results.json','reservation.json','frozen-inputs.json','integrity-before.json','integrity-after.json','Latin.lean','Supplement.lean','proof-source.zip','replay.py','replay-result.json','enumerate.py','certificate.json','partition.csv','paper.py','paper.pdf','pdf-qa.json','requirements-paper.txt','lean-toolchain','lake-manifest.json','source-reference-index.json','source-receipt-excerpts.json','seal.py']
files=[L/n for n in names]+list((L/'evidence').iterdir())+list((L/'render').glob('*.png'))
files += [p for p in E.rglob('*') if p.is_file() and p.suffix not in ['.olean','.ilean','.c','.o']]
assert all(not p.is_symlink() for p in files)
payload={str(p.relative_to(L)):H(p) for p in sorted(files)}
write('package-manifest.json',{'payload_sha256':payload,'frozen_authoritative_source_sha256':f,'note':'Excludes itself and external ZIP to avoid self-reference; final manifest.json binds both archives.'})
files.append(L/'package-manifest.json')
with zipfile.ZipFile(L/'dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,str(p.relative_to(L)))
write('manifest.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{str(p.relative_to(L)):H(p) for p in sorted(files+[L/'dossier.zip'])},'authoritative_frozen_sources':f,'archives':{'proof-source.zip':H(L/'proof-source.zip'),'dossier.zip':H(L/'dossier.zip')},'self_excluded':True,'accepted_credit':0})
with zipfile.ZipFile(L/'dossier.zip') as z:
 assert z.testzip() is None
 assert not any(Path(n).suffix in ['.olean','.ilean','.o'] for n in z.namelist())
print(json.dumps({'frozen':len(f),'mismatches':bad,'archives':json.loads((L/'manifest.json').read_text())['archives'],'dossier_entries':len(files),'replay':r['status']},indent=2))

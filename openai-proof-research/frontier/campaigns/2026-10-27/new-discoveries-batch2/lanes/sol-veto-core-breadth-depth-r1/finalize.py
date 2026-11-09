from pathlib import Path
import json,hashlib,datetime,re
O=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
http=[json.loads(x) for x in (O/'http.jsonl').read_text().splitlines()]
for r in http:
 p=O/r['path'];assert sha(p)==r['sha256']
 f=O/'frozen'/p.name
 if not f.exists():f.write_bytes(p.read_bytes())
 assert sha(f)==r['sha256']
versions=[]
for p in sorted((O/'sources').glob('*abs*')):
 s=p.read_text(errors='replace');body=s.split('Submission history')[-1].split('Access Paper')[0]
 versions.append({'file':str(p.relative_to(O)),'sha256':sha(p),'history_text':re.sub('<[^>]*>',' ',body).strip()[:2000]})
(O/'source-versions.json').write_text(json.dumps(versions,indent=2))
bindings=json.loads((O/'input-bindings.json').read_text())
for r in bindings:
 for key in ['original','frozen','working']:
  p=Path(r[key]) if key=='original' else O/r[key]
  assert sha(p)==r['sha256'],(key,p)
guard=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(O/'guard-copy.py').write_bytes(guard.read_bytes())
provenance={
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'proposed complete ordinary proof; independent review/priority clearance pending',
 'target':{'author':'M. August Rossi','url':'https://arxiv.org/abs/2610.26535v1','version':'v1','submitted_utc':'2026-10-19T14:58:48Z','statement':'unnumbered conjecture after Lemma5, printed p9','pdf':'frozen/1-veto.pdf','pdf_sha256':sha(O/'frozen/1-veto.pdf')},
 'guard':{'path':str(guard),'sha256':sha(guard),'limits':{'AS_bytes':536870912,'sampled_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'instruction':'all replay commands below must be wrapped by this guard; do not raise caps'},
 'input_bindings':'input-bindings.json','http':'http.jsonl','versions':'source-versions.json','history':'history-screen.json',
 'administrative':{'snapshot_only':True,'bound_as_scientific_inputs':False,'root_alone_accepts_counts_stages':True,'snapshot_counts':'9 additional /39 total, next40; no changes'},
 'proof_dependencies':['weighted Hall / fractional matching equivalence (Rossi Lemma1/Proposition3)','Berger et al. 2307.07495v3 Section3.1 is credited comparison, metric inequalities rederived','Rossi Lemma5 supplies already-public sharpness'],
 'body_read_scope':{'Rossi':'definitions, Lemma1/Proposition3, full Lemmas4/5 and conjecture, regularization discussion','Berger':'complete Section3.1 coupling/metric proof, general-weight statement','k-ApprovalVeto':'core/distortion definitions, Theorem1, utilitarian/proportional proof and percentile contexts','other_scouts':'relevant definitions, theorem statements, proof mechanisms and actual question contexts, not every auxiliary proof'},
 'limits':['no independent adversarial review','no Lean or manuscript','no MathSciNet/zbMATH or comprehensive history clearance','current public proof registries inaccessible under inherited denials; no denied route retried','new PDFs are arXiv versions; publisher versions not independently authenticated','finite LP checks are floating diagnostics, not proof','initial unguarded read-only discovery and initial text-read-before-freeze deviations retained in progress.md'],
 'manifest_exclusions':['finalmanifest.json','verification-receipt.json'],
 'external_actions':{'browser':False,'git':False,'messages_posts_uploads':False,'MathDB_edits':False,'children':False},
}
(O/'provenance.json').write_text(json.dumps(provenance,indent=2))
files={str(p.relative_to(O)):sha(p) for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(O/'finalmanifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exclusions':['finalmanifest.json','verification-receipt.json'],'files':files},indent=2))
print('finalized',len(files),'files; assigned originals/copies unchanged')

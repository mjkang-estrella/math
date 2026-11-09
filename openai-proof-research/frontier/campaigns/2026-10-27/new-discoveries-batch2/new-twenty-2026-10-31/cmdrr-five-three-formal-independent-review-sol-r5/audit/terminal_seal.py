from pathlib import Path
import json,hashlib,os,subprocess
root=Path.cwd()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
order=json.loads(Path('SOURCE-ORDER.json').read_text()); replay=json.loads(Path('results/FRESH-REPLAY.json').read_text())
for m in order:
 s=Path('src')/(m+'.lean');o=Path('build')/(m+'.olean')
 assert sha(s)==sha(Path('inputs/author-src')/(m+'.lean'))==replay['sources_after_checkers'][m]
 assert sha(o)==replay['oleans_after_checkers'][m]
for p in Path('receipt').glob('*.json'):
 d=json.loads(p.read_text());assert d['group_members_left']==[];assert sha(Path(d['log']))==d['log_sha256']
frozen=json.loads(Path('frozen-after.json').read_text());assert not frozen['mismatches']
review=json.loads(Path('review.json').read_text());assert review['326555']['gates']['overall_recommendation']['complete_independent_final_review'] is False
active=list(Path('logs').glob('*_terminal_seal.log'));assert len(active)==1
log=active[0]; receipt=Path('receipt')/(log.stem+'.json')
exclusions=['SHA256-MANIFEST.json',str(log),str(receipt)]
files=[]
for p in root.iterdir():
 assert not p.is_symlink(),p
 if p.is_file():files.append(p)
allowed=['audit','build','cache','inputs','logs','output','receipt','results','src','tmp']
for d in allowed:
 for base,dirs,names in os.walk(root/d,followlinks=False):
  for n in dirs:assert not (Path(base)/n).is_symlink()
  for n in names:
   p=Path(base)/n;assert not p.is_symlink();files.append(p)
manifest={str(p.relative_to(root)):sha(p) for p in sorted(files) if str(p.relative_to(root)) not in exclusions}
obj={'scope':'Actual files in this lane only; no external provenance reads. Includes frozen copies, helpers, pins, plans, sources, own oleans, completed receipts/logs, renders and reports.','files':manifest,'exact_terminal_noncircular_exclusions':exclusions,'exclusion_reason':'The manifest cannot hash itself; terminal runner log and receipt are finalized after this child returns. No other future file or generic directory exclusion.','frozen_after':frozen,'post_checker_source_olean_hashes_verified':True,'all_completed_runner_groups_empty':True,'final_review_status':'INCOMPLETE_REVISE_HOLD','credit':0}
subprocess.run(['python3','-I','-B','write_lane.py','SHA256-MANIFEST.json'],input=json.dumps(obj,indent=2)+'\n',text=True,check=True)
print('SEALED',len(manifest),'FILES','EXCLUSIONS',json.dumps(exclusions),'MANIFEST_SHA256',sha(Path('SHA256-MANIFEST.json')))
print('All completed runner groups empty; this terminal runner must still finish and reap its child. Review INCOMPLETE, credit0, campaign55/60 beyond39.')

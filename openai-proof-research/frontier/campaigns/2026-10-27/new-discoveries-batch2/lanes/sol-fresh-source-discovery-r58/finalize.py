from pathlib import Path
import hashlib,json,datetime,shutil
P=Path(__file__).resolve().parent
v=json.loads((P/'checks.json').read_text());n=len(v['rows']);assert n==33
for name in ['SUMMARY.md','discovery.md']:
 f=P/name;s=f.read_text().replace('34 rectangles','33 rectangles').replace('checks34 rectangles','checks33 rectangles').replace('pp11–13','pp12–14');f.write_text(s)
for k in ['omega-main','openai','aim','count']:
 src=P.parent/'sol-fresh-source-discovery-r56'/'sources'/(k+'-head.json');shutil.copyfile(src,P/'sources'/(k+'-head-CACHED-r56.json'))
files={}
for f in sorted(P.rglob('*')):
 if f.is_file() and '__pycache__' not in f.parts and f.name!='provenance.json':
  b=f.read_bytes();files[str(f.relative_to(P))]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
events=[json.loads(s) for s in (P/'http.jsonl').read_text().splitlines()]
head=json.loads((P/'sources/omega-head.json').read_text())
meta=dict(lane=str(P),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),target='Alofi-Dukes arXiv2411.02667v1 Conjecture13',status='unresolved',credit=0,nomination=False,PROOF_md=False,counts_unchanged=dict(additional=6,total=36),candidate_count=1,source_qualification='expert/published author conjecture; actual journal-body comparison HOLD',remaining_gap='Uniform central pair-sum fiber inequality or another full proof/refutation; current broad registry/publication-body coverage incomplete',current_omega=dict(sha=head['sha'],commit_utc=head['commit']['committer']['date']),other_heads='Current refresh failed shared API403; r56 cached heads are explicitly NOT current-verified',coverage_limits=json.loads((P/'registry-screen.json').read_text())['limits'],failures=[x for x in events if 'error' in x],resource_policy=dict(AS_bytes=536870912,CPU_seconds=210,wall_seconds=230,process_group_sampled_RSS_bytes=536870912,BLAS_threads=1),checks=dict(rectangles=n,ordered_pairs=sum(x['pairs'] for x in v['fibers']),fibers=sum(x['fibers'] for x in v['fibers'])),files=files)
(P/'provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:meta[k] for k in ['utc','status','checks','credit']}))

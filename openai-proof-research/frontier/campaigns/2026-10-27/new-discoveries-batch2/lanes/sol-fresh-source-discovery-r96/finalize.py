from pathlib import Path
import hashlib,json,datetime,re
P=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
root=next(f for f in P.parents if f.name=='openai-proof-research')
ctx={}
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/NEXT.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']:
 f=root/rel;ctx[rel]=sha(f)
http=json.loads((P/'http.json').read_text())
heads={n:json.loads((P/'sources'/(n+'_head.json')).read_text())['sha'] for n in ['omega','openai']}
d=json.loads((P/'sources/omega-full-delta.json').read_text())
pat=re.compile(r'melonic|clasped|2503[.]16296|367609|2502[.]08948|2509[.]16868|Links.Gould|Ishii',re.I)
hits=[]
for f in (P/'sources').glob('omega-*-body-*'):
 for i,l in enumerate(f.read_text(errors='replace').splitlines(),1):
  if pat.search(l):hits.append(dict(file=f.name,line=i,text=l[:500]))
prov=dict(lane=P.name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='UNRESOLVED',credit=0,counts={'additional':8,'total':38},context_sha256=ctx,source_requests=http,heads=heads,registry_coverage={'frozen_omega':'1b999d9fda71df7537b62327147496d64a6f66ef','compare_total_commits':d.get('total_commits'),'returned_files':len(d.get('files',[])),'potential_300_file_truncation':True,'complete_current_semantic_coverage':False,'saved_changed_body_keyword_hits':hits,'novelty_clearance':False},resource={'guard_sha256':sha(P/'helper_guard.py'),'AS_and_group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1,'sampled_RSS_limit_not_continuous':True},proof=False,lean=False,paper=False,external_mutations=False)
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
for manifest,files in [('sourcebytes.sha256',sorted((P/'sources').rglob('*'))),('manifest.sha256',sorted(P.rglob('*')))]:
 lines=[]
 for f in files:
  if not f.is_file() or '__pycache__' in f.parts or f.name in ['manifest.sha256','replay.log']:continue
  lines.append(sha(f)+'  '+str(f.relative_to(P)))
 (P/manifest).write_text('\n'.join(lines)+'\n')
print('finalized',len(http),'HTTP records',heads,'delta hits',len(hits))

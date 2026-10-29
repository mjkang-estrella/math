from pathlib import Path
import json,hashlib,re,datetime,shutil
P=Path(__file__).resolve().parent;B=P.parent.parent;R=B.parents[3]
# Resolve from known workspace ancestry without writing outside this lane.
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
old=B/'lanes/sol-fresh-analysis-source-r22/sources'
for n in ['aim-full-current-tree.json','count-count-full-tree.json','openai-openai-preprints-tree.json','aim-head.json','count-head.json','openai-head.json','aim-root.json','count-root.json','openai-root.json']:
 shutil.copyfile(old/n,P/'sources'/('inherited-'+n))
terms=r'sakaguchi|lupa[sşș]|tayyah|hankel|univalent|schwarz|starlike|symmetric.?domain'
files=['omega-D5.json','omega-Problems.json','omega-main-full.json','inherited-aim-full-current-tree.json','inherited-count-count-full-tree.json','inherited-openai-openai-preprints-tree.json']
screen=[]
for f in files:
 j=json.loads((P/'sources'/f).read_text());assert not j['truncated']
 screen.append({'file':f,'sha':j['sha'],'entries':len(j['tree']),'truncated':False,'matched_paths':[x['path'] for x in j['tree'] if re.search(terms,x['path'],re.I)],'scope':'complete named subtree path inventory; not exhaustive body review'})
(P/'registry-screen.json').write_text(json.dumps(screen,indent=2))
heads={}
for name in ['omega-dev','omega-main','openai','aim','count']:
 heads[name]=re.findall(r'"currentOid":"([a-f0-9]+)"',(P/'sources'/(name+'.html')).read_text())[0]
assert heads['omega-dev']==json.loads((P/'sources/omega-root.json').read_text())['sha']
for name in ['openai','aim','count']:
 assert heads[name]==json.loads((P/'sources'/('inherited-'+name+'-head.json')).read_text())['sha']
def hashed(f):
 b=f.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
inputs=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']+list((B/'lanes').glob('sol-fresh*/SUMMARY.md'))+[B/'lanes/pi-han-pedon-higher-shifts-r1/SUMMARY.md']
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete ordinary counterexample for displayed source class; literal-source/prior/substantive HOLD; credit0','write_scope':str(P),'registry_heads':heads,'inventories':'registry-screen.json','http_log':'http.json','source_target':{'original':'https://doi.org/10.3390/sym17081244','original_date':'2025-08-05','label':'Conjecture1','followup':'https://doi.org/10.3390/sym18081307','followup_date':'2026-08-03','label_followup':'Conjecture1 pp2–4, Theorem1','direct_bytes_obtained':False,'body_scope':'indexed actual mathematical passages only; no full-PDF source clearance','witness_H':'-769/12288','strict_gap':'1/12288'},'strongest_objection':'Short Schur-boundary witness exactly attains already-published2026 upper bound; routine missed equality case eligibility objection unresolved. Direct source files403; full correction/conclusion history unread.','coverage_gaps':['Whole dev recursive root truncated; current complete D5/Problems only, not every auxiliary directory','Original2025 and followup2026 full direct bodies403; indexed passages only','No exhaustive semantic registry search, citing-body or specialist database review','No worldwide priority guarantee','No independent adversarial review or formal certificate'],'resource_limits':{'AS_bytes':536870912,'CPU_seconds':20,'internal_wall_seconds':25,'outer_wall_seconds':30,'BLAS_threads':1},'formal':{'run':False,'certificate':False,'plan':'LEAN-BRIDGE-PLAN.md'},'inherited_inputs':{str(f.relative_to(R)):hashed(f) for f in inputs},'artifacts':{str(f.relative_to(P)):hashed(f) for f in P.rglob('*') if f.is_file() and f.name!='provenance.json'}}
(P/'provenance.json').write_text(json.dumps(prov,indent=2))
print(json.dumps({'heads':heads,'complete_inventories':[(r['file'],r['entries']) for r in screen],'artifacts':len(prov['artifacts']),'status':prov['status']},indent=2))

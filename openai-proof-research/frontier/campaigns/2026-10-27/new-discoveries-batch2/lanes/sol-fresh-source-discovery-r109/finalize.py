from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent;R=Path('openai-proof-research').resolve();B=P.parent.parent
G=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(65536),b''):h.update(b)
 return h.hexdigest()
inputs=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',G,B/'lanes/sol-fresh-source-discovery-r106/http.json',B/'lanes/sol-fresh-source-discovery-r106/SUMMARY.md',B/'lanes/sol-fresh-source-discovery-r95/discovery.md',B/'lanes/sol-fresh-source-discovery-r69/discovery.md',B/'lanes/sol-fresh-source-discovery-r103/discovery.md',R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing/tools/scripts/agent/openproblem/SCREENED-OUT-R71.md']
# Read all structured governing records, recording keys, not dumping their large buffers.
read_summary={}
for f in inputs:
 if f.suffix=='.json':
  data=json.loads(f.read_text());read_summary[str(f.relative_to(R))]=list(data) if isinstance(data,dict) else {'records':len(data)}
(P/'context-read.json').write_text(json.dumps(read_summary,indent=2))
(P/'inputbytes.sha256').write_text(''.join(sha(f)+'  '+str(f)+'\n' for f in inputs))
sources=sorted((P/'sources').glob('*'))
(P/'sourcebytes.sha256').write_text(''.join(sha(f)+'  '+str(f.relative_to(P))+'\n' for f in sources if f.is_file()))
http=[]
for f in sorted(P.glob('http*.json')):http.extend(json.loads(f.read_text()))
prov={'lane':P.name,'finalized_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':{'additional':8,'total':38,'changed':False},'selected':'Fryš–Kotrbatý2609.08612v2 Conjecture1.11, full optimized-translation higher-order unbalanced join','full_ordinary_result':False,'no_PROOF_Lean_paper':True,'guard':{'path':str(G),'sha256':sha(G),'AS_and_group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'nominal_sampling_seconds':0.04,'BLAS_threads':1,'unchanged':True},'duplicate_screens':[json.loads((P/x).read_text()) for x in ['duplicate-audit.json','join-audit.json']],'http_receipts':http,'registry':{'status':'HOLD','new_requests':0,'reason':'Known r105/r106403; no recorded reset located. No alternate endpoint or retry. Current absence not cleared.','historical_Omega':'73a5033dd654a16a14fcd1b13277f1a03d81d82619','historical_OpenAI':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','baseline_and_chain_limit':'18:13 complete paths plus bounded dated chains; unresolved300cap; no semantic absence clearance'},'checks':{'status':'PASS diagnostics only','simplex_hulls':64,'bound_identities':120,'square_fibres':4},'failures':['compact-failed.py missing optional bs4; traceback retained in compact.guard.json; standard-library replacement passed'],'gap':'Uniform optimized-translation volume comparison, or a strict all-translation lower certificate for a concrete convex body.','strongest_objection':'Known implication join=>mixed volumes is not reversible; candidate routes discard translation geometry.','restrictions':{'children':0,'git':False,'shared_writes':False,'browser':False,'external_posting':False}}
(P/'provenance.json').write_text(json.dumps(prov,indent=2,ensure_ascii=False))
with (P/'manifest.sha256').open('w') as out:
 for f in sorted(P.rglob('*')):
  if f.is_file() and f.name not in ['manifest.sha256','finalize.log','finalize.guard.json']:out.write(sha(f)+'  '+str(f.relative_to(P))+'\n')
print('finalized',len(http),'HTTP receipts;',len(sources),'source files; credit0')

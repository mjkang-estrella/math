import pathlib,json,hashlib,datetime,sys,platform
from html.parser import HTMLParser
D=pathlib.Path(__file__).resolve().parent
ROOT=D.parents[5]
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):self.a.append(d)
for name in ['shankar','shankar-original']:
 p=Extract();p.feed((D/'source-evidence'/f'{name}.html').read_text());s=' '.join(' '.join(p.a).split());(D/'source-evidence'/f'{name}.txt').write_text(s)
# Context json is parsed fully, and a bounded current reconciliation retained.
batch=D.parent.parent
ledger=json.loads((batch/'ledger.json').read_text());prior=json.loads((batch/'prior-campaign-context.json').read_text())
context={'ledger':{k:ledger.get(k) for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},'prior_context_top_keys':list(prior),'notes':'NEXT read through tool; initial terminal output truncated; no claim that all historical lines were manually read.'}
(D/'context-read.json').write_text(json.dumps(context,indent=2))
reg=batch/'lanes/root-edge-irregulator-current-prior-r1'
inputs=[batch/'AGENTS.md',batch/'ledger.json',batch/'prior-campaign-context.json',batch/'NEXT.md',reg/'CURRENT-REGISTRIES.json',reg/'omega-tree.txt',reg/'openai-tree.txt',reg/'openai-CONTENTS.md']
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'credit':0,'status':'unresolved','target':'Shankar arXiv2609.15651v1 Conjecture1','http':json.loads((D/'http.json').read_text()),'registry':json.loads((reg/'CURRENT-REGISTRIES.json').read_text()),'registry_limits':'Read-only dated17:20UTC inventories; heads not refreshed here; path absence is not semantic/global novelty clearance; selected bodies only.','access_limits':'No API calls, retries, alternate proxies, browser tabs, account/contact/public mutations or git operations. Direct HTTP bodies200; no challenge markers detected.','resource_caps':{'address_space_bytes':536870912,'process_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'sample_interval_seconds':0.04,'BLAS_threads':1,'http_response_cap_bytes':3000000},'deviations':['Initial administrative context/listing output truncated; retained bounded filename artifacts.','Initial bare15031 duplicate expression matched unrelated numeric JSON; narrowed exact title/IDs before target selection.','Not a global prior-art clearance or latest-head assertion.'],'context_hashes':{str(p):digest(p) for p in inputs},'search_urls':['https://arxiv.org/abs/2609.15651','https://arxiv.org/html/2609.39917v1','https://www.combinatorics.org/ojs/index.php/eljc/article/view/v33i3p43'],'search_limits':'Web discovery/primary HTML reads recorded in discovery.md; secondary returned summaries not used as theorem evidence.'}
prov['files']={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':digest(p)} for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['provenance.json','seal.log','seal.guard.json']}
(D/'provenance.json').write_text(json.dumps(prov,indent=2))
print(json.dumps({'sealed_files':len(prov['files']),'utc':prov['utc'],'context':context}))

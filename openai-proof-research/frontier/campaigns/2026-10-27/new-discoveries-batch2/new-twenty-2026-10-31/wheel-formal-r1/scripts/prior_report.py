from pathlib import Path
import json,hashlib,re,datetime
D=Path(__file__).resolve().parent.parent
S=D/'sources'
repos={}
for k,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('authors','Shivaramkratos/Ultimate_Independence_ratio_Python_Gurobi_code')]:
 h=json.loads((S/(k+'-head.json')).read_text())
 repos[k]={'repository':r,'head':h['sha'],'commit_time':h['commit']['committer']['date'],'head_route':'https://api.github.com/repos/'+r+'/commits/HEAD','trees':[]}
 for scope in ['D5','Problems','preprints','root']:
  p=S/(k+'-'+scope+'.json')
  if p.exists():
   t=json.loads(p.read_text());repos[k]['trees'].append({'scope':scope,'entries':len(t['tree']),'truncated':t['truncated'],'matches':[x['path'] for x in t['tree'] if re.search('wheel|fractional.?chrom|2511.18747',x['path'],re.I)]})
receipts=[json.loads(p.read_text())|{'receipt':str(p.relative_to(D))} for p in sorted(S.glob('*.receipt.json'))]
out={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'outcome':'No prior proof found in bounded searched scope; not exhaustive novelty clearance','arxiv':{'id':'2511.18747','current_version':'v1','history':'only v1 listed, 2025-11-24','body':'sources/source-live.html','conjecture':'7.3'},'registries':repos,'citing_works':{'index':'OpenAlex W7106693227','count':0,'query_receipt':'sources/citations.json.receipt.json'},'later_bodies_read_sections':{'2610.13852':'Introduction and graph-power definition: distance graph powers, not Cartesian powers','2607.19817':'Introduction through Theorem 1.2: graph energy versus independence number','2609.00210':'Introduction through main theorem discussion: localized Caro–Wei bound','2607.05961':'Introduction and main theorem/t-minor discussion: chromatic bound for t-perfect graphs','2607.22915':'Abstract and Introduction: oriented chromatic number'},'scope_issue':'MathDB has no explicit t range; source is odd wheels of length at least five, t>=2. Assignment extends to t>=1. t=0 is not a simple cyclic wheel and is not asserted.','access_failures': [x for x in receipts if x.get('error') or x.get('status')!=200], 'receipts':receipts}
(D/'PRIOR-ART.json').write_text(json.dumps(out,indent=2))

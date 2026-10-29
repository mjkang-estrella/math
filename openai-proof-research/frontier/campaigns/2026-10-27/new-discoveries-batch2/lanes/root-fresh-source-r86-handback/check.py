import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
import sympy as S
root=Path(__file__).resolve().parent
B=root.parents[1]; lane=root.parent/'sol-fresh-source-discovery-r86'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
manifest=json.loads((lane/'provenance.json').read_text())['files']
for row in manifest:
    assert sha(lane/row['path'])==row['sha256'],row['path']
x,s,b=S.symbols('x s b');m=S.Function('m')(x)
w=m/(1+s*m);h=(x-b)*w
wp=S.diff(m,x)/(1+s*m)**2
wpp=S.diff(m,x,2)/(1+s*m)**2-2*s*S.diff(m,x)**2/(1+s*m)**3
for expr in [S.diff(w,x)-wp,S.diff(w,x,2)-wpp,S.diff(h,x)-(w+(x-b)*wp),S.diff(h,x,2)-(2*wp+(x-b)*wpp)]:
    assert S.simplify(expr)==0
decision={'utc':datetime.now(timezone.utc).isoformat(),'status':'EXCLUDE_ROUTINE','credit':0,
 'counts':{'additional':8,'total':38},'manifest_verified':len(manifest),'root_exact_symbolic_identities':4,
 'reason':'For h=(x-b)w, w>0, w prime<0, w double-prime<=0. On x<b h prime>0; on x>=b h double-prime<0. This gives unimodality directly for every b; s=0 is constant. Source formulas provide w=(1-c*x^T)/(1+s*(1-c*x^T)).',
 'countercase':'The exact conjecture is open in the inspected paper, but the negative-gain region is handled by the same elementary derivative identity; no substantive residual inequality remains.',
 'source':'Eruguz et al., Omega128 (2024)103127 Conjecture A.1 in the linear purchase model; root read actual cached conjecture and model/appendix passages.',
 'qualifications':'Root did not repeat all 16416 worker rational tests or conduct a fresh comprehensive prior-art audit. No exact earlier published solution asserted. Hyman sample-size scope and original box-fragmentation versus successor scope remain HOLD; neither is refuted here.',
 'provenance_sha256':sha(lane/'provenance.json')}
(root/'EXCLUSION.json').write_text(json.dumps(decision,indent=2)+'\n')
ledgerpath=B/'ledger.json';ledger=json.loads(ledgerpath.read_text())
assert ledger['accepted_count']==8 and ledger['total_accepted_count']==38
entry={'id':'eruguz-linear-retail-unimodality','status':'EXCLUDE_ROUTINE','credit':0,'reason':decision['reason'],'scope_note':decision['source'],'decision':'lanes/root-fresh-source-r86-handback/EXCLUSION.json'}
if not any(v['id']==entry['id'] for v in ledger['excluded']):ledger['excluded'].append(entry)
ledgerpath.write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'pass':True,'manifest':len(manifest),'symbolic_identities':4,'credit':0}))

# MIT. Writes only this review root. Run once after final payload completion.
from pathlib import Path
import json,hashlib,datetime,runpy,stat
R=Path(__file__).resolve().parents[1]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
assert not (R/'MANIFEST.json').exists(),'already sealed'
base=R.parents[3]
before=json.loads((R/'packet/private/originals-before.json').read_text());after={}
for name in ['fresh-structural-discovery-r139','fresh-structural-discovery-r140']:
 root=R.parent/name
 for p in [root,*root.rglob('*')]:
  s=p.lstat();after[str(p.relative_to(base))]={'kind':'file' if p.is_file() else 'directory','mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,**({'sha256':h(p),'size':s.st_size} if p.is_file() else {})}
assert before==after,'current original roots changed'
bind=json.loads((R/'packet/private/input-bindings.json').read_text());observations=[]
for a in bind:
 p=base/a['original'];observations.append({'path':a['original'],'kind':a['kind'],'bound_sha256':a['sha256'],'current_sha256':h(p),'matches':h(p)==a['sha256']})
stable=[e for e in observations if e['kind']!='mutable-parent-observation']
assert all(e['matches'] for e in stable),'named nonmutable originals changed'
dump(R/'packet/private/preservation-after.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'whole_current_r139_r140_match_before':True,'entries':len(after),'named_observations':observations,'scope':'Present byte/mode/link-count preservation after reviewer baseline; not historical or whole-parent preservation','filesystem_denial_contract':False})
ns=runpy.run_path(str(R/'packet/public/verify.py'))
m={'format':'t205q140-contribution-r1-exact-v1','sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_roots':['packet','work'],'detached_exclusions':['MANIFEST.json','outsideREPORT.md','FINAL.json','ANCHORS.json','controls/'],'rights':'Private bodies and controls local only under original rights; original public review/code separately licensed','entries':ns['inventory'](R)}
dump(R/'MANIFEST.json',m)
f={'candidate':'T205Q140','review_round':'contribution-r1','verdict':'TECHNICAL','conditional_on_correctness':True,'prior_independent_objections':[],'scope_sha256':'0b57f7972d43586f721a6e1aaa42cdd6fa8c80512702f933796b82e2bcd3f6ef','author_proof_sha256':'fe18edab356729afe1c0cd96919bf20210ac7ba72c756a125495113d3f78e0ff','manifest_sha256':h(R/'MANIFEST.json'),'outside_report_sha256':h(R/'outsideREPORT.md'),'review_sha256':h(R/'packet/public/review.md'),'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'correctness_gate':'NOT_PERFORMED','acceptance':'NOT_ASSIGNED','count_change':0,'publication':'STOPPED','downstream':'NOT_OPENED','parent_alone_integrates':True}
dump(R/'FINAL.json',f)
print(json.dumps({p:h(R/p) for p in ['MANIFEST.json','outsideREPORT.md','FINAL.json']}))

"""Current selected-original stability observation. Writes only owned metadata."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;P=R.parents[3]
e=json.loads((R/'input-membership.json').read_text());observations=[]
for x in e:
 p=P/x['original'];b=p.read_bytes();h=hashlib.sha256(b).hexdigest();c=hashlib.sha256((R/x['copy']).read_bytes()).hexdigest()
 assert h==c==x['sha256'],x['original']
 observations.append({'original':x['original'],'sha256':h,'matches_initial_selected_snapshot':True,'copy_unchanged':True})
a=R.parent/'fresh-analytic-discovery-r138';anchors=json.loads((R/'incoming-authentication.json').read_text())['external_anchors']
for n,h in anchors.items():assert hashlib.sha256((a/n).read_bytes()).hexdigest()==h
v1=json.loads((R/'private/history-search.json').read_text());v2=json.loads((R/'private/history-search-v2.json').read_text())
# Metadata-only audit: no excluded file bodies are reopened.
import re
pat=re.compile(r'h138[-_]|t185r144|structural.*r144|arithmetic.*r10[89]|arithmetic.*r110|analytic.*r13[5-8]|arithmetic.*r107|structural.*r143|t177c143|t373e135|k369r134|t088p133',re.I)
audit=[]
for name,s in [('v1',v1),('v2',v2)]:
 bad=[x['path'] for x in s['admitted'] if any(pat.search(y) for y in Path(x['path']).parts)];assert not bad
 audit.append({'scan':name,'admitted_path_peer_round_matches':len(bad),'scope':'admitted path metadata only, not historical/OS/body isolation certificate'})
(R/'final-input-observations.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'selected_originals':observations,'incoming_external_envelopes_unchanged':True,'search_path_audit':audit,'limits':'Only52 explicit named current originals and copies plus3 author envelopes. Not whole author/parent/shared/OS or first-read preservation. No forbidden histories reopened.'},indent=2)+'\n')
print(json.dumps({'selected_inputs_unchanged':len(observations),'incoming_envelopes_unchanged':3,'search_admitted_prohibited_paths':0}))

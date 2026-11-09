"""Fresh arithmetic, certificate and safe extraction checks; no theorem prover or solver."""
from pathlib import Path, PurePosixPath
import json,hashlib,zipfile,stat,tarfile
from collections import Counter
p=Path(__file__).resolve().parent.parent
E=p/'evidence';h=lambda b:hashlib.sha256(b).hexdigest()
labels=json.loads((E/'joinla-review-r1/outputs/four.json').read_text())['result']['labels']
vertices=[(c,k,j) for c in range(2) for k,nn in [('u',3),('v',3),('x',2)] for j in range(nn)]
edges=[]; rows=[]
for c in range(2):
 for j in range(3):
  u,v,x,y=(c,'u',j),(c,'v',j),(c,'x',0),(c,'x',1)
  edges.extend([(u,v),(u,x),(u,y),(v,x),(v,y)])
  rows.append([c,j]+labels[len(edges)-5:len(edges)])
weights={v:sum(a for (u,w),a in zip(edges,labels) if v in (u,w)) for v in vertices}
assert sorted(labels)==list(range(1,len(edges)+1))
assert all(weights[u]!=weights[v] for u,v in edges)
assert sorted(set(weights.values()))==[45,49,84,99]
reference=json.loads((E/'joinla-review-r1/outputs/four-verified.json').read_text())
assert weights=={tuple(r['vertex']):r['weight'] for r in reference['vertices']}
T=sum(labels);Mmax=6*max(labels);Qmin=sum(range(1,13))
assert (T,Mmax,Qmin,5*Mmax-T,T+5*Qmin,3*(5*Mmax-T),2*(T+5*Qmin))==(465,180,78,435,855,1305,1710)
assert sum(weights.values())==2*T
counts=Counter(sum(v in edge for edge in edges) for v in vertices)
assert counts=={3:12,6:4}
# General identities checked as exact polynomial coefficient identities.
# From 2M=S+6Z, T=2S+M: 2*(first)+(second) gives 5M=T+12Z.
assert (2*2+1,2*(-1)+2,2*(-6))==(5,0,-12)
# 5*(6Z=M+Q) and 5M=T+12Z give 5Q=18Z-T.
assert 5*6-12==18
packet=p/'source-only.zip';assert h(packet.read_bytes())=='9b269351bf3dddcfd3e2c98e00ce50c60b9a8cf4edbb979011658c312e386d12'
dest=p/'packet-test'; entries=[]
with zipfile.ZipFile(packet) as z:
 seen=set()
 for i in z.infolist():
  name=PurePosixPath(i.filename)
  assert not name.is_absolute() and '..' not in name.parts and '\\' not in i.filename
  assert i.filename not in seen;seen.add(i.filename)
  mode=i.external_attr>>16
  assert not stat.S_ISLNK(mode)
  assert i.is_dir() or stat.S_IFMT(mode) in (0,stat.S_IFREG)
  target=dest.joinpath(*name.parts);assert target.resolve().is_relative_to(dest.resolve())
  if i.is_dir():target.mkdir(parents=True,exist_ok=True);continue
  data=z.read(i);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  entries.append({'path':i.filename,'bytes':len(data),'sha256':h(data)})
mods=sorted(dest.rglob('*.lean'));assert len(mods)==7
anti=next(f for f in mods if f.name=='Antimagic.lean')
with tarfile.open(E/'expanded-corpus-r159/lean-packet.tar') as t:
 m=next(m for m in t.getmembers() if m.name.endswith('/Antimagic.lean'))
 assert t.extractfile(m).read()==anti.read_bytes()
endpoint=next(f for f in mods if f.name=='Endpoint.lean').read_text()
assert 'theorem not_conjecture41 : ¬ Conjecture41' in endpoint
# Recompute audit closure statistics from the existing data, rather than copying counts.
audit=(E/'joinla-formal-r2/outputs/audit.tsv').read_text().splitlines()
localmods={'AntimagicBasics','AntimagicIso','Antimagic','LauShiu','Counts','Endpoint','Audit'}
parsed=[r.split('\t') for r in audit]
axioms=sorted(r[0] for r in parsed if r[2]=='axiom')
assert axioms==['Classical.choice','Quot.sound','propext']
local=[r for r in parsed if r[1] in localmods]
assert all(all(x=='false' for x in r[3:]) for r in local)
assert len(audit)==7825
# Packet producer uses a broader local-name convention; preserve both counts explicitly.
producer_local=[r for r in parsed if r[0].startswith(('Antimagic.', 'LauShiu.', 'R159.')) or r[1] in localmods]

raw=E/'expanded-corpus-r159/raw/365453.jsonl';assert len(raw.read_text().splitlines())==1
out={'vertices':len(vertices),'edges':len(edges),'component_vertices':len(vertices)//2,'component_edges':len(edges)//2,'degree_multiplicities':dict(counts),'label_sum':T,'matching_label_count':6,'matching_sum_upper':Mmax,'join_selected_count':12,'join_sum_lower':Qmin,'upper_12Z':5*Mmax-T,'lower_18Z':T+5*Qmin,'upper_36Z':3*(5*Mmax-T),'lower_36Z':2*(T+5*Qmin),'palette':sorted(set(weights.values())),'weight_total':sum(weights.values()),'table':rows,'weights':[{'vertex':list(v),'weight':weights[v]} for v in vertices],'bijection':True,'local':True,'packet_sha256':h(packet.read_bytes()),'module_count':len(mods),'raw_line_sha256':h(raw.read_bytes()),'audit_data_rows':len(audit),'audit_local_by_module':len(local),'audit_local_by_name_or_module':len(producer_local),'axioms':axioms}
(p/'receipts/arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
(p/'receipts/safe-extraction.json').write_text(json.dumps({'archive_sha256':h(packet.read_bytes()),'safe':True,'executed_packet_code':False,'members':entries},indent=2)+'\n')
print(json.dumps(out,indent=2))

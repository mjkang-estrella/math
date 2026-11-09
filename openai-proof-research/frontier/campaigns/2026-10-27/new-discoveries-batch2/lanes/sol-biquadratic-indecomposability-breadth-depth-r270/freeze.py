from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-cross-family-mechanisms-r263'/'sources'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out=[]
for p in sorted(S.iterdir()):
 if p.name.endswith(('.txt','.pdf')) and p.name.startswith(('1909.05422','1909.06707','1909.02634','1909.05987','1909.05532','1909.04281','1909.03972','1909.04918','1909.04023','1909.01893')):
  q=L/'sources'/p.name;q.parent.mkdir(exist_ok=True);a=h(p);q.write_bytes(p.read_bytes());assert a==h(p)==h(q);out.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=a,kind='scientific'))
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',L.parent/'sol-visible-lattice-breadth-depth-r267'/'SCOUTING.md',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')]:
 q=L/'context'/((p.parent.name+'-') if p.name=='AGENTS.md' else '')/p.name if p.name=='AGENTS.md' else L/'context'/p.name
 q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());out.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h(q),kind='administrative snapshot'))
(L/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('frozen',len(out),'files')

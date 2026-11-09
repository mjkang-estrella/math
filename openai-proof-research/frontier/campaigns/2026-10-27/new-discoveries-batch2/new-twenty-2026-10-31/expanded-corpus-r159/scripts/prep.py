import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
out=[]
import gzip
blocks=gzip.decompress((D/"sources/atlas.dat.gz").read_bytes()).decode().split("GRAPH ")[1:]
for block in blocks:
 ls=block.splitlines();n=int(ls[1].split()[1]);es=[tuple(map(int,l.split())) for l in ls[2:] if l.strip()]
 seen={0} if n else set()
 for _ in range(n):
  for a,b in es:
   if a in seen or b in seen:seen.update([a,b])
 if n and len(seen)==n:out.append([n,es])
(D/'outputs/atlas.json').write_text(json.dumps(out))
with (D/'outputs/atlas.txt').open('w') as f:
 for n,es in out:f.write(str(n)+' '+str(len(es))+' '+' '.join(str(x) for e in es for x in e)+'\n')
print('connected atlas graphs',len(out))
for name in ['registry-openai','registry-omega']:
 o=json.loads((D/f'sources/{name}.json').read_text());print(name,o['sha'])
# Produce manageable historical matches; numeric substring matches in giant embedded dumps are not ID evidence.
lines=(D/'history-matches.txt').read_text().splitlines()
with (D/'outputs/history-screen.txt').open('w') as f:
 for l in lines:
  if len(l)<15000:f.write(l+'\n')
  else:f.write(l.split(':',2)[0]+': oversized line; numeric substring only, not cleared by this scan\n')
# Ledger/status evidence read and compacted without changing shared files.
for p in [B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json']:
 o=json.loads(p.read_text());print(str(p),hashlib.sha256(p.read_bytes()).hexdigest(),list(o)[:15])
 text=json.dumps(o,ensure_ascii=False,indent=2)
 (D/'outputs'/('read-'+p.parent.name+'-'+p.name)).write_text(text)

import pathlib,re,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
# All current conjecture paragraphs, for review without repeated cross-references.
for p in (D/'sources').glob('25*.txt'):
 if 'abs' in p.name:continue
 t=p.read_text();parts=[]
 for m in re.finditer(r'Conjecture \d+(?:\.\d+)*\s*\.',t):parts.append(t[max(0,m.start()-60):m.start()+1200])
 (D/'outputs'/(p.stem+'-claims.txt')).write_text('\n\n'.join(parts))
# Record read-only ledger families, no shared file writes.
ps=[D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']
out=[]
for p in ps:
 if p.exists():
  b=p.read_bytes();x=json.loads(b);out.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'top_keys':list(x),'accepted':x.get('accepted',[]),'excluded':x.get('excluded',x.get('rejected',[]))})
(D/'outputs/inherited-ledgers.json').write_text(json.dumps(out,indent=2))

import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
ids=json.loads((D/'reservation.json').read_text())['ids']; pattern=re.compile(r'(?<![0-9])(?:'+ '|'.join(map(str,ids))+r')(?![0-9])')
h=[]
for line in (D/'history-matches.txt').read_text().splitlines():
 if len(line)<16000 and pattern.search(line) and '/expanded-corpus-r169/' not in line:h.append(line)
(D/'outputs/history-exact.txt').write_text('\n'.join(h)+'\n')
for i in [324356,328427,328049,332071,334946,367132,369727,360376]:
 lines=(D/f'sources/{i}.txt').read_text().splitlines(); print('\nID',i)
 for j,l in enumerate(lines):
  if re.match(r'^Conjecture|^Problem|^Question',l):print('\n'.join(lines[max(0,j-3):j+16]))
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 o=json.loads(p.read_text()); (D/'outputs'/(p.parent.name+'-'+p.name)).write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'accepted':o.get('accepted',[]),'excluded':o.get('excluded',[]),'counting_standard':o.get('counting_standard')},indent=2))

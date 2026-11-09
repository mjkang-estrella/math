import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
out={}
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 data=p.read_bytes();j=json.loads(data)
 out[str(p)]={'sha256':hashlib.sha256(data).hexdigest(),'accepted':j.get('accepted',j) if isinstance(j,dict) else j,'excluded_after_review':j.get('excluded_after_review',{}) if isinstance(j,dict) else {}}
(D/'outputs/context-ledgers.json').write_text(json.dumps(out,indent=2))
lines=(D/'history-matches.txt').read_text().splitlines();ids=json.loads((D/'reservation.json').read_text())['ids'];hits={str(i):[] for i in ids}
for l in lines:
 for i in ids:
  if re.search(r'(?<![a-zA-Z0-9])'+str(i)+r'(?![a-zA-Z0-9])',l) and len(l)<2000 and '/expanded-corpus-r196/' not in l:hits[str(i)].append(l)
(D/'outputs/history-screen.json').write_text(json.dumps(hits,indent=2))
for i,h in hits.items():print(i,len(h),h[:2])

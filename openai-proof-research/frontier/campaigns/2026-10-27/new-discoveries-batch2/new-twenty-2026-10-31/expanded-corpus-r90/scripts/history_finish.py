from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());pat='|'.join(r'\b'+i+r'\b' for i in x)+'|'+'|'.join(re.escape(o['title']) for o in x.values())
lines=[l for l in (D/'history-matches.txt').read_text().splitlines() if re.search(pat,l,re.I)]
(D/'outputs/history-exact.txt').write_text('\n'.join(lines)+'\n')
review={'scope':'Read-only structured snapshots of accepted/excluded/candidate families. Initial fixed ID/title rg over batch2 completed. Wider all-campaign exact-regex scan hit wall cap with no committed results; not claimed complete.'}
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 b=p.read_bytes();o=json.loads(b);review[str(p.resolve())]={'sha256':hashlib.sha256(b).hexdigest(),'accepted':o.get('accepted',[]),'excluded':o.get('excluded',[]),'candidates':o.get('candidates',[])}
(D/'outputs/inherited-family-review.json').write_text(json.dumps(review,indent=2)+'\n')
print('exact historical matches',len(lines))

import json,pathlib,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
out={}
for p in [B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json']:
 o=json.loads(p.read_text());out[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'accepted':o.get('accepted'), 'excluded_after_review':o.get('excluded_after_review'),'rejected':o.get('rejected'),'keys':list(o)}
(D/'outputs/inherited-families.json').write_text(json.dumps(out,indent=2))
# exact ID boundaries to remove incidental digit matches
s=(D/'history-matches.txt').read_text();ids=json.loads((D/'reservation.json').read_text())['ids'];lines=[l for l in s.splitlines() if any(re.search(r'(?<!\d)'+str(i)+r'(?!\d)',l) for i in ids)]
(D/'outputs/history-relevant.txt').write_text('\n'.join(lines)+'\n');print('\n'.join(lines)[:5000])

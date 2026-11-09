from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());lines=(D/'history-matches.txt').read_text().splitlines();out={}
for i,o in x.items():
 hits=[l for l in lines if re.search(r'(?<!\d)'+i+r'(?!\d)',l) or o['title'].casefold() in l.casefold()]
 substantive=[l for l in hits if 'ledger.json:' not in l and 'review-freeze.json:' not in l and '"sha256"' not in l]
 out[i]={'literal_boundary_hits':len(hits),'nonledger_nonhash_matches':substantive,'interpretation':'373707 inherited exclusion retained; remaining matches are bounded history search only, not global novelty clearance' if i=='373707' else 'No exclusion inferred from numerical substring matches or assignment mentions.'}
(D/'outputs/history-screen.json').write_text(json.dumps(out,indent=2))
print({i:len(o['nonledger_nonhash_matches']) for i,o in out.items()})

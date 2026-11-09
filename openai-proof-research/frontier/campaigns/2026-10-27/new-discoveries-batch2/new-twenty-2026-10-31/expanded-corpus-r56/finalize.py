from pathlib import Path
import json,hashlib,datetime
w=Path(__file__).resolve().parent;d=json.loads((w/'results.json').read_text());hist={i:[] for i in d}
for line in (w/'history-rg.log').read_text().splitlines():
 path,num,token=line.rsplit(':',2)
 if token not in d:continue
 kind='current reservation administrative listing' if path.endswith('/ledger.json') else 'false positive decimal fragment; actual line read, unrelated to MathDB claim'
 hist[token].append(dict(path=path,line=int(num),match=token,classification=kind,substantive_inherited_match=False))
for i,v in d.items():v['inherited_matches']=hist[i];v['historical_search']='history-rg.log and history-matches.json: completed bounded ID/title search over campaign .md and result/review/ledger/context JSON files; earlier Python scans terminated without results';v['inherited_substantive_matches_found']=False
(w/'results.json').write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');(w/'history-matches.json').write_text(json.dumps(hist,indent=2))
(w/'search-notes.json').write_text(json.dumps(dict(date='2026-11-01',method='web search tool; results are leads, not downloaded-source hashes',queries=['"2402.00237" counterexample conjecture','"r(G)" "2er" snarks resistance','"ribbon partitions" "Catalan" Armstrong conjecture','"Allie" "note on reducing resistance" snarks pdf','"snarks" "resistance 3" edge reduction','"Small snarks with large oddness" arxiv','"beta shift" "minimal forbidden" words'],primary_leads=[dict(url='https://www.ajol.info/index.php/qm/article/view/254691',depth='primary abstract only; vertex-reduction normalization differs, no body clearance'),dict(url='https://sites.math.northwestern.edu/~kra/papers/strong-shift-approx.pdf',depth='search-exposed Lemma 5.5 proof lead; full PDF not downloaded or audited; no top-address subsumption established'),dict(url='https://doi.org/10.1007/s00026-026-00819-9',depth='published Armstrong version lead only; full published body unread')],status='Search output does not supply byte-authenticated HTTP status/hash receipts; no hashes invented. Downloaded primary-body receipts are in sources/.'),indent=2))
print('validated exact IDs',len(d));assert len(d)==40;assert all(v['accepted_credit']==0 for v in d.values())

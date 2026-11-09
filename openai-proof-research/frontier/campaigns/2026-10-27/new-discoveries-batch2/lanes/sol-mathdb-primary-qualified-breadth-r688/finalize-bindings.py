import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;B=L.parent
p=O/'flat-bindings.json';rows=json.loads(p.read_text());d={r['path']:r for r in rows}
for ref in [B/'AGENTS.md',B.parents[3]/'AGENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if ref.exists():
  bb=ref.read_bytes();d[str(ref)]={'path':str(ref),'sha256':hashlib.sha256(bb).hexdigest(),'size':len(bb)}
p.write_text(json.dumps(list(d.values()),indent=2)+'\n')
# Source/reporting chronology and explicit local proof coverage, not novelty clearance.
(O/'primary-review-notes.json').write_text(json.dumps({'sources':[{'report':'10.4171/OWR/2024/6','record_ids':[404644,404646,404659,404660],'coverage':'selected definitions, statements and source-internal finite criterion only; neither full report nor referenced proof bodies read'},{'report':'10.4171/OWR/2025/42','record_ids':[404948,404961],'coverage':'selected theorem/conjecture passages only; authorship/resolution reported in primary text; underlying published proof bodies unread'},{'report':'10.4171/OWR/2025/43','record_ids':[404969],'coverage':'selected diameter formula at physical page22 and reference at page23; no full-body or successor-body clearance'}],'obligations_if_reopened':['exact source scope and omitted hypotheses','closest successor proof bodies and routine-subsumption bridges','current proof registry availability','substantial full-scope mechanism, not finite checks or wording corrections'],'proposal_count':0},indent=2)+'\n')
p=O/'verify.py';s=p.read_text();s=s.replace("payload(O,m,a.negative_test)","payload(O,m,a.negative_test)\n receipt=load(O/'final-verification-receipt.json')\n assert (receipt['manifest_sha256'],receipt['manifest_size'])==digest(O/'manifest.json'), 'final receipt manifest binding mismatch'")
s=s.replace("for e in chunks+frozen:check(R/e['path'],e)","for e in chunks+frozen:check(R/e['path'],e)\n for name in ['accepted-exclusions.json','historical-dispositions.json']:\n  original=L/'root-mathdb-accepted-exclusions-r304'/name\n  assert original.read_bytes()==(R/'frozen/root-mathdb-accepted-exclusions-r304'/name).read_bytes(), 'r304 direct pair mismatch'")
p.write_text(s)
p=O/'freeze.py';s=p.read_text();s=s.replace("dump(O/'manifest.json',{'files':files,'excluded_exact_paths':['manifest.json','final-verification-receipt.json']})", "dump(O/'manifest.json',{'files':files,'excluded_exact_paths':['manifest.json','final-verification-receipt.json']})\n b=(O/'manifest.json').read_bytes();dump(O/'final-verification-receipt.json',{'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'stage':'pre-final verification binding'})")
p.write_text(s)
print('Strengthened guard/reference and final receipt bindings; r304 direct equality checks.')

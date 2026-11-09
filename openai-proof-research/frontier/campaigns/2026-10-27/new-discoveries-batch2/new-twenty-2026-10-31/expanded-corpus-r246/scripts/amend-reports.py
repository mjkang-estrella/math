import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for f in ['SUMMARY.md','CANDIDATE.md']:
 p=D/f;s=p.read_text();s=s.replace('73 immutable HTTP receipts','88 immutable HTTP receipts').replace('There are 73 HTTP receipts','There are 88 HTTP receipts')
 s+='\n## Final registry audit and sequencing caveat\n\nThe raw Lean Pool candidates/ index files at the recorded HEAD were fetched and scanned for all reserved IDs, source arXiv IDs, authors and distinctive keywords. projects.yml returned 404 and is absent from the complete tree; its receipt is retained, with no retry. Four spaced unauthenticated GitHub repository queries (source ID, local antimagic, Lau/Shiu, Mobius ladder, each with lean) returned no repositories. Full queries, heads, receipts and hits are in outputs/registry-screen.json.\n\n**Procedural failure disclosed:** the live tree/path and web screens preceded numerical work, but the mandatory raw candidate-index scan and GitHub repository API search were completed only during final audit, after the witness and Lean certificate. This does not satisfy the required sequencing. No pre-investment novelty-clearance claim is made; the candidate remains on hold.\n'
 p.write_text(s)
r=json.loads((D/'results.json').read_text())
for v in r.values():v['registry_screen']='outputs/registry-screen.json; raw index and repository API checks completed during final audit, not before investment; explicit sequencing failure.'
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')

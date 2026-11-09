import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
p=D/'CANDIDATE.md';s=p.read_text().replace('This graph is bipartite and the underlying property has a source-proved positive resolution after an appropriate labeling.','This graph is bipartite. The source claimed a positive result for bipartite graphs, but Roy–Saha disproves that general claim; the eight-labeling calculation here concerns only this particular square.');p.write_text(s)
# Retain the distinction between provisional diagnostics and the final prior-art disposition.
for name in ['SUMMARY.md','CANDIDATE.md','results.json','outputs/registry-screen.json','outputs/final-audit.json']:
 assert (D/name).is_file() and (D/name).stat().st_size
m={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'};(D/'outputs/artifact-manifest.json').write_text(json.dumps(m,indent=2)+'\n');print('Final artifacts verified; no Lean endpoint claimed.')

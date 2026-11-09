from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
data=json.loads((L/'checks.json').read_text())['intersections']
s='# All32 exact source intersections\n\nSource parameter q has q>=1 (H5 requires q>=2). Each row solves Cq+D=0; a nonintegral, negative or below-domain root is rejected before generator/multiplicity tests. No persistent intersection occurs.\n\n|H|4a=3b: root|4a=3d: root|\n|---|---|---|\n'
for h in range(1,17):
 rows=[r for r in data if r['H']==h]
 s+='|%d|%s|%s|\n'%(h,rows[0]['root'],rows[1]['root'])
s+='\nAll admissible source-parameter roots and their triples, including failures of a>=12, are retained in checks.json. Every retained flag is false.\n'
(L/'intersections.md').write_text(s)
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('manifest files',len(manifest))

"""Audit-time reader; not used by the final read-only verifier."""
import sys,json,hashlib,re
from pathlib import Path
BASE=Path('frontier/sources/i111_rational_tail_attachment_r2')
old=json.loads(Path('frontier/sources/i107_rational_tail_attachment/reading-manifest.json').read_text())
keys={'G':'Filtered-chromatic','H':'The-height-three','O':'A-rational-obstruction','F':'Finite-generation'}
a,name,*rg=sys.argv[1:]
if a=='BSSW': p=Path('frontier/sources/i105_chromatic_homotopy_discovery/external/bssw-v2.txt')
elif a=='PATH': p=Path(name)
else: p=Path(next(x['local'] for x in old if keys[a] in x['local'])).parent/(name+'.tex')
data=p.read_bytes(); txt=data.decode(); lines=txt.split('\n'); s=int(rg[0]) if rg else 1; end=min(int(rg[1]),len(lines)) if len(rg)>1 else len(lines)
part='\n'.join(lines[s-1:end]); sha=lambda d:hashlib.sha256(d).hexdigest()
rec={'local':str(p),'source_sha256':sha(data),'LF_start':s,'LF_end':end,'LF_fields':len(lines),'splitlines_count':len(txt.splitlines()),'passage_sha256':sha(part.encode()),'labels':re.findall(r'\\label\{([^}]+)\}',part),'line_convention':'LF split; no appended newline; Python splitlines separately counted'}
manifest=BASE/'reading-manifest.json'; rows=json.loads(manifest.read_text()); rows.append(rec);manifest.write_text(json.dumps(rows,indent=2)+'\n')
print(str(p))
for n,l in enumerate(lines[s-1:end],s):print(f'{n}: {l}')

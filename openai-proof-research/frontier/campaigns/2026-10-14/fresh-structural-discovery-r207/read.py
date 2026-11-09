from pathlib import Path
import json,sys,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r207');s=json.loads((R/'private/selection.json').read_text())
i=int(sys.argv[1]);prefix='preprints/'+s['folders'][i-1]+'-September-27-2026/'
for spec in sys.argv[2:]:
 name,*bounds=spec.split(':'); p=prefix+('build/'+name if name in ['main.tex','preamble.tex','references.bib'] else 'build/sections/'+name+'.tex')
 assert p in {e['path'] for e in s['entries'] if e['type']=='blob'}
 b=(R/'private/canonical'/p).read_bytes();start=int(bounds[0]) if bounds else 0;end=int(bounds[1]) if len(bounds)>1 else len(b);part=b[start:end];text=part.decode()
 print('\n=== C'+str(i)+' '+name+' bytes ['+str(start)+','+str(end)+')/'+str(len(b))+' ===\n'+text)
 with (R/'private/read-extents.jsonl').open('a') as f:f.write(json.dumps({'companion':i,'path':p,'start':start,'end':end,'total':len(b),'sha256':hashlib.sha256(b).hexdigest(),'kind':'full raw TeX display; tool truncations require recovery'})+'\n')

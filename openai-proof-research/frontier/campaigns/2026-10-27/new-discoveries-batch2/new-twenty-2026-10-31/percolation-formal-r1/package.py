import sys,zipfile
from pathlib import Path
root=Path(sys.argv[1]).resolve()
items=['guard.sh','replay.sh','scan.py','module-order.txt','source-manifest.sha256','SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md']
if (root/'results.json').exists(): items.append('results.json')
with zipfile.ZipFile(root/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
    for name in items: z.write(root/name,name)
    for dirname in ['src','evidence']:
        for p in sorted((root/dirname).rglob('*')):
            if p.is_file(): z.write(p,str(p.relative_to(root)))

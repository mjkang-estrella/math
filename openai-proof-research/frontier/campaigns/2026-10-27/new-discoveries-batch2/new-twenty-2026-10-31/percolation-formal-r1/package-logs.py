import sys,zipfile
from pathlib import Path
root=Path(sys.argv[1]).resolve()
with zipfile.ZipFile(root/'replay-logs.zip','w',zipfile.ZIP_DEFLATED) as z:
    for directory in [root/'logs',root/'fresh-extracted/logs']:
        for p in sorted(directory.iterdir()):
            if p.is_file(): z.write(p,str(p.relative_to(root)))

from pathlib import Path
import zipfile,sys,hashlib
R=Path(sys.argv[1]);P=R/'packet'
with zipfile.ZipFile(R/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted((P/'src').glob('*.lean')):z.write(p,str(p.relative_to(P)))
 for n in ['module-order.txt','source-manifest.sha256','guard.sh','replay.sh','replay-frontiers.tsv','normalized-trimmed.json','normalized.cnf','certificate-sha256.json','generator-correspondence.json','scan.py']:z.write(P/n,n)
with zipfile.ZipFile(R/'source-only.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 z.extractall(R/'fresh-extracted')
print(hashlib.sha256((R/'source-only.zip').read_bytes()).hexdigest())

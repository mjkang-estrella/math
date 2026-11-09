from pathlib import Path
import zipfile,hashlib
L=Path(__file__).resolve().parent
with zipfile.ZipFile(L/'330264-replay-fit-r2-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted((L/'source').glob('*.lean')):z.writestr(p.name,p.read_bytes())
(L/'packet.sha256').write_text(hashlib.sha256((L/'330264-replay-fit-r2-source.zip').read_bytes()).hexdigest()+'  330264-replay-fit-r2-source.zip\n')

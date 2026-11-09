from research import *
import subprocess
u='https://math.mit.edu/~goemans/18433S07/matroidunion.pdf';b=urllib.request.urlopen(u,timeout=45).read();assert b.startswith(b'%PDF')
p=PRIVATE/'primary/goemans-union.pdf';p.write_bytes(b)
subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
save('union-acquisition.json',dict(url=u,acquired_utc=now(),size=len(b),sha256=sha(b),text_sha256=sha(p.with_suffix('.txt').read_bytes()),role='author lecture proof, not original Edmonds publication'))
save('acquisition-failures.json',[dict(url='https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf',observed_utc=now(),raw_result='urllib HTTP 403; later web open timeout (400)',extent='search metadata only; no primary body read'),dict(target='Edmonds 1970 Submodular functions, matroids, and certain polyhedra',observed_utc=now(),result='bounded search yielded metadata and citations, no acquired original body')])
print(p)

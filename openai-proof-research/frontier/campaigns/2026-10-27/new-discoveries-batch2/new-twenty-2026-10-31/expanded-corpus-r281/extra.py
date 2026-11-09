from pathlib import Path
p=Path(__file__).resolve().parent
exec((p/'fetch.py').read_text().split('rows=json.loads')[0])
exec('def fetch(url):'+(p/'fetch.py').read_text().split('def fetch(url):')[1].split('with concurrent.futures')[0])
import subprocess
urls=['https://github.com/openai/math','https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/master/data/projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool.lean','https://lemon.cs.elte.hu/egres/open/Well-balanced_orientations_of_hypergraphs','https://lemon.cs.elte.hu/egres/open/Acyclic_orientation_with_connectivity_prescriptions','https://lemon.cs.elte.hu/egres/open/Quasi-kernels_and_quasi-sinks','https://pagesperso.g-scop.grenoble-inp.fr/~szigetiz/OCG/Steiner_appeared.pdf','https://arxiv.org/abs/0911.2292']
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:rs=list(ex.map(fetch,urls))
for r in rs:
 f=p/r['file']
 if f.exists() and f.read_bytes()[:4]==b'%PDF':
  t=f.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(f),str(t)],capture_output=True,timeout=20);r['text_file']=str(t.relative_to(p))
(p/'extra-receipts.json').write_text(json.dumps(rs,indent=2)+'\n')
for r in rs:print(json.dumps(r))

from pathlib import Path
import resource,json,hashlib,datetime,urllib.request,concurrent.futures,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
jobs={
'levande.pdf':'https://arxiv.org/pdf/1006.3013',
'chromatic.pdf':'https://personal.lse.ac.uk/boettche/docs/AllBoeGriKohMor_ChromaticThreshold.pdf',
'steinberg.pdf':'https://wrap.warwick.ac.uk/id/eprint/80306/7/WRAP_1173667-ma-110716-steinberg.pdf',
'cyclic-later.pdf':'https://www.combinatorics.org/ojs/index.php/eljc/article/download/v18i1p71/pdf/',
'duplicate-current.html':'https://eulersolve.org/papers/owr-4425-011/',
'annihilation-current.html':'https://www.trureturing.org/research/ayyer-mallick-2010-annihilation-maximal-degeneracy/',
'registry-openai.html':'https://github.com/openai/math',
'registry-pool.yml':'https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml',
'registry-pool.lean':'https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool.lean',
'registry-turing.html':'https://www.trureturing.org/conjectures'}
def get(j):
 n,u=j;r={'url':u,'file':'sources/'+n,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=20) as q:b=q.read(16*1024**2);r.update(status=q.status,final_url=q.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(p/'sources'/n).write_bytes(b)
  if n.endswith('.pdf'):r['text_exit']=subprocess.run(['pdftotext','-layout',str(p/'sources'/n),str(p/'sources'/n.replace('.pdf','.txt'))],capture_output=True,timeout=10).returncode
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:r=list(ex.map(get,jobs.items()))
(p/'followup-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2));print(resource.getrusage(resource.RUSAGE_SELF))

import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json
L=pathlib.Path(__file__).resolve().parent;r=json.loads((L/'reservation.json').read_bytes())
a=[(str(x['mathdb_id'])+'-abs.html',x['source_url']) for x in r['rows']]
a += [('matroid-later.pdf','https://arxiv.org/pdf/1412.8399'),('matroid-later-abs.html','https://arxiv.org/abs/1412.8399'),('cooper-author.pdf','https://people.math.sc.edu/cooper/ASRCH.pdf'),('leanpool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool/projects.yml'),('leanpool-index.lean','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool.lean'),('leanpool-head.html','https://github.com/Vilin97/lean-pool/commits/main/'),('math-readme.md','https://raw.githubusercontent.com/openai/math/main/README.md'),('math-head.html','https://github.com/openai/math/commits/main/')]
(L/'more-sources.json').resolve().write_text(json.dumps(a,indent=2)+'\n')
p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json');print(p.read_text())

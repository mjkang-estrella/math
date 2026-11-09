from research import *
files=[str(p) for p in L.parent.glob('*/*.md') if p.parent!=L and p.name in ['SUMMARY.md','SCOUTING.md','discovery.md']]
r=subprocess.run(['rg','-il','0512299|Shapiro.*conjecture|Mukhin.*Tarasov.*Varchenko',*files],capture_output=True,text=True);log('alias-checks.jsonl',dict(pattern='0512299|Shapiro.*conjecture|Mukhin.*Tarasov.*Varchenko',paths=r.stdout.splitlines(),scope='direct lane reports'))
fetch('math-0512299v2.pdf','https://arxiv.org/pdf/math/0512299v2')
if (L/'primary'/'math-0512299v2.pdf').exists():extract(L/'primary'/'math-0512299v2.pdf')
fetch('last-current.atom','https://export.arxiv.org/api/query?id_list=math/0512299,1002.4384,1107.4875')

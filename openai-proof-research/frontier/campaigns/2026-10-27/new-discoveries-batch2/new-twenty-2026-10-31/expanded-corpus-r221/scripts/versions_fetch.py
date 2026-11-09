import pathlib,json,re,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for a,vs in [('2504.15167',[1,2]),('2212.03100',[1,2]),('2506.12660',[1,2])]:
 for v in vs:get(a+f'v{v}.html',f'https://arxiv.org/html/{a}v{v}')
get('fox-tidor.pdf','https://drops.dagstuhl.de/storage/00lipics/lipics-vol367-socg2026/LIPIcs.SoCG.2026.50/LIPIcs.SoCG.2026.50.pdf')
get('rigidity-followup.html','https://arxiv.org/html/2607.09252')

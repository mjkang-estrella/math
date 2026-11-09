import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib
p=pathlib.Path(__file__).with_name('bodies.py');s=p.read_text();a=s.index('items=');b=s.index('\nout=[]',a)
s=s[:a]+"items=[('horton','https://arxiv.org/pdf/1804.05966'),('staged-journal','https://orlandomarigliano.com/staged-trees-exponential.pdf'),('metric-companion','https://perso.limos.fr/ffoucaud/Publications/Papers/J56_DistanceBased-PathBased-CyclomaticNumber_DM_2025.pdf')]"+s[b:]
s=s.replace('http-bodies.json','http-companions.json')
exec(compile(s,str(p),'exec'))

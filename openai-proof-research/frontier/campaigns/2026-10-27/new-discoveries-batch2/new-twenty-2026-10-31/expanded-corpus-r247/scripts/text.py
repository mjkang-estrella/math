import pathlib,subprocess,resource,os
L=pathlib.Path(__file__).resolve().parents[1];(L/'texts').mkdir(exist_ok=True)
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3)); os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
for p in sorted((L/'http').glob('*pdf*/body')):
 o=L/'texts'/(p.parent.name+'.txt')
 if not o.exists():subprocess.run(['pdftotext','-layout',str(p),str(o)],check=True,timeout=20)

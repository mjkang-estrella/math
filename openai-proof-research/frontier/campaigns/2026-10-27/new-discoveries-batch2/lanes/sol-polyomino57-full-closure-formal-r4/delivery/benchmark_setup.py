from pathlib import Path
import resource,signal,shutil,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent; D=L/'bench';D.mkdir(exist_ok=True);(D/'formal').mkdir(exist_ok=True)
s=(L/'closure/generate.py').read_text().replace('range(6)','range(7)').replace('for size in [6,7]','for size in [8]').replace('for size in [5,6]','for size in [7]')
s=s[:s.index('# exact equality check')]+"(L/'generated-modules.json').write_text(json.dumps(mods,indent=2))\n"
(D/'generate.py').write_text(s)
for n in ['run.py','pins.json']:shutil.copyfile(L/'closure'/n,D/n)

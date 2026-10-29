import urllib.request,hashlib,json,datetime,pathlib,sys
P=pathlib.Path(__file__).resolve().parent

urls={'omega':'https://api.github.com/repos/the-omega-institute/trureturing/commits/dev','omega-main':'https://api.github.com/repos/the-omega-institute/trureturing/commits/main','openai':'https://api.github.com/repos/openai/math/commits/main','aim':'https://api.github.com/repos/MColbrook/AIM/commits/main','count':'https://api.github.com/repos/suvrit/count-ex-machina/commits/main'}
import subprocess
for k,u in urls.items():subprocess.run([sys.executable,str(P/'fetch.py'),k+'-head.json',u],check=True)

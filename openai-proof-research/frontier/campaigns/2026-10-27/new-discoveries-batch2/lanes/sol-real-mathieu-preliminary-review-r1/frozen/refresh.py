import concurrent.futures,subprocess,pathlib
P=pathlib.Path(__file__).resolve().parent
jobs=[('omega','the-omega-institute/trureturing','dev'),('omega-main','the-omega-institute/trureturing','main'),('openai','openai/math','main'),('aim','MColbrook/AIM','main'),('count','suvrit/count-ex-machina','main')]
def go(j):
 k,r,b=j;return subprocess.run(['python3',str(P/'fetch.py'),k+'-head.json','https://api.github.com/repos/'+r+'/commits/'+b],capture_output=True,text=True).stdout
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
 for r in ex.map(go,jobs):print(r,end='')

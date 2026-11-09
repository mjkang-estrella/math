import pathlib,json,subprocess,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; P=L.parents[4]; R=json.loads((L/'records.json').read_text()); out={};start=time.monotonic()
for i,a in R.items():
    terms=[i,a['record']['title'],a['record']['source_url'].split('/abs/')[-1]]
    cmd=['rg','-l','-F','--glob','*.md','--glob','*.json','--glob','*.txt','--glob','!mathdb*','--glob','!routing*','--glob','!coverage*','--glob','!screening*']
    for t in terms:cmd+=['-e',t]
    q=subprocess.run(cmd+[str(P)],capture_output=True,text=True,timeout=6)
    paths=[p for p in q.stdout.splitlines() if str(L) not in p];out[i]={'terms':terms,'paths':paths,'note':'Routing hits and numeric coincidences are not prior mathematical review. Full text scope excludes JSONL corpus and binary PDFs.'}
(L/'historical-search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'elapsed':time.monotonic()-start,'counts':{i:len(a['paths']) for i,a in out.items()}}))

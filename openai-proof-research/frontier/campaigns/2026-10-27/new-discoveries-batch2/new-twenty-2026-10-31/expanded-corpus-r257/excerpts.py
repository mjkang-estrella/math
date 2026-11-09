import pathlib,json,re,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));L=pathlib.Path(__file__).resolve().parent;D=json.loads((L/'literal-records.json').read_text());out={}
for i,x in D.items():
 a=x['record']['source_url'].split('/')[-1];p=L/(a+'.txt');ls=p.read_text().splitlines();parts=[]
 for n,t in enumerate(ls):
  if re.search('Conjecture|conjecture|Question|question',t):parts.append({'line':n+1,'body':'\n'.join(ls[max(0,n-2):min(n+10,len(ls))])})
 out[i]=parts
(L/'primary-question-excerpts.json').write_text(json.dumps(out,indent=2))
for i in ['325401','325475','325485','325566','325567','325700','325868','325979','326295']:
 print(i)
 for p in out[i][-3:]:print(p['line'],p['body'][:850])

import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,sys,time,datetime,urllib.request,base64,re
L=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def write(n,t):
 p=subprocess.run([sys.executable,'-I','-B',str(L/'write_lane.py'),n],input=t,text=True,capture_output=True);assert p.returncode==0,p.stderr
def wj(n,v):write(n,json.dumps(v,ensure_ascii=False,indent=2)+'\n')
def reservation():
 b=(L/'reservation.json').read_bytes();assert H(b)=='6f07546df91c2088144e7a5cd013a397fe1db5dabab2821ec3891aaa4fda0edf'; assert H(b) in (L/'reservation.sha256').read_text();return json.loads(b)
a=sys.argv[1];R=reservation()
if a=='extract':
 ids=set(R['ids']);out={};directory=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 for p in sorted(directory.glob('mathdb-normalized-chunk-*.jsonl')):
  data=p.read_bytes();ch=H(data)
  for lineno,raw in enumerate(data.splitlines(keepends=True),1):
   obj=json.loads(raw);i=obj.get('mathdb_id',obj.get('id'))
   if i in ids:
    assert str(i) not in out
    st=obj.get('statement',obj.get('problem_statement',''));print('ID',i,'KEYS',list(obj),'\nFULL',json.dumps(obj,ensure_ascii=False))
    if not isinstance(st,str):st=json.dumps(st,ensure_ascii=False)
    out[str(i)]={'chunk':str(p),'chunk_sha256':ch,'one_based_line':lineno,'raw_sha256':H(raw),'raw_base64_including_newline':base64.b64encode(raw).decode(),'raw_UTF8_including_newline':raw.decode(),'statement_UTF8_sha256':H(st.encode()),'statement_field':'statement' if 'statement' in obj else 'problem_statement','full_parsed_JSON':obj}
 assert len(out)==20;wj('raw-provenance.json',out);wj('reservation-before.json',{'sha256':H((L/'reservation.json').read_bytes()),'ids':R['ids'],'verified':True})
elif a=='history':
 paths=json.loads((L/'historical-results-allowlist.json').read_text());matches=[];receipts=[];blocked=[]
 terms=[str(x) for x in R['ids']]+['gaussian-prime','projective planes','neighborhood-prime','primitive-set','consumption','strong c-Wilf','modulus metric','Condition (I)']
 for name in paths:
  if any(t in name.lower() for t in ['crown','transitive-bunkbed','tournament']):blocked.append(name);continue
  p=pathlib.Path(name)
  try:b=p.read_bytes()
  except OSError as e:receipts.append({'path':name,'error':str(e)});continue
  txt=b.decode();hits=[t for t in terms if t.lower() in txt.lower()];receipts.append({'path':name,'sha256':H(b),'bytes':len(b),'depth':'full machine text comparison; matched entries emitted for human review'})
  if hits:matches.append({'path':name,'hits':hits,'body':json.loads(txt)})
 wj('history-access.json',{'read':receipts,'blocked_before_open':blocked});wj('history-matches.json',matches)
 for m in matches:
  print(m['path'],m['hits']);print(json.dumps(m['body'],ensure_ascii=False)[:14000])
 print('TOTAL',len(receipts),'matches',len(matches),'blocked',len(blocked))
elif a=='fetch':
 for idx in map(int,sys.argv[2:]):
  row=next(x for x in R['rows'] if x['mathdb_id']==idx);url=row['source_url'].replace('/abs/','/pdf/');rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'method':'GET','id':idx}
  try:
   op=urllib.request.build_opener(urllib.request.ProxyHandler({}));resp=op.open(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceRead/1.0'}),timeout=18);b=resp.read(18*1024**2);rec.update(status=resp.status,final_url=resp.url,bytes=len(b),sha256=H(b));wj(f'source-{idx}-bytes.json',{'base64':base64.b64encode(b).decode()})
   if b.startswith(b'%PDF'):
    p=subprocess.run(['pdftotext','-layout','-','-'],input=b,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=35);rec['conversion_exit']=p.returncode;rec['conversion_stderr']=p.stderr.decode(errors='replace');t=p.stdout.decode();write(f'source-{idx}.txt',t);rec['text_chars']=len(t);print(idx,'ACQUIRED',len(t),'characters',t[:500])
   else:write(f'source-{idx}.txt',b.decode(errors='replace'));print(idx,'nonpdf',len(b))
  except Exception as e:rec['error']=repr(e);print(idx,'ERROR',repr(e))
  wj(f'http-{idx}-{time.time_ns()}.json',rec)
elif a=='read':
 for idx in map(int,sys.argv[2:]):
  p=L/f'source-{idx}.txt'
  if p.exists():print('FILE',p.name,'\n',p.read_text())
elif a=='inspect':
 for n in sys.argv[2:]:print('FILE',n,'\n',(L/n).read_text())

elif a=='statements':
 for k,v in json.loads((L/'raw-provenance.json').read_text()).items():print(k,v['full_parsed_JSON']['statement'])
elif a=='passages':
 idx=sys.argv[2];p=L/f'source-{idx}.txt';p=p if p.exists() else L/f'{idx}.txt';t=p.read_text();lines=t.splitlines();ranges=[]
 for j,line in enumerate(lines):
  if re.search(sys.argv[3],line,re.I):ranges.append((max(0,j-int(sys.argv[4])),min(len(lines),j+int(sys.argv[5])+1)))
 used=set()
 for lo,hi in ranges:
  for j in range(lo,hi):
   if j not in used:print(f'{j+1}: {lines[j]}');used.add(j)
 wj(f'read-{idx}-{time.time_ns()}.json',{'file':f'source-{idx}.txt','sha256':H(t.encode()),'line_count':len(lines),'emitted_one_based_lines':sorted(j+1 for j in used),'depth':'actual emitted passages; other text acquired only'})
elif a=='historicalcompact':
 out=[]
 for m in json.loads((L/'history-matches.json').read_text()):
  b=m['body']; entries=b.items() if isinstance(b,dict) else enumerate(b)
  for k,v in entries:
   text=json.dumps(v,ensure_ascii=False)
   if str(k) in map(str,R['ids']) or any(term.lower() in text.lower() for term in ['gaussian-prime','prime gaussian','modulus metric','primitive-set','consumption ordering','neighborhood-prime','strong c-Wilf','Condition (I)']):out.append({'path':m['path'],'key':k,'entry':v})
 wj('history-relevant.json',out)
 for x in out:print(json.dumps(x,ensure_ascii=False))
elif a=='get':
 name,url=sys.argv[2:4];rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'method':'GET'}
 try:
  resp=urllib.request.build_opener(urllib.request.ProxyHandler({})).open(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceRead/1.0'}),timeout=18);b=resp.read(18*1024**2);rec.update(status=resp.status,final_url=resp.url,bytes=len(b),sha256=H(b));wj(name+'-bytes.json',{'base64':base64.b64encode(b).decode()})
  if b.startswith(b'%PDF'):
   p=subprocess.run(['pdftotext','-layout','-','-'],input=b,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=35);rec['conversion_exit']=p.returncode;t=p.stdout.decode();write(name+'.txt',t);print(t[:1000])
  else:write(name+'.txt',b.decode(errors='replace'));print(b[:2000].decode(errors='replace'))
 except Exception as e:rec['error']=repr(e);print(rec)
 wj('http-'+name+'-'+str(time.time_ns())+'.json',rec)

elif a=='lines':
 p=L/sys.argv[2];t=p.read_text();lines=t.splitlines();lo=int(sys.argv[3]);hi=int(sys.argv[4]);print('\n'.join(f'{j+1}: {lines[j]}' for j in range(lo-1,min(hi,len(lines)))))
 wj('read-'+p.stem+'-'+str(time.time_ns())+'.json',{'file':p.name,'sha256':H(t.encode()),'emitted_range_one_based':[lo,min(hi,len(lines))],'depth':'full emitted text range'})
elif a=='versions':
 for row in R['rows']:
  idx=row['mathdb_id'];url=row['source_url'];rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'method':'GET'}
  try:
   resp=urllib.request.build_opener(urllib.request.ProxyHandler({})).open(url,timeout=10);b=resp.read(2*1024**2);rec.update(status=resp.status,final_url=resp.url,bytes=len(b),sha256=H(b));t=b.decode();write(f'abs-{idx}.html',t);chron=re.findall(r'.{0,120}(?:Submitted|revised|Journal reference|journal_ref|v[1-9]|Withdrawn|withdrawn|doi.org).{0,200}',t);print(idx,'\n'.join(chron));rec['depth']='version/journal/withdrawal metadata lines emitted; not full HTML human reading'
  except Exception as e:rec['error']=repr(e);print(idx,rec['error'])
  wj(f'http-abs-{idx}.json',rec)
elif a=='runfile':
 exec(compile((L/sys.argv[2]).read_text(),str(L/sys.argv[2]),'exec'))

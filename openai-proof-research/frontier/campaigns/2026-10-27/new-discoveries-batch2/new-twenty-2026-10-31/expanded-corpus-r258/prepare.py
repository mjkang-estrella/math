import pathlib,json,re,hashlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
L=pathlib.Path(__file__).resolve().parent;S=L/'sources';C=L.parent
v={};items=[]
for p in S.glob('*.abs.html'):
 a=p.name.split('.abs')[0];s=p.read_text();vv=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int);v[a]={'versions':vv,'doi':re.findall(r'name="citation_doi" content="([^"]+)',s)}
 for z in vv:items.append([a+'v'+z+'.pdf','https://arxiv.org/pdf/'+a+'v'+z])
items += [['neural-journal.pdf','https://msp.org/involve/2021/14-5/involve-v14-n5-p01-s.pdf'],['2606.13960.pdf','https://arxiv.org/pdf/2606.13960'],['2606.11014.pdf','https://arxiv.org/pdf/2606.11014']]
for repo,label,sha in [('openai/math','openai','4eaee87548250b2682affda7d05d947c05554bae'),('the-omega-institute/trureturing','omega','622593005d2dd18d37a84559855df25e18fa2c3c'),('Vilin97/lean-pool','pool','01db1d7049cf9668bda1e9e106875ee1278b43e6')]:
 items += [[label+'-HEAD.html','https://github.com/'+repo+'/commits/HEAD']]
 for path in (['README.md','CONTENTS.md'] if label!='pool' else ['LeanPool.lean']):items.append([label+'-'+path.replace('/','_'),'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+path])
(S/'versions.json').write_text(json.dumps(v,indent=2));(L/'versions-fetch.json').write_text(json.dumps(items,indent=2))
# Historical notes: root adjudications, all reservations and current ledger; bounded corpus token search receipt.
pat=re.compile(r'342517|359209|373197|381168|326956|326852|queen|polynomial.positivity|printed.construction|source.own|357910|331498|330162|330164|330741|331097',re.I)
out={}
for p in C.iterdir():
 if p.is_file() and (p.suffix in ['.md','.json']) and ('ruling' in p.name or 'adjudicat' in p.name or 'acceptance' in p.name or p.name in ['ledger.json','STATUS.md']):
  s=p.read_text(errors='replace')
  if pat.search(s):out[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'content':s}
(L/'historical-notes.json').write_text(json.dumps(out,indent=2))
for a,x in v.items():print(a,x)

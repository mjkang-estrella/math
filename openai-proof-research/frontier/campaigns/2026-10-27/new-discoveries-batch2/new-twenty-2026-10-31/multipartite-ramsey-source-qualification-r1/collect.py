from pathlib import Path
import hashlib,json,resource,datetime,urllib.request,urllib.error,sys,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
O=Path(__file__).resolve().parent
P=O.parent
def dump(n,d): (O/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
if sys.argv[1]=='check':
 d=json.loads((O/'frozen-inputs.json').read_text()); bad=[]
 for p,h in d.items():
  f=Path(p)
  if not f.is_file() or hashlib.sha256(f.read_bytes()).hexdigest()!=h: bad.append(p)
 dump(sys.argv[2],{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(d),'mismatches':bad})
 print(len(d),bad)
elif sys.argv[1]=='fetch':
 name,url=sys.argv[2:4]; r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source qualification'}),timeout=35) as f:
   b=f.read(); r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()); (O/name).write_bytes(b)
 except Exception as e: r.update(status=getattr(e,'code',None),error=str(e))
 dump(name+'.receipt.json',r); print(r)
elif sys.argv[1]=='context':
 for n in ['ledger.json','../ledger.json','../prior-campaign-context.json','expanded-corpus-r258/context.json','expanded-corpus-r258/historical-notes.json','expanded-corpus-r258/registry-review.json','expanded-corpus-r258/registry-fetch.json','expanded-corpus-r258/search-notes.json','expanded-corpus-r258/sources/versions.json']:
  f=(P/n).resolve(); d=json.loads(f.read_text()); print('\nFILE',f,'\n',json.dumps(d,ensure_ascii=False)[:26000])
 print('RESULT',json.dumps(json.loads((P/'expanded-corpus-r258/results.json').read_text())['359209'],indent=2))
 print('RECORD',(P/'expanded-corpus-r258/records/359209.jsonl').read_text())
elif sys.argv[1]=='inspect':
 import re
 from html import unescape
 for n in ['ledger.json','../ledger.json','../prior-campaign-context.json','expanded-corpus-r258/context.json']:
  f=(P/n).resolve(); d=json.loads(f.read_text()); print('CONTEXT',n, 'keys',list(d) if isinstance(d,dict) else type(d))
  if isinstance(d,dict): print({k:v for k,v in d.items() if k not in ['accepted','rejected','held','families'] and len(str(v))<1800})
 s=(O/'dissertation-page.html').read_text(); s=unescape(re.sub('<[^>]+>',' ',s)); s=re.sub(r'\s+',' ',s); i=s.find('Bilangan Ramsey merupakan'); print('THESIS ABSTRACT',s[i:i+11000])
 for folder in ['expanded-corpus-r258','expanded-corpus-r259','nim-extension-source-qualification-r1','polar-bound-source-review-r1']:
  for f in (P/folder).rglob('*.json'):
   if f.name in ['frozen-inputs.json','historical-notes.json','context.json','MANIFEST.sha256.json']: continue
   t=f.read_text()
   if '622593' in t:
    print('LATERHEAD',f,[(m.start(),t[max(0,m.start()-130):m.start()+230]) for m in re.finditer('622593',t)][:4])
 for f in (P/'expanded-corpus-r258/sources').glob('*fresh*'):
  if f.name.endswith('receipt.json'): print('REGISTRY RECEIPT',f.name,f.read_text())
  else:
   lines=f.read_text().splitlines(); hits=[(i+1,l[:350]) for i,l in enumerate(lines) if re.search('multipartite|anuwiksa|359209|K2n|K_2,n|conference|Hadamard',l,re.I)]
   print('REGISTRY MATCH',f.name,hits[:30])
 dump('inspection.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'thesis_page_only_abstract':True,'registry_screen_only':True,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
elif sys.argv[1]=='registry':
 import re
 R=P/'expanded-corpus-r258'
 d=json.loads((R/'registry-review.json').read_text()); print('REGISTRY KEYS',list(d))
 out={}
 for k,v in d.items():
  if len(str(v))<4000: print(k,v)
  else: print(k,'type',type(v).__name__,'length',len(v),'keys',list(v)[:20] if isinstance(v,dict) else '')
 for n in ['omega-HEAD.html','omega-README.md.receipt.json','omega-fresh-README.md.receipt.json']:
  t=(R/'sources'/n).read_text()
  if n.endswith('receipt.json'): out[n]=json.loads(t)
  else:
   out[n]={'commits_first_10':list(dict.fromkeys(re.findall(r'/commit/([0-9a-f]{40})',t)))[:10], 'date_first_10':re.findall(r'datetime="([^"]+)"',t)[:10],'receipt':json.loads((R/'sources'/(n+'.receipt.json')).read_text())}
 print('CHRONOLOGY',json.dumps(out,indent=2));dump('registry-chronology.json',out)
elif sys.argv[1]=='registry-audit':
 import re
 R=P/'expanded-corpus-r258'; d=json.loads((R/'registry-review.json').read_text()); out={}
 for k,v in d.items():
  f=Path(v['cached_index_path']); b=f.read_bytes(); t=b.decode(); z=json.loads(t)
  exact=[t[max(0,m.start()-120):m.end()+120] for m in re.finditer(r'multipartite|Anuwiksa|359209',t,re.I)]
  out[k]={'fresh_head_reported':v['fresh_head'],'cached_index_path':str(f),'index_sha256':hashlib.sha256(b).hexdigest(),'hash_matches_author':hashlib.sha256(b).hexdigest()==v['cached_index_sha256'],'truncated':z.get('truncated') if isinstance(z,dict) else None,'exact_term_hits':exact[:30],'author_limit':v['limitation']}
  print(k,out[k])
 dump('registry-audit.json',out)

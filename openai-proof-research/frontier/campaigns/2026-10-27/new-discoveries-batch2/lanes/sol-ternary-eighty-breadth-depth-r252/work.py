import pathlib,hashlib,json,shutil,sys,subprocess,urllib.request,time
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
P=L.parent/'sol-wide-finite-arithmetic-scout-r250'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
def freeze(paths,name):
 out=[]
 for p in paths:
  a=sha(p); out.append({'path':str(p),'sha256':a,'size':p.stat().st_size}); assert sha(p)==a
 put(name,out)
 return out
if sys.argv[1]=='freeze':
 L.mkdir(exist_ok=True); (L/'administrative').mkdir(exist_ok=True)
 for n in ['ledger.json','prior-campaign-context.json','AGENTS.md']: shutil.copyfile(B/n,L/'administrative'/n)
 freeze(list((L/'administrative').iterdir()),'administrative-snapshot.json')
 paths=[P/n for n in ['SUMMARY.md','SCOUTING.md','discovery.md','checks.py','work.py','diagnostics.json','history-hits.json','history-references.json','source-freeze.json']]+list((P/'source').glob('*.txt'))
 freeze(paths,'immutable-bindings.json')
 print('Frozen',len(paths),'immutable references; no recursive copies.')
elif sys.argv[1]=='read':
 for r in json.loads((L/'immutable-bindings.json').read_text()): assert sha(pathlib.Path(r['path']))==r['sha256']
 for n in sys.argv[2:]:
  p=P/n; print('\nFILE',p,'\n',p.read_text()[:65000])
elif sys.argv[1]=='admin':
 for p in (L/'administrative').glob('*.json'): print(p.name,p.read_text()[:65000])
elif sys.argv[1]=='fetch':
 import urllib.parse
 (L/'retrieved').mkdir(exist_ok=True)
 for name,q in [('followup','all:"square-free reducts"'),('followup2','all:"Grytczuk" AND all:"Stankiewicz"'),('breadth','(cat:math.CO OR cat:math.NT OR cat:math.RA) AND (all:"conjecture" OR all:"open problem") AND submittedDate:[202101010000 TO 202103010000]')]:
  url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':0,'max_results':16})
  try:
   data=urllib.request.urlopen(url,timeout=30).read(1800000); p=L/'retrieved'/(name+'.xml');p.write_bytes(data)
   freeze([p],name+'-freeze.json'); print(name,data.decode()[:80000])
  except Exception as e:
   with (L/'failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':str(e),'time':time.time()})+'\n')
   print(name,str(e))
elif sys.argv[1]=='catalog':
 import xml.etree.ElementTree as ET
 ns={'a':'http://www.w3.org/2005/Atom'}
 for n in ['followup2','breadth']:
  print(n)
  for e in ET.fromstring((L/'retrieved'/(n+'.xml')).read_bytes()).findall('a:entry',ns):
   print(e.find('a:id',ns).text,e.find('a:title',ns).text,[a.text for a in e.findall('a:author/a:name',ns)], e.find('a:summary',ns).text[:650])
elif sys.argv[1]=='papers':
 (L/'source').mkdir(exist_ok=True)
 records=[]
 for ident in sys.argv[2:]:
  url='https://arxiv.org/pdf/'+ident
  try:
   p=L/'retrieved'/(ident+'.pdf');p.write_bytes(urllib.request.urlopen(url,timeout=30).read(10000000))
   q=L/'source'/p.name;shutil.copyfile(p,q);assert sha(p)==sha(q)
   records.append({'url':url,'original':str(p),'copy':str(q),'sha256':sha(q),'time':time.time()});put('pdf-bindings.json',records)
   subprocess.run(['pdftotext','-layout',str(q),str(q.with_suffix('.txt'))],check=True)
   print(ident,'frozen/extracted',q.stat().st_size)
  except Exception as e:
   with (L/'failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':str(e),'time':time.time()})+'\n')
   print(ident,str(e))
elif sys.argv[1]=='bodies':
 import re
 for p in (L/'source').glob('*.txt'):
  s=p.read_text();print('\nFILE',p.name,s[:1800])
  for m in re.finditer(r'(?i)conjecture|open problem|question [0-9]|problem [0-9]',s): print(s[max(0,m.start()-150):m.start()+1800])
elif sys.argv[1]=='excerpt':
 for spec in sys.argv[2:]:
  ident,offset,length=spec.split(':');s=(L/'source'/(ident+'.txt')).read_text();print('\nFILE',ident,'offset',offset,'\n',s[int(offset):int(offset)+int(length)])
elif sys.argv[1]=='history':
 aliases=['2102.11818','Gardam','Agashe','2102.12618','2101.09860','Onsager','Watkins','2102.04185','2102.08052','multiplicative 1-2-3','2101.05229','Elphick','permanent-on-top','2101.03428','2101.09592','log-rank','2101.04716','Aharoni']
 paths=sorted({p for name in ['SUMMARY.md','SCOUTING.md','discovery.md'] for p in L.parent.glob('*/'+name) if p.parent!=L})
 rec=freeze(paths,'history-bindings.json'); hits={a:[] for a in aliases}
 for row in rec:
  p=pathlib.Path(row['path']);s=p.read_text(errors='replace');assert sha(p)==row['sha256']
  for a in aliases:
   if a.lower() in s.lower():hits[a].append(str(p))
 put('history-hits.json',hits);print(json.dumps({a:v for a,v in hits.items() if v},indent=2));print('reports',len(paths))
elif sys.argv[1]=='locate':
 import re
 for ident in sys.argv[2:]:
  s=(L/'source'/(ident+'.txt')).read_text();print('\n',ident,'size',len(s))
  for m in re.finditer(r'(?:Conjecture|Question|Theorem|Proof|Corollary) [A-Z0-9]|Proof\.',s):print(m.start(),s[m.start():m.start()+140].replace('\n',' '))
elif sys.argv[1]=='finalize':
 freeze([P/'source'/'2011.12822v1.pdf',P/'retrieved'/'2011.12822v1.pdf'],'immutable-pdf-bindings.json')
 assert sha(P/'source'/'2011.12822v1.pdf')==sha(P/'retrieved'/'2011.12822v1.pdf')
 freeze(list((L/'source').glob('*.txt')),'derived-text-bindings.json')
 import xml.etree.ElementTree as ET
 ns={'a':'http://www.w3.org/2005/Atom'}
 entries=[]
 for e in ET.fromstring((L/'retrieved'/'breadth.xml').read_bytes()).findall('a:entry',ns):entries.append({'id':e.find('a:id',ns).text,'title':e.find('a:title',ns).text,'authors':[a.text for a in e.findall('a:author/a:name',ns)],'published':e.find('a:published',ns).text,'updated':e.find('a:updated',ns).text})
 put('chronology.json',entries)
 put('progress.json',{'status':'completed bounded research; target unresolved','counts_context':{'additional':9,'total':39,'next':40,'authority':'root alone'},'mechanisms':['all-node terminal masks and exact branch unions','uniform reduction-reflecting code criterion and failed fourth-code extension'],'source81_states':2928,'interval_parameters':1225,'context_parameters':100,'source_code_tests':3279,'fourth_code_universe':1392,'additional_completed_scout_families':8,'overflow_not_counted':1,'new_resolution':False,'credit_recommended':0,'resource_limits':{'address_space_bytes':536870912,'sampled_group_rss_bytes':536870912,'cpu_seconds':210,'wall_seconds':230,'raised':False},'largest_observed_guard_rss_bytes':48742400,'longest_observed_run_wall_seconds':12.224071996985003,'limitations':['RSS sampling does not exclude unsampled transients','no current proof registry head or comprehensive citing-body audit','finite negatives do not decide80'],'time':time.time()})
 put('provenance.json',{'date':'2026-10-30','assigned_lane':str(L),'guard':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'immutable_prior_texts':'immutable-bindings.json','scientific_pdf_references':'immutable-pdf-bindings.json','new_pdf_original_copy_records':'pdf-bindings.json','administrative_snapshots_only':'administrative-snapshot.json','history_report_bindings':'history-bindings.json','derived_texts':'derived-text-bindings.json','live_query_freezes':['followup-freeze.json','followup2-freeze.json','breadth-freeze.json'],'rejected_code_records':'fourth-code-extension.json','forbidden_actions_performed':False,'final_manifest_excludes':['final-manifest.json','final-verification.json']})

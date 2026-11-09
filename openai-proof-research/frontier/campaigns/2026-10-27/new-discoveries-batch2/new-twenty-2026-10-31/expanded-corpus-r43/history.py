import pathlib,json,subprocess,resource,hashlib
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
w=pathlib.Path(__file__).resolve().parent;d=json.loads((w/'provenance.json').read_text());root=w.parents[3];out={}
for i,x in d.items():
 found=[]
 for term,regex in [(i,True),(x['record']['title'],False)]:
  args=['rg','-n','--glob','*.md','--glob','results.json','--glob','dispositions.json','--glob','*ledger*.json','--glob','*exclusion*.json','--glob','!history-search.json']
  args+=['-e',r'\b'+term+r'\b'] if regex else ['-F','-e',term]
  p=subprocess.run(args+[str(root)],capture_output=True,text=True,timeout=20)
  for line in p.stdout.splitlines():
   if '/expanded-corpus-r43/' in line:continue
   found.append(line[:2200])
 out[i]={'terms':[i,x['record']['title']],'matches':found,'scope':'Exact word-boundary ID and literal title across campaign Markdown, results/dispositions/ledgers/exclusions. Not a semantic/full-source global history proof.'}
(w/'history-reviewed.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({i:v['matches'] for i,v in out.items() if v['matches']},indent=2))

import pathlib,json,urllib.request,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
r=pathlib.Path(__file__).parent;t=json.loads(pathlib.Path(json.loads((r/'reused-tree-location.json').read_text())[0]).read_text());rec=[]
roots=['A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026','Conditional-permutations-in-a-revealed-switching-environment-September-26-2026','From-partial-permutation-information-to-Fourier-bounds-September-26-2026','Random-coordinate-frames-and-partial-permutation-laws-September-26-2026']
for j,root in enumerate(roots):
 paths=[x['path'] for x in t['tree'] if x['path'].startswith(root+'/') and x['path'].endswith(('/paper.tex','/main.tex'))]
 for k,path in enumerate(paths):
  url='https://raw.githubusercontent.com/OpenAI/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/'+path;d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':path}
  try:
   with urllib.request.urlopen(url,timeout=18) as f:
    b=f.read();fn=f'openai-body-{j}-{k}.tex';(r/fn).write_bytes(b);d.update(status=f.status,file=fn,sha256=hashlib.sha256(b).hexdigest())
  except Exception as e:d['error']=str(e)
  rec.append(d);print(d,flush=True);(r/'openai-body-receipts.json').write_text(json.dumps(rec,indent=2))

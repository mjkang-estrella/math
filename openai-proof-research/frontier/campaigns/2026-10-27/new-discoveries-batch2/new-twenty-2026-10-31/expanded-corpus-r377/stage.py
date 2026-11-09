import runpy
D=runpy.run_path(__file__.replace('stage.py','research.py'));globals().update({k:v for k,v in D.items() if not k.startswith('__')})
f=json.loads(read(L/'raw-provenance.json'))
for i,v in f.items():
 if i!='338437':print(i,v['parsed']['statement'])
a=json.loads(read(L/'historical-results-allowlist.json'));hits=[];filtered=[]
for x in a:
 if any(w in x.lower() for w in ['crown','bunkbed','tournament','multispin-forest-model-formal-pi-r1']):filtered.append(x);continue
 b=read(x);s=b.decode()
 matched=[i for i in f if i in s]
 if matched:hits.append({'path':x,'ids':matched,'json':json.loads(s)})
write('historical-hits.json',hits);write('historical-filtered.json',filtered)
print('HITS',json.dumps(hits,ensure_ascii=False));print('FILTERED',len(filtered))
p=L.parents[4]/'sources/upstream.json'
# root is resolved from known project path, never recursive discovery.
p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json')
print('UPSTREAM',read(p).decode())
write('stage-receipts.json',receipts)
print('TRUE_EXIT',0,'PID',os.getpid(),'RUSAGE',list(resource.getrusage(resource.RUSAGE_SELF)))

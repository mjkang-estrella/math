import pathlib,json,urllib.request,datetime,hashlib,re,subprocess
b=pathlib.Path(__file__).parent;lanes=b.parent
head=json.loads((b/'sources/omega-current.json').read_text())[0]['sha']
base='6f8ee6614e0faf9dfa2cce46d1eb758dea97c335'
url=f'https://api.github.com/repos/the-omega-institute/trureturing/compare/{base}...{head}'
x={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
try:
 with urllib.request.urlopen(url,timeout=30) as f:data=f.read(12000000);x['status']=f.status
 (b/'sources/omega-compare.json').write_bytes(data);d=json.loads(data);x.update(sha256=hashlib.sha256(data).hexdigest(),base=base,head=head,commits=d.get('total_commits'),files=len(d.get('files',[])),file_limit=300)
except Exception as e:x['error']=str(e)
pattern=r'1905\.01736|Asanjarani|Nazarathy|MMPP|Markov.?modulat|Markovian.?arrival|phase.?type|CoxProcess'
hits={}
for name in ['omega-tree.txt','openai-tree.txt']:
 p=lanes/'root-edge-irregulator-final-freeze-r1'/name
 hits[str(p)]=[line for line in p.read_text().splitlines() if re.search(pattern,line,re.I)]
p=lanes/'sol-fresh-source-discovery-r86/live-compare-inspection.json'
x['r86_receipt']=json.loads(p.read_text())
x['baseline_path_hits']=hits
x['fresh_delta_hits']=[f['filename'] for f in d.get('files',[]) if re.search(pattern,f['filename'],re.I)] if 'd' in locals() else []
x['limit']='Only path/delta coverage. No semantic absence or global priority proof. Wrong branch main July head explicitly rejected.'
(b/'registry-audit.json').write_text(json.dumps(x,indent=2));print(json.dumps(x,indent=2)[:5000])
# All-date duplicate search includes all filename styles; exclude this lane only from output.
p=subprocess.run(['rg','-l','-i',pattern,str(b.parents[4]),'--glob','*.md','--glob','*.txt','--glob','*.json'],capture_output=True,text=True)
paths=[z for z in p.stdout.splitlines() if '/sol-fresh-source-discovery-r90/' not in z]
(b/'mmpp-duplicate-all.txt').write_text('\n'.join(paths)+'\n')

exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('jobs=')[0])
import re
jobs={'peak-repo.json':'https://api.github.com/repos/fengqiaoqu/plactic-peak-counterexample','peak-head.json':'https://api.github.com/repos/fengqiaoqu/plactic-peak-counterexample/commits/HEAD','equivariant.pdf':'https://arxiv.org/pdf/2601.17314','plactic-abs.html':'https://arxiv.org/abs/2410.20460','properties-abs.html':'https://arxiv.org/abs/2512.21401','inverse-abs.html':'https://arxiv.org/abs/2507.01332'}
r=json.loads((L/'http.json').read_text())
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(16000000);x.update(status=f.status,final_url=f.url)
  p=L/'sources'/name;p.write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2))
d=json.loads((L/'sources/omega-delta.json').read_text());pat=r'plactic|Sagan|Wilson|InverseZ|Inverse.Z|Gao|Ruan|Xie|2507.01332|2410.20460'
summary={'omega_head':json.loads((L/'sources/omega-head.json').read_text())['sha'],'openai_head':json.loads((L/'sources/openai-head.json').read_text())['sha'],'total_commits':d.get('total_commits'),'commits_returned':len(d.get('commits',[])),'files_returned':len(d.get('files',[])),'delta_matching_bodies':[f for f in d.get('files',[]) if re.search(pat,f['filename']+' '+f.get('patch',''),re.I)]}
(L/'registry-audit.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2));print(json.dumps(r[-6:],indent=2))

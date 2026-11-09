import pathlib,json,math,hashlib,datetime,urllib.request,subprocess
P=pathlib.Path(__file__).parent;L=P.parent
out={}
a=[0]*1038;a[0]=1
for k in range(1,len(a)):
 if k%9:
  for n in range(k,len(a)):a[n]+=a[n-k]
out['325680']={'executed':'exact coin-change recurrence for parts not divisible by9, n<=1037','tested_k':list(range(33)),'residues_mod12':[a[32*k+13]%12 for k in range(33)],'proof':False}
def s7(n):return sum(math.comb(n,k)**2*math.comb(n+k,k)* (math.comb(2*k,n) if 2*k>=n else 0) for k in range(n+1))
out['326814']={'executed':'integer binomial sum at p=3, m=1..30','residues_mod27':[(s7(3*m)-s7(m))%27 for m in range(1,31)],'proof':False,'missing':'all-m p=3 congruence; no novel full-scope route'}
edges={(i,(i+1)%5) for i in range(5)};edges={tuple(sorted(e)) for e in edges};N=[{j for j in range(5) if tuple(sorted((i,j))) in edges} for i in range(5)]
out['326550']={'executed':'exact C5 adjacency certificate','edges':sorted(edges),'triangle_free':all(not(N[i]&N[j]) for i,j in edges),'every_nonedge_has_common_neighbor':all(bool(N[i]&N[j]) for i in range(5) for j in range(i+1,5) if (i,j) not in edges),'degree_sequence':[len(n) for n in N],'balanced_K2_3_degree_sequence':[2,2,2,3,3],'eligibility':'wording correction only; source uses global cycle maximum'}
(P/'bounded-calculations.json').write_text(json.dumps(out,indent=2)+'\n')
# Successor version: only one fresh lawful request, no parked route.
url='https://arxiv.org/pdf/1306.0136v2';prov=json.loads((P/'source-provenance.json').read_text());e={'id':325680,'url':url,'version':'1306.0136v2','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=30) as r:b=r.read(8000000);e['final_url']=r.url
 assert b.startswith(b'%PDF');p=P/'325680-v2.pdf';p.write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));prov.append(e);(P/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
 subprocess.run(['pdftotext','-layout',str(p),str(P/'325680-v2.txt')],check=True)
 t=(P/'325680-v2.txt').read_bytes();e['derivative']={'path':'325680-v2.txt','sha256':hashlib.sha256(t).hexdigest(),'size':len(t)}
except Exception as ex:e['failure']=str(ex);prov.append(e) if e not in prov else None
(P/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps(out));print(json.dumps(e))
# Bounded administrative exclusions: no unrelated scientific records printed.
ids={x['record']['mathdb_id'] for x in json.loads((P/'literal-records.json').read_text())}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 d=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());print(name,'top keys',list(d),'assignment-ID text matches',[i for i in sorted(ids) if str(i) in json.dumps(d)])
print('ledger accepted titles',[(e['number'],e['title']) for e in json.loads((L.parent/'ledger.json').read_text())['accepted']])

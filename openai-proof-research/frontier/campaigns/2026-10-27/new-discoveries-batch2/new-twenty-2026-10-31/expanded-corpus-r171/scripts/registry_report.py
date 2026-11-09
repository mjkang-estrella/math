import pathlib,json,hashlib,re,datetime
D=pathlib.Path(__file__).resolve().parents[1];E=json.loads((D/'extracted.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
keys={'324110':['1209.2404','maximal avoidance','Bona','Bóna'],'343643':['1908.10212','wild auxiliary','Kurkofka'],'361200':['2312.11287','Braun','Bruegge'],'374171':['2604.13221','higher-derivative','Dong','Ning'],'374191':['2604.13850','wheel-clique','wheel clique'],'374252':['2604.16759','Treblecross','Liang','Muxi'],'374477':['2604.27452','Nash-Williams','Posa'],'374977':['2605.27233','Korsky','sums of roots'],'375232':['2606.11494','Anholcer','Bartkowiak','Bosek','Grytczuk','matroid EF1'],'375615':['2606.27961','Barcau','Pasol','Turcas','transversal difference'],'375690':['2606.31702','Gravier','claw-free perfect'],'375696':['2606.31702','Borowiecki','Cartesian product list'],'398465':['Adem-Ge-Pan','Lyndon-Hochschild','Petrosyan'],'400439':['spectral halo','Newton-polygon','Diao','Yao']}
for i in ['374661','374664','374852','374855','374857','374858']:keys[i]=['2605.10512','2605.21718','Ballantine','Feigon','Maurischat','PartitionPolynomial','subsum']
pool=[p for p in (D/'sources').glob('pool-*') if not p.name.endswith(('-tree.json','-head.json'))]
trees=[D/'sources'/x for x in ['omega-D5-tree.json','omega-Problems-tree.json','openai-preprints-tree.json']]
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':{k:json.loads((D/f'sources/{k}-head.json').read_text())['sha'] for k in ['pool','omega','openai']},'scopes':[{ 'file':str(p.relative_to(D)),'sha256':sha(p),'truncated':json.loads(p.read_text()).get('truncated'),'paths':len(json.loads(p.read_text())['tree'])} for p in trees], 'pool_files':[{'file':str(p.relative_to(D)),'sha256':sha(p)} for p in pool],'github_searches':[],'by_id':{},'limit':'Path/metadata screen, not proof-body or theorem-subsumption clearance. Eight repository queries spaced eight seconds; no code-search claim. Only the unrelated Braun-Bruegge finite facet-sum public proof body was read; it does not settle the arbitrary-graph bounds.'}
for rec in json.loads((D/'outputs/fetch-search.json').read_text()):
 p=D/'sources'/('github-search-'+str(len(out['github_searches']))+'.json');o=json.loads(p.read_text()) if p.exists() else {}
 out['github_searches'].append({**rec,'query':__import__('urllib.parse',fromlist=['parse_qs']).parse_qs(__import__('urllib.parse',fromlist=['urlparse']).urlparse(rec['url']).query).get('q'),'total_count':o.get('total_count'),'repos':[x['full_name'] for x in o.get('items',[])]})
for i,o in E.items():
 terms=[i]+keys[i];hits=[]
 for p in pool:
  for n,line in enumerate(p.read_text().splitlines(),1):
   matched=[t for t in terms if t.lower() in line.lower()]
   if matched:hits.append({'file':str(p.relative_to(D)),'line':n,'terms':matched,'excerpt':line[:400]})
 paths=[]
 for p in trees:
  for x in json.loads(p.read_text())['tree']:
   if any(t.lower() in x['path'].lower() for t in terms):paths.append({'scope':p.name,'path':x['path']})
 out['by_id'][i]={'terms':terms,'pool_hits':hits,'path_hits':paths,'conclusion':'Published partition proof positively identified' if i in ['374661','374664','374852','374855','374857','374858'] else 'No target proof identified in bounded metadata/path screen; generic keyword hits are not proof readings'}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print('registry report: 20 IDs,',len(out['github_searches']),'repository searches')

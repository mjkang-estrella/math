import pathlib,json,hashlib,datetime,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'extracted.json').read_text());receipts=[json.loads(l) for l in (D/'outputs/http.jsonl').read_text().splitlines()];terms={
'332342':['Kitaev','Mütze','universal partial','1601.06456'], '332965':['Brasco','De Philippis','Faber-Krahn'], '333201':['Bang-Jensen','Bessy','antistrong'],'333364':['Diaco','counterfeit','augmented weighing'],'333477':['Soberón','Soberón','Bárány','Larman','colored Tverberg'],'333510':['Naslund','Sawin','sunflower'],'333533':['Ziegler','Drewnowski','stable Kneser'],'333709':['Gerbner','Keszegh','projective plane','line percolation'],'333827':['Merker','Postle','bounded diameter arboricity'],'333862':['Kaiser','Lukot','Rollov','zero-sum flow'],'334104':['Kim','Park','dynamic coloring'],'334132':['Dimca','Sticlaru','plane curve','spectral sequence'],'334219':['Goddard','Henning','triangulation','total dominating'],'334705':['Henning','Yeo','free vertex','4-uniform'],'337293':['Golowich','Kim','set-sequential','odd tree'],'337410':['Gonçalves','Goncalves','Monte Carmelo','Nakaoka','multipartite Ramsey'],'337437':['Chruściel','Delay','Klinger','scalar master'],'337517':['Nikiforov','Rojo','pendent path'],'337830':['Gastineau','Togni','packing edge'],'381332':['Heuer','Sheehan','uniquely Hamiltonian']}
reg={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Bounded metadata/path/keyword screen, not worldwide novelty clearance or all-proof-body audit','repositories':{},'by_id':{},'github_queries':[],'limitations':['GitHub repository search does not search all Lean file contents or private/deleted repositories.','No target public Lean proof identified in screened metadata; no universal absence claim.','The dynamic-coloring GitHub arXiv query was made after its bounded diagnostic sweep; no candidate was advanced.']}
for repo in ['Vilin97-lean-pool','the-omega-institute-trureturing','openai-math']:
 h=json.loads((D/'sources'/(repo+'-head.json')).read_text());reg['repositories'][repo]={'head':h['sha'],'head_endpoint':'/commits/HEAD','commit_date':h['commit']['committer']['date']}
for f in (D/'sources').glob('github-*.json'):
 o=json.loads(f.read_text());rec=next((x for x in receipts if x.get('file')==str(f)),None)
 if rec is None:continue
 reg['github_queries'].append({'file':str(f),'url':rec['url'],'query':urllib.parse.parse_qs(urllib.parse.urlparse(rec['url']).query).get('q'),'utc':rec['utc'],'status':rec.get('status'),'sha256':rec.get('sha256'),'total_count':o.get('total_count'),'hits':[{'full_name':x['full_name'],'description':x.get('description'),'url':x['html_url']} for x in o.get('items',[])]})
pool=list((D/'sources').glob('pool-*'))
for i,row in rows.items():
 ts=[i,row['source_url'].split('/')[-1]]+terms[i];hits=[]
 for p in pool:
  for n,l in enumerate(p.read_text().splitlines(),1):
   matches=[t for t in ts if t.casefold() in l.casefold()]
   if matches:hits.append({'file':p.name,'line':n,'matched_terms':matches,'text':l[:700]})
 reg['by_id'][i]={'terms':ts,'lean_pool_hits':hits,'github_query_files':[x['file'] for x in reg['github_queries'] if i in pathlib.Path(x['file']).name],'verdict':'No exact target Lean proof identified by this bounded screen; generic author/keyword hits are not exclusions.'}
reg['failed_requests']=[x for x in receipts if x.get('error')]
reg['access_limit']='GitHub returned403 on the final333709 numeric-ID query; route not retried. Earlier arXiv/title/author queries succeeded. No further GitHub requests made.'
reg['lean_pool_files']=[{'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in pool]
reg['other_path_screen']=json.loads((D/'outputs/registry-path-hits.json').read_text())
reg['other_path_screen_interpretation']='The 15 OpenAI paths are the Nagata plane-curves preprint, not a demonstrated proof of Dimca-Sticlaru stabilization. No exact leading-target path hit.'
(D/'outputs/registry-screen.json').write_text(json.dumps(reg,indent=2,ensure_ascii=False)+'\n')
print('IDs',len(reg['by_id']),'GitHub queries',len(reg['github_queries']),'Lean Pool files',len(pool))

import pathlib,json,re,datetime
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'reservation.json').read_text())['rows'];r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':{},'screens':{},'limitations':['Metadata and path screen only; no non-match proves novelty. GitHub maximum eight queries.']}
extra=['Dall Pfeifle polyhedral','Pasotti Pellegrini Horak','Butler rainbow arithmetic','Gill Gillespie Semeraro hole stabilizer','Taylor Nash-Williams','Guillou Isaksen eta-local','Meszaros Kirillov reduction','Methuku Palvolgyi hypermatrices','Protasov Slobodianiuk','Iarrobino Khatami Zhao','Hong nonseparating','Shao larger sieve','Morotti p-vanishing','Esperet Lemoine Maffray','Bollobas Scott bisection','Herzog Macchia Welker orthogonal','Balko Jelinek Valtr Beer','Beagley Drube tableau inversion','Noja Pelinovsky Shaikhova tadpole','Dvorakova Florian pseudostandard']
for n in ['leanpool','omega','openai']:r['heads'][n]=json.loads((D/f'sources/{n}-head.body').read_text())['sha']
for row,ex in zip(rows,extra):
 i=str(row['mathdb_id']);terms=[i,row['source_url'].split('/')[-1]]+ex.split();hits=[];paths=[]
 for p in (D/'sources').glob('pool-file-*.body'):
  for no,l in enumerate(p.read_text().splitlines(),1):
   if any(re.search(r'(?<!\w)'+re.escape(t)+r'(?!\w)',l,re.I) for t in terms):hits.append({'file':p.name,'line':no,'text':l[:600]})
 for n in ['omega-D5','omega-Problems','openai-preprints']:
  x=json.loads((D/f'sources/{n}.body').read_text());h=[z['path'] for z in x.get('tree',[]) if any(t.lower() in z['path'].lower() for t in terms)];paths.append({'name':n,'truncated':x.get('truncated'),'entries':len(x.get('tree',[])),'hits':h})
 r['screens'][i]={'terms':terms,'pool_hits':hits,'path_hits':paths,'novelty_cleared':False}
 print(i,'pool',len(hits),[(x['name'],x['hits']) for x in paths if x['hits']])
r['github_searches']=[]
for p in sorted((D/'sources').glob('github-search-*.receipt.json')):
 x=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'));y=json.loads(b.read_text()) if b.exists() else {};r['github_searches'].append({'receipt':p.name,'url':x['url'],'status':x.get('status'),'count':y.get('total_count'),'hits':y.get('items',[])})
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))

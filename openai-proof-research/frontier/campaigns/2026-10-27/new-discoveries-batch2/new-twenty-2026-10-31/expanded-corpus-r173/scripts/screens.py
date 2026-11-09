import pathlib,json,re,hashlib,subprocess,datetime
D=pathlib.Path(__file__).resolve().parents[1];xs=json.loads((D/'extracted.json').read_text());out=json.loads((D/'outputs/registry-screen.json').read_text());out['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();out['scope']='Lean Pool projects and all candidate files read as text; GitHub repository metadata searches, not code search; no global novelty clearance.'
terms={}
for i,x in xs.items():terms[i]=[i,x['source_url'].split('/')[-1]]
more={'368969':['Speyer','Panzer','edge.cut'],'369161':['Blanco','Zeilberger','B-Z'],'369162':['Blanco','Zeilberger','B-Z'],'369318':['equitable.matroid'],'369511':['sunflowerable','Karker','Mirabi'],'369595':['redundant.rigidity'],'369645':['chromatic.discrepancy'],'369646':['chromatic.discrepancy'],'369767':['quadratic.Rado'],'370191':['rainbow.tree'],'370475':['Larman'],'370483':['Ranganatha','overpartition'],'370688':['Briggs','Ling','matching.preorder'],'370836':['Frías','Heegaard','lens.space'],'370885':['sandwich.problem'],'370940':['Tokushige'],'371070':['b.chromatic','Cartesian'],'371181':['antagonistic'],'371255':['hyperconnectivity']}
files=[D/'sources/lean-pool-projects.yml']+list((D/'sources').glob('pool-candidates*'));out['pool_screen']={}
for i,ts in terms.items():
 hits=[]
 for p in files:
  for no,line in enumerate(p.read_text().splitlines(),1):
   if any(re.search(re.escape(t) if '.' not in t else t,line,re.I) for t in ts+more.get(i,[])):hits.append({'file':p.name,'line':no,'excerpt':line[:500]})
 out['pool_screen'][i]={'terms':ts+more.get(i,[]),'hits':hits}
out['github_queries']=[json.loads(x) for x in (D/'outputs/http.jsonl').read_text().splitlines() if '/search/repositories?' in x]
for q in out['github_queries']:
 p=D/q['file'];q['total_count']=json.loads(p.read_text()).get('total_count') if p.exists() else None
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2,ensure_ascii=False));print('pool hits by ID', {k:len(v['hits']) for k,v in out['pool_screen'].items()})
# Build safe bounded historical evidence excluding giant numerical JSON lines.
lines=(D/'history-matches.txt').read_text().splitlines();outlines=[l for l in lines if len(l)<3000 and not re.search(r'sha256|raw_sha|"note"',l)]
(D/'outputs/history-relevant.txt').write_text('\n'.join(outlines)+'\n')
print('\n'.join(outlines[:5]))

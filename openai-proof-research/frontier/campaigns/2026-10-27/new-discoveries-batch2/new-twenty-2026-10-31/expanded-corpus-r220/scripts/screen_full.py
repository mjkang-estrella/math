import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1];P=L.parent
rows=json.loads((L/'reservation.json').read_text())['rows'];words={366512:['Kainen','Guy','skewness'],366515:['Leonida','third eigenvalue'],366563:['Pilipczuk','linear cliquewidth'],366634:['wreath'],366697:['Thornburgh','k-cover'],366751:['Wilhelmi','modular cut'],366794:['Gottlieb','Muršič','impartial chess','generalized staircase'],366827:['pentanomial'],366899:['Kruft','terminal set'],366962:['Tanggara','code-switching'],366989:['Walsh','Bose','basis hypergraph'],367074:['Bensmail','local irregular'],367093:['Häggkvist','avoidable'],367097:['Taranenko','polystochastic'],367142:['longest cycle'],367150:['Lavrov','double Hall'],367173:['Ryser','permanent'],367191:['Grosof','joint-ancestor'],367313:['Gishboliner','F-forest'],367333:['Sheats','bowtie']};out={}
for r in rows:
 k=r['mathdb_id'];terms=[str(k),r['source_url'].split('/')[-1]]+words[k];hits=[]
 for p in (L/'receipts').glob('pool-file-*.body'):
  for i,line in enumerate(p.read_text().splitlines(),1):
   matched=[t for t in terms if t.lower() in line.lower()]
   if matched:hits.append({'file':p.name,'line':i,'terms':matched,'text':line[:700]})
 out[str(k)]={'queries':terms,'hits':hits,'interpretation':'String leads only; not all hits are same target. No public-proof clearance claimed.'}
(L/'outputs/registry-screen.json').write_text(json.dumps({'heads':{x:json.loads((L/'receipts'/f'{x}-head.body').read_text())['sha'] for x in ['leanpool','omega','openai']},'leanpool_tree_truncated':False,'screen':out,'github_search_receipts':[p.name for p in (L/'receipts').glob('github-search-*.json')],'limitations':['Lean Pool projects and all candidate files screened as text; proof bodies not exhaustively audited.','OpenAI and Omega current heads fetched; their complete current trees not fetched, so no clearance from those registries.','No final candidate survived to novelty review.']},indent=2))
hist={}
paths=(L/'outputs/history-paths.txt').read_text().splitlines()
for r in rows:
 k=str(r['mathdb_id']);matches=[]
 for name in paths:
  p=P/name
  if L in p.resolve().parents:continue
  for i,line in enumerate(p.read_text(errors='replace').splitlines(),1):
   if re.search(r'(?<!\d)'+k+r'(?!\d)',line):matches.append({'path':str(p),'line':i,'text':line[:800]})
 hist[k]=matches
(L/'outputs/history-screen.json').write_text(json.dumps(hist,indent=2));print({k:len(v) for k,v in hist.items()});print('registry hits',{k:len(v['hits']) for k,v in out.items()})

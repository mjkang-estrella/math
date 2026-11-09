import pathlib,json,re,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186');out={'heads':{},'searches':json.loads((L/'outputs/github-search.json').read_text()),'screens':{},'limitations':['GitHub repository metadata search is not exhaustive code search.','OpenAI and Omega live HEAD fetched; no live proof-body inspection unless separately cited.','Initial root projects.yml returned 404; tree located actual LeanPool/projects.yml, fetched at same pinned HEAD.']}
for name in ['lean-pool','omega','openai']:
 p=next((L/'sources').glob('*-'+name+'-head.body'));obj=json.loads(p.read_text());out['heads'][name]={'sha':obj['sha'],'body':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
files=list((L/'sources').glob('*-pool-candidate*.body'))+list((L/'sources').glob('*-pool-projects-correct.body'))
for row in json.loads((L/'reservation.json').read_text())['rows']:
 i=str(row['mathdb_id']);a=row['source_url'].rsplit('/',1)[1];authors=row['title'].split("'s")[0] if "'s" in row['title'] else ''
 patterns=[i,a]+[s for s in re.findall(r'\b[A-Z][A-Za-zÀ-ž-]{3,}\b',row.get('title','')) if s not in ['Conjecture','Every','Regularity']]
 # exact source identifiers plus title-derived keywords; authors taken from raw corpus source_name
 raw=json.loads((L/f'sources/{i}.raw.jsonl').read_text());source=raw['source_name'];patterns+=re.findall(r'\b[A-Z][A-Za-zÀ-ž]{3,}\b',source.split('“')[0]);hits=[]
 for p in files:
  for n,line in enumerate(p.read_text().splitlines(),1):
   found=[x for x in patterns if re.search(re.escape(x),line,re.I)]
   if found:hits.append({'file':str(p),'line':n,'terms':found,'text':line[:1000]})
 out['screens'][i]={'patterns':patterns,'hits':hits,'verdict':'bounded text screen only; generic keyword/name matches require scope inspection'}
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print('registry entries',len(out['screens']),'heads',out['heads']['lean-pool']['sha'])

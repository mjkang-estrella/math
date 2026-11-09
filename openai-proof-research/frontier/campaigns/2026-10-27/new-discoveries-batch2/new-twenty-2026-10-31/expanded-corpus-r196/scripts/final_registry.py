import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];p=D/'outputs/registry-screen.json';o=json.loads(p.read_text());r=json.loads((D/'reservation.json').read_text())['rows'];o['exact_id_arxiv_hits']=[]
terms=[str(x['mathdb_id']) for x in r]+[x['source_url'].rsplit('/',1)[1] for x in r];rx=re.compile('|'.join(re.escape(t) for t in terms));keywords=re.compile(r'Gao|Derycke|Le Borgne|Mikulincer|Neuwohner|Golafshan|Whiteland|Dobrovolska|Nakamuta|Bezrukov|Bulatovic|Kuzmanovski|Gurevich|Kravitz|sign.smoothing|wall.crossing|\bCTI\b|\bITC\b|edge.isoperimetric|Kekul|weighted.star',re.I)
for z in o['receipts']:
 if 'raw.githubusercontent.com/Vilin97/lean-pool' in z['url'] and z['status']==200:
  for n,line in enumerate(pathlib.Path(z['body']).read_text().splitlines(),1):
   if rx.search(line):o['exact_id_arxiv_hits'].append({'path':z['body'],'line':n,'text':line})
o['distinctive_pool_hits']=[x for x in o['pool_keyword_hits'] if keywords.search(x['text'])]
for scope in o.get('path_screens',[]):scope['distinctive_hits']=[x for x in scope['hits'] if keywords.search(x)]
o['assessment']='No exact ID/arXiv matches found in pool if exact_id_arxiv_hits is empty. Generic isoperimetry, hypercube pebbling and partition bijections are different targets. No global novelty clearance.'
p.write_text(json.dumps(o,indent=2));print('exact hits',len(o['exact_id_arxiv_hits']));print('distinctive pool hits',len(o['distinctive_pool_hits']));print([(s['repo'],s['scope'],s['count'],len(s['distinctive_hits'])) for s in o.get('path_screens',[])])

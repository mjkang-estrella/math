import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];o={}
for x in json.loads((D/'reservation.json').read_text())['rows']:
 i=str(x['mathdb_id']);s=(D/f'sources/{i}-abs.body').read_text(); aid=x['source_url'].split('/')[-1]
 vs=sorted(set(re.findall(re.escape(aid)+r'v(\d+)',s)),key=int)
 dois=re.findall(r'name="citation_doi" content="([^"]+)',s)
 o[i]={'arxiv':aid,'versions':vs,'doi':dois}
 print(i,vs,dois)
(D/'outputs/versions.json').write_text(json.dumps(o,indent=2))
for k in ['leanpool','omega','openai']:
 p=D/f'sources/{k}-head.body'
 if p.exists():print(k,json.loads(p.read_text()).get('sha'))

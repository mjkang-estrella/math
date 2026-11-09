import sys
sys.argv=[sys.argv[0],'import']
import research as r,json
d=json.loads((r.L/'retrieval/citing-openalex.json').read_text())
for w in d.get('results',[]):print(w['id'],w['display_name'],w.get('doi'),w.get('cited_by_count'))
w=next(w for w in d['results'] if w['display_name'].lower().startswith('multiplier sequences, classes'))
r.fetch('https://api.openalex.org/works?filter=cites:'+w['id'].rsplit('/',1)[1]+'&per-page=30','citer-list.json')

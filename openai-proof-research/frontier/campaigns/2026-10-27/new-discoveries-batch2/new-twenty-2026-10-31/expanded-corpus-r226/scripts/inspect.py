from pathlib import Path
import re,json
L=Path(__file__).resolve().parents[1]
for p in sorted((L/'receipts').glob('*.json')):
 try:r=json.loads(p.read_text());u=r['url']
 except (KeyError,TypeError):continue
 if '/abs/' in u:
  t=(L/'inputs'/(Path(r['body']).stem+'.txt')).read_text(); a=t.find('Submission history');print(u, re.sub(r'\s+',' ',t[a:a+800]).split('Full-text')[0])
 if 'trees/HEAD' in u:
  t=json.loads((L/'receipts'/r['body']).read_text()); matches=[x['path'] for x in t['tree'] if re.search('Spanning|TrailTrap|ForbiddenOut|Edoukou|OddEdge|Lando|Hermitian|Theta|SquaredPath|Supersatur|TriangularEdge|Spider|Horoconvex|Zonotope|Observability|Artin|Semialgebraic',x['path'],re.I)];(L/'inputs/registry-path-matches.json').write_text(json.dumps({'sha':t['sha'],'truncated':t.get('truncated'),'matches':matches},indent=2));print('registry',t['sha'],len(matches));print('\n'.join(matches)[:4500])

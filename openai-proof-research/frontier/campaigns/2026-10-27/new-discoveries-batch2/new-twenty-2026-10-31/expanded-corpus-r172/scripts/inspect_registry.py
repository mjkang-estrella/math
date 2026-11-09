import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
terms=r'miura|pebbl|domination.*cover|cover.*domination|paperboat|paper.boat|kurz|latsch|luroth|regular.*genus|matching.*degree|degree.*power|cactus|young.*even|doublehall|double.hall|pathfree|path.free|contraction|higherbruhat|minimalcayley|centroidsection'
for p in (D/'sources').glob('*-D5.json'):
 o=json.loads(p.read_text());h=[x['path'] for x in o['tree'] if re.search(terms,x['path'],re.I)];(D/'outputs'/('hits-'+p.name)).write_text(json.dumps(h,indent=2));print(p.name,o.get('truncated'),'\n'+'\n'.join(h[:140]))
for p in (D/'sources').glob('pool-*'):
 lines=p.read_text().splitlines();h=[(i+1,l[:700]) for i,l in enumerate(lines) if re.search(terms+'|2607.28616|2506.16561|375830|368018',l,re.I)];
 if h:print(p.name,h[:15])

import pathlib, json, hashlib, datetime, fnmatch, os, re, urllib.request
ROOT=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r141'
PRIVATE=OUT/'packet/private'
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name,obj):
 p=PRIVATE/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(obj,indent=2)+'\n')
def bind(rel):
 p=ROOT/rel;b=p.read_bytes();q=PRIVATE/'context'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 return dict(path=rel,sha256=sha(b),size=len(b),observed_utc=now(),copy=str(q.relative_to(OUT)))
def forbidden(name):
 return any(fnmatch.fnmatch(name.lower(),pat) for pat in ['k369r134-*','*analytic*r134*','t088p133-*','discovery-analytic-r133-parent','*analytic*r135*','*arithmetic*r105*'])
if __name__=='__main__':
 rels=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/NEW-TEN-2026-10-14.md','frontier/campaigns/2026-10-14/expanded-target-2026-10-17/research-brief-2026-10-20.txt']
 rels += ['frontier/campaigns/2026-10-14/discovery-structural-r140-parent/'+p for p in ['contribution-r1-disposition.md','contribution-r1-adoption/adoption.json','contribution-r1-adoption/replay.json']]
 rels += ['frontier/campaigns/2026-10-14/t205q140-contribution-r1/'+p for p in ['packet/public/review.md','packet/public/reading-limits.md','MANIFEST.json','outsideREPORT.md','FINAL.json']]
 records=[bind(r) for r in rels];save('context-bindings.json',records)
 tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); assert len(tree['tree'])==13223 and not tree['truncated'];assert sha((ROOT/'sources/preprints-tree.json').read_bytes())=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 for p,h in {'MANIFEST.json':'de7d844f0f3c3783ebad4586175b7f7f5f53a3626ea18dd5f76bc527af5d2d5c','outsideREPORT.md':'d40cd1baf766137ac78e2dc629edbe5cb5d3e8cad2f4b6fc73e03945055d7aff','FINAL.json':'b713f9096e733a830cde65854c0a419d0a1eb122a77f75063a4b2fdc387cad0f','packet/public/review.md':'66fb8c7e0fa78c1f6604632433b07295b1630f6ed034115c4c9b8a134e356968'}.items():
  assert sha((ROOT/'frontier/campaigns/2026-10-14/t205q140-contribution-r1'/p).read_bytes())==h
 print('Tree and four supplied review anchors authenticated; current named originals bound after initial reads.')
 for e in tree['tree']:
  if any(x in e['path'].lower() for x in ['elementary-positivity-of-chromatic','foulkes','quadratic-stabilization']):print(e['path'],e.get('size'))

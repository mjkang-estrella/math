from pathlib import Path
import fnmatch,hashlib,json,datetime
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r142'
paths=['AGENTS.md','sources/upstream.json',
'frontier/campaigns/2026-10-14/discovery-structural-r141-parent/assessment.md',
*[f'frontier/campaigns/2026-10-14/fresh-structural-discovery-r141/packet/public/{x}.md' for x in ['handoff','prefreeze-derivation','read-and-scope-limits']],
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r28/screen-200.md',
'frontier/iterations/i226-new-algebraic-bridge.md',
'frontier/experiments/i226_new_algebraic_bridge/analytic-attempt.md',
'frontier/campaigns/2026-10-14/relative-ci-r2/original-scope.md',
'frontier/campaigns/2026-10-14/relative-ci-r2/candidate.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r11/original-scope.md',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r11/literature-screen.md']
rows=[]
for name in paths:
 assert not any(fnmatch.fnmatch(c.lower(),p) for c in Path(name).parts for p in ['t373e135-*','*analytic*r135*','*arithmetic*r106*'])
 b=(P/name).read_bytes();target=R/'packet/private/originals'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
 rows.append(dict(path=name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
tree=(P/'sources/preprints-tree.json').read_bytes()
assert hashlib.sha256(tree).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
assert len(json.loads(tree)['tree'])==13223
(R/'packet/private/current-originals.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Late current named-original observation only; not an initial or full-project baseline.',files=rows,tree=dict(path='sources/preprints-tree.json',entries=13223,sha256=hashlib.sha256(tree).hexdigest())),indent=2)+'\n')
print('Copied and bound',len(rows),'named current originals; complete tree authenticated')

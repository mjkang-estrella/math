from pathlib import Path
import hashlib,json,subprocess
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT=PROJECT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r148'
selected={
'AGENTS.md':'Complete applicable instructions; ancestor checks earlier found no other applicable AGENTS.',
'sources/upstream.json':'Complete.',
'frontier/iterations/i13-fresh-discovery.md':'Lines 1-35 and 57-136 fully read; incidental unrelated lines 37-55 in earlier truncated display; not complete report.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r66/constructions.md':'All 77 lines read.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r127/packet/public/other-screens.md':'Relevant lines 22-28 read; display 18-35 included incidental adjacent text; not complete file.',
'frontier/campaigns/2026-10-14/discovery-structural-r147-parent/assessment.md':'Complete direct named exception.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r147/notes/00-provenance-and-isolation.md':'Complete direct named exception.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r147/notes/01-prefreeze-calculations.md':'Complete direct named exception; recovered after truncated first combined display.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r147/notes/02-integrated-reduction-and-gap.md':'Complete direct named exception; recovered after truncated first combined display.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r147/notes/03-evidence-and-reading-limits.md':'Complete direct named exception.'}
rows=[]
for rel,extent in selected.items():
 p=PROJECT/rel
 if p.is_symlink() or not p.is_file():raise RuntimeError(rel)
 data=p.read_bytes();dest=ROOT/'private/history'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 original=hashlib.sha256(data).hexdigest()
 copied=subprocess.check_output(['sha256sum',str(dest)],text=True).split()[0]
 if original!=copied:raise RuntimeError('copy mismatch')
 rows.append({'original_path':rel,'original_bytes':len(data),'original_sha256':original,'copy':str(dest.relative_to(ROOT)),'copy_sha256_independent_sha256sum':copied,'read_extent':extent,'authentication':'Selected current original bytes directly hashed; no historic manifest used; full copied file does not imply full semantic reading.'})
(ROOT/'private/history/selected-original-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
tree=PROJECT/'sources/preprints-tree.json';data=tree.read_bytes();j=json.loads(data)
assert hashlib.sha256(data).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
(ROOT/'private/tree-authentication.json').write_text(json.dumps({'path':'sources/preprints-tree.json','bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'entries':len(j['tree']),'truncated':j['truncated'],'read_extent':'Complete JSON parsed for metadata. Only selected Source161 canonical paths fetched; no other source bodies selected.'},indent=2)+'\n')
print('Authenticated selected originals:',len(rows),'and complete tree metadata.')

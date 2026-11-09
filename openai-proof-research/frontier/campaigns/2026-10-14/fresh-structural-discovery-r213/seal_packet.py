"""One real seal of this round's explicit own selection; refuses an existing packet."""
from pathlib import Path
import hashlib,json,shutil,stat,sys
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r213');P=R/'packet'
assert not P.exists(),'real packet already exists: do not reseal'
assert not (R/'ANCHORS.json').exists(),'detached anchors already exist: do not reseal'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selected=['FINAL.md','DERIVATIONS.md','RELATIVE-DERIVATION.md','STABILITY-REDUCTIONS.md','READING-LIMITS.md','verify_packet.py','guard.py','get_pinned.py','read_exact.py','read_primary.py','navigate_originals.py','navigate_relative.py','navigate_relative_refined.py','primary_get.py','control_packet.py','seal_packet.py']
private=['authenticated.json','tree-selection.json','read-extents.jsonl','source-coverage.json','direct-reading.json','acceptance-selection.txt','source337-navigation.txt','337.md','FillingCoefficient.lean','SharpCAT0Filling.lean','formal-access.json','original-candidates.json','original-navigation-counts.json','original-reading.jsonl','history-section-extents.json','original-selection-r58-section1.txt','original-selection-r58-sections2-8.txt','original-selection-i286-7.txt','original-selection-i286-8.txt','relative-candidates.json','relative-navigation-counts.json','relative-refined-candidates.json','relative-refined-navigation-counts.json','reading-corrections.json','control-results.json']
selected+=['private/'+x for x in private]
for x in json.loads((R/'private/authenticated.json').read_text()):selected.append('private/pinned/'+x['path'])
selected+=['private/primary/'+x for x in ['access.json','access-extra.json','access-AK.json','access-Almgren-recovery.json','read-extents.jsonl','visual-reading.json']]
rows=[json.loads(x) for x in (R/'private/primary/read-extents.jsonl').read_text().splitlines()]
ids=sorted({x['id'] for x in rows}|{'Almgren1986'})
selected+=['private/primary/'+x+'.pdf' for x in ids]
visual=json.loads((R/'private/primary/visual-reading.json').read_text())
for k,x in visual.items():
 for page in x['pdf_pages_1based']:selected.append('private/primary/'+k+'-p'+str(page)+'.png')
# Exact own mathematical excerpts. Raw complete PDFs authenticate the document versions;
# full extraction artifacts and unused downloads are not silently added to the selection.
E=R/'private/selected-primary';E.mkdir(exist_ok=False)
recipe=[]
for i,x in enumerate(rows):
 a=x['start'];z=80303 if x['id']=='Schulze2020' else x['end']
 data=(R/'private/primary'/(x['id']+'.txt')).read_bytes()
 assert sha(R/'private/primary'/(x['id']+'.txt'))==x['extraction_sha256']
 name=f"{i+1:02d}-{x['id']}-{a}-{z}.txt";p=E/name;p.write_bytes(data[a:z])
 selected.append('private/selected-primary/'+name)
 recipe.append({'path':'private/selected-primary/'+name,'id':x['id'],'source_extraction_sha256':x['extraction_sha256'],'start':a,'end':z,'sha256':sha(p),'editorial_overread_excluded':x['id']=='Schulze2020'})
(R/'private/selected-primary-recipe.json').write_text(json.dumps(recipe,indent=2)+'\n')
selected.append('private/selected-primary-recipe.json')
assert len(selected)==len(set(selected))
# Explicit membership and rights statement are themselves part of the selected packet.
selection={'selected_paths':sorted(selected+['SELECTION.json']),'rights':'Private/local source, primary, history and metadata artifacts retain original rights; original research prose/code does not relicense them.','semantics':'Membership authenticates artifacts, not semantic reading of entire raw PDFs. See exact reading ledgers.','unselected':'Acquisition scratch, unused Maggi material, duplicate navigation copies, bytecode caches, copied-control working directory, outside REPORT, anchors and verification receipt are outside this packet.'}
(R/'SELECTION.json').write_text(json.dumps(selection,indent=2)+'\n');selected.append('SELECTION.json')
P.mkdir()
for rel in sorted(selected):
 src=R/rel;assert src.is_file() and not src.is_symlink()
 dst=P/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);dst.chmod(0o444)
items=[]
for rel in sorted(selected):
 p=P/rel;items.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p),'mode':'0444'})
dirs={'.'}
for rel in selected:
 for a in Path(rel).parents:
  dirs.add(a.as_posix())
m={'format':'r213-exact-packet-v1','round':'fresh-structural-discovery-r213','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','seal_count':1,'disposition':'PREFREEZE/no nominee','files':items,'directories':sorted(dirs),'scope':'Exact own selected packet; not an inherited manifest; artifact verification only.'}
(P/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');(P/'MANIFEST.json').chmod(0o444)
for d in sorted(dirs,key=lambda x:len(Path(x).parts),reverse=True):(P/d).chmod(0o555)
report=R/'REPORT.md';report.chmod(0o444)
anchors={'FINAL':{'path':'packet/FINAL.md','sha256':sha(P/'FINAL.md')},'MANIFEST':{'path':'packet/MANIFEST.json','sha256':sha(P/'MANIFEST.json')},'REPORT':{'path':'REPORT.md','sha256':sha(report)},'selection_files':len(items),'selection_bytes':sum(x['bytes'] for x in items),'real_seals':1}
(R/'ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n');(R/'ANCHORS.json').chmod(0o444)
print(json.dumps(anchors,indent=2))

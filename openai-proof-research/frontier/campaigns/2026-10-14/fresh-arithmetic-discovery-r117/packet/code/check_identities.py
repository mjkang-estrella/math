from pathlib import Path
import json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117');H=lambda b:hashlib.sha256(b).hexdigest()
b=Path('sources/preprints-tree.json').read_bytes();assert H(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(b);assert len(tree['tree'])==13223 and not tree.get('truncated');ix={x['path']:x for x in tree['tree']}
source=[]
for a in json.loads((R/'packet/source-identities.json').read_text()):
 b=(R/a['selected_copy']).read_bytes();e=ix[a['canonical_path']];git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 ok=len(b)==a['size']==e['size'] and git==a['gitblob']==e['sha'] and H(b)==a['sha256'];assert ok;source.append({'path':a['canonical_path'],'matches':ok})
incoming=[]
for a in json.loads((R/'packet/incoming-identities.json').read_text()):
 b=Path(a['original']).read_bytes();c=(R/a['selected_copy']).read_bytes();assert H(c)==a['selected_sha256'];incoming.append({'original':a['original'],'selection':a['selection'],'copy_matches':True,'whole_current_matches_capture':H(b)==a['whole_sha256_at_capture'],'current_whole_sha256':H(b),'semantic_reread':False})
out={'tree_sha256':H(Path('sources/preprints-tree.json').read_bytes()),'canonical_sources':source,'incoming':incoming,'warning':'Incoming originals authenticate capture-time bytes only, independently of exact selected-copy manifest membership.'}
(R/'packet/identity-recheck.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'source_matches':len(source),'incoming_copy_matches':len(incoming),'changed_whole_originals':[x['original'] for x in incoming if not x['whole_current_matches_capture']]},indent=2))

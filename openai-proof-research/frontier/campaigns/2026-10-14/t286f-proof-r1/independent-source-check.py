#!/usr/bin/env python3
"""MIT. Read-only independent check of the T286F author packet's canonical source
identities against the repository's own complete preprints tree (not the packet copy).
Usage: independent-source-check.py PACKET_DIR REPO_ROOT
Run it on an authenticated disposable copy of the packet. It writes nothing.
"""
import hashlib,json,sys
from pathlib import Path

TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def sha(b):return hashlib.sha256(b).hexdigest()
def main(packet,repo):
 tree_raw=(repo/'sources/preprints-tree.json').read_bytes()
 if sha(tree_raw)!=TREE_SHA:raise ValueError('repository tree anchor mismatch')
 tree=json.loads(tree_raw)
 if tree['truncated'] is not False or len(tree['tree'])!=13223:raise ValueError('incomplete repository tree')
 ctx=json.loads((packet/'context-identities.json').read_text())
 for c in ctx['contexts']:
  if sha((repo/c['original']).read_bytes())!=c['sha256']:raise ValueError('context original mismatch: '+c['original'])
 fams=ctx['families']
 ent=[e for e in tree['tree'] if any(e['path'].startswith(f+'/') for f in fams)]
 blobs={e['path']:e['sha'] for e in ent if e['type']=='blob' and not e['path'].lower().endswith('.pdf')}
 rec=json.loads((packet/'source-identities.json').read_text())
 if {r['source_path'] for r in rec}!=set(blobs) or len(rec)!=len(blobs):raise ValueError('selected set differs from complete family set')
 for r in rec:
  p=Path(r['path'])
  if p.is_absolute() or '..' in p.parts:raise ValueError('unsafe path')
  b=(packet/p).read_bytes()
  if hashlib.sha1(b'blob %d\0'%len(b)+b).hexdigest()!=blobs[r['source_path']]:raise ValueError('git blob mismatch: '+r['source_path'])
  if sha(b)!=r['sha256'] or len(b)!=r['bytes']:raise ValueError('receipt mismatch: '+r['source_path'])
 print(json.dumps({'status':'PASS_INDEPENDENT_CANONICAL_SOURCES','repository_tree_entries':len(tree['tree']),'family_entries':len(ent),'non_pdf_blobs':len(rec),'contexts':len(ctx['contexts'])}))
if __name__=='__main__':
 try:
  if len(sys.argv)!=3:raise ValueError('usage: independent-source-check.py PACKET_DIR REPO_ROOT')
  main(Path(sys.argv[1]),Path(sys.argv[2]))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)

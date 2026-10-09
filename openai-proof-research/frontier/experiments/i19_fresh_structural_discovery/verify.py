#!/usr/bin/env python3
"""Offline I19 byte/provenance verifier with separate concurrent-input drift reporting."""
import sys
sys.dont_write_bytecode=True
import hashlib,json,runpy
from pathlib import Path
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i19_fresh_structural_discovery'
E=R/'frontier/experiments/i19_fresh_structural_discovery'
REPORT=R/'frontier/iterations/i19-fresh-structural-discovery.md'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];drift=[]
def require(ok,desc):
 if not ok:errors.append(desc)
inputs=json.loads((S/'inputs.json').read_text())
for a in inputs:
 p=R/a['snapshot'];require(p.exists() and digest(p)==a['sha256'],'frozen input: '+a['path'])
 live=R/a['path']
 if not live.exists() or digest(live)!=a['sha256']:drift.append(a['path'])
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text())
require(tree['truncated'] is False,'complete inventory truncated')
blobs={a['path']:a['sha'] for a in tree['tree'] if a['type']=='blob'}
manifest=json.loads((S/'pinned-manifest.json').read_text())
for a in manifest:
 p=S/'pinned'/a['path'];b=p.read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 require(len(b)==a['bytes'] and digest(p)==a['sha256'],'source sha256/bytes: '+a['path'])
 require(git==a['git_blob']==blobs.get(a['path']),'source pinned Git blob: '+a['path'])
 require(a['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+a['path'],'source URL: '+a['path'])
for a in json.loads((S/'theorem-contracts.json').read_text()):
 require(hashlib.sha256(a['text'].encode()).hexdigest()==a['sha256'],'contract self hash')
 t=(S/'pinned'/a['path']).read_text();lines=t.splitlines(keepends=True)
 require(a['text'] in ''.join(lines[a['start_line']-1:a['end_line']]),'contract source slice: '+a['path'])
for a in json.loads((S/'read-locators.json').read_text()):
 lines=(S/'pinned'/a['path']).read_text().splitlines(keepends=True)
 require(hashlib.sha256(''.join(lines[a['start_line']-1:a['end_line']]).encode()).hexdigest()==a['sha256'],'read locator: '+a['path'])
lit=json.loads((S/'literature/manifest.json').read_text())
for a in lit:
 p=R/a['path'];require(p.exists() and digest(p)==a['sha256'] and p.stat().st_size==a['bytes'],'literature bytes: '+a['name'])
for a in json.loads((S/'primary-contracts.json').read_text()):
 t=(R/a['path']).read_text()[a['start_offset']:a['end_offset']]
 require(t==a['text'] and hashlib.sha256(t.encode()).hexdigest()==a['sha256'],'primary contract: '+a['label'])
# Reproduce exact diagnostics without overwriting the retained JSON.
ns=runpy.run_path(str(E/'check.py'),run_name='i19_check_module');fresh=json.loads(json.dumps(ns['main']()))
require(fresh==json.loads((E/'results.json').read_text()),'exact diagnostic reproduction')
seal=json.loads((S/'artifact-seal.json').read_text())
actual={str(p.relative_to(R)) for base in (S,E) for p in base.rglob('*') if p.is_file() and p not in (S/'artifact-seal.json',E/'validation.json') and '__pycache__' not in p.parts}
actual.add(str(REPORT.relative_to(R)))
require(actual==set(seal['files']),'artifact inventory equality')
for path,h in seal['files'].items():
 p=R/path;require(p.exists() and digest(p)==h,'sealed artifact: '+path)
result=dict(status='PASS' if not errors else 'FAIL',errors=errors,counts=dict(frozen_inputs=len(inputs),pinned_sources=len(manifest),source_contracts=len(json.loads((S/'theorem-contracts.json').read_text())),primary_retrievals=len(lit),primary_contracts=len(json.loads((S/'primary-contracts.json').read_text())),sealed_artifacts=len(seal['files'])),diagnostics='reproduced exactly' if fresh==json.loads((E/'results.json').read_text()) else 'mismatch',live_input_drift=drift,drift_policy='Live-input differences are concurrent context drift, not frozen-proof corruption. No live file is changed.',mathematical_status='technical lemma and scoped negative report; no independent proof/significance acceptance')
(E/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));sys.exit(bool(errors))

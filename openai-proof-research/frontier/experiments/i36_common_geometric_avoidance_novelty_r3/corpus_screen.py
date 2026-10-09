"""Read-only complete text inventory screen, independently hash every cached text."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
M=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json'
T=json.loads((ROOT/'sources/preprints-tree.json').read_text()); assert T['truncated'] is False
entries={r['path']:r for r in T['tree']}; rows=json.loads(M.read_text())['files']
patterns={
 'similarity':r'(Erd.{0,30}s similarity|measure universal|measure-universal)',
 'common-geometric':r'(simultaneous|common|all ratios|every ratio|uncountable).{0,100}(geometric|ratio|sequence)|(geometric|ratio).{0,100}(simultaneous|uncountable|common set)',
 'operations':r'(physical.{0,15}window|moving.{0,10}indice|parameter.{0,30}arrangement|local.{0,15}subtree|first.default)',
 'primary-citations':r'(Kolountzakis|Papageorgiou|Chleb.{0,5}k|Burgin|2610\.11449|2210\.09284)',
}
hits={k:[] for k in patterns}; bytes_read=0
for row in rows:
 b=(C/row['path']).read_bytes();bytes_read+=len(b)
 assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']==entries[row['path']]['sha']
 text=re.sub(r'\s+',' ',b.decode('utf-8',errors='replace'))
 for key,pat in patterns.items():
  matches=list(re.finditer(pat,text,re.I))
  if matches: hits[key].append({'path':row['path'],'count':len(matches),'contexts':[text[max(0,m.start()-90):m.end()+90] for m in matches]})
names=sorted({r['path'].split('/')[1] for r in T['tree'] if r['path'].startswith('preprints/')})
print(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','status':'PASS','tree_entries':len(entries),'manuscripts':len(names),'text_files':len(rows),'bytes_read_and_verified':bytes_read,'patterns':patterns,'hits':hits,'inventory':names,'limits':'Complete text search and Git/SHA verification, not semantic reading of every manuscript; relevant G/D full proofs separately read.'},indent=2,sort_keys=True))

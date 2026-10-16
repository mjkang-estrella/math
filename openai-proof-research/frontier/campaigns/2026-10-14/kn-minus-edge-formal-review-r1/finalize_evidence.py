#!/usr/bin/env python3
"""Write review evidence inventories. Copyright 2026 Myeongjin Kang; MIT.
This only inventories the independent review's outputs; it never reseals author inputs.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[3];A=H.parent/'kn-minus-edge-formal-v1'
def rec(p,root):
 b=p.read_bytes();return {'path':str(p.relative_to(root)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
# Check every independent theorem's kernel dependencies, separately from author parser.
q=(H/'logs/review-control-types-axioms.stdout').read_text()
c=json.loads((H/'controls-receipt.json').read_text());reports={}
for n in c['theorems']:
 name='IndependentReview.'+n;m=re.search("'"+name+r"' depends on axioms: \[([^\]]*)\]",q)
 if m:
  ax=set(re.sub(r'\.\{[^}]*\}','',m[1]).replace('\n','').replace(' ','').split(','))
 else:
  assert "'"+name+"' does not depend on any axioms" in q,name;ax=set()
 assert ax <= {'propext','Classical.choice','Quot.sound'},(name,ax)
 reports[name]=sorted(ax)
assert c['status']=='PASS' and len(reports)==16
c['axiom_reports']=reports;(H/'controls-receipt.json').write_text(json.dumps(c,indent=2)+'\n')
# Record the ELF executable and shared Lean compiler implementation, not just version text.
r=json.loads((H/'build-receipt.json').read_text());lean=Path(r['compiler_realpath'])
env=os.environ.copy();env['GIT_OPTIONAL_LOCKS']='0'
p=subprocess.run(['file',str(lean)],capture_output=True,text=True,check=True)
(H/'logs/compiler-file.stdout').write_text(p.stdout);(H/'logs/compiler-file.stderr').write_text(p.stderr)
p=subprocess.run(['ldd',str(lean)],capture_output=True,text=True,check=True)
(H/'logs/compiler-ldd.stdout').write_text(p.stdout);(H/'logs/compiler-ldd.stderr').write_text(p.stderr)
libs=sorted((lean.parent.parent/'lib/lean').glob('*shared*.so'))
(H/'compiler-inventory.json').write_text(json.dumps({'executable':rec(lean,lean.parent.parent),'installation_root':str(lean.parent.parent),'shared_implementation':[rec(p,lean.parent.parent) for p in libs]},indent=2)+'\n')
# Read-only source and object inventory; no author object is used in our LEAN_PATH.
for f in ['KnMinusEdge.lean','Controls.lean','Checks.lean','ControlChecks.lean']:
 assert (H/'build'/f).read_bytes()==(A/f).read_bytes()
assert (H/'build/ReviewControls.lean').read_bytes()==(H/'ReviewControls.lean').read_bytes()
(H/'build-inventory.json').write_text(json.dumps({'files':[rec(p,H) for p in sorted((H/'build').rglob('*')) if p.is_file()],'author_olean_used':False,'dependency_cache':'read-only pinned prebuilt libraries; not rebuilt'},indent=2)+'\n')
# Add exact references read in this review that are not in author's immediate manifest.
m=json.loads((H/'input-manifest.json').read_text());d={x['path']:x for x in m['files']}
extras=[ROOT/'sources/CONTENTS.md',H.parent/'fresh-substantial-discovery-r2/sources/upstream/kn/main.tex',H.parent/'fresh-substantial-discovery-r2/sources/literature/owh-2014-sciencedirect-fetch.txt']
for p in extras:d[str(p.relative_to(ROOT))]=rec(p,ROOT)
m['files']=sorted(d.values(),key=lambda x:x['path']);(H/'input-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
# Freeze the review deliverables, excluding this self-referential manifest.
files=[rec(p,H) for p in sorted(H.rglob('*')) if p.is_file() and p.name!='output-manifest.json' and '__pycache__' not in p.parts]
(H/'output-manifest.json').write_text(json.dumps({'self_excluded':True,'files':files,'rights':'original prose CC BY 4.0; original code MIT; third-party rights retained'},indent=2)+'\n')
print('PASS',len(files),'review outputs inventoried;',len(reports),'independent theorem axiom reports')

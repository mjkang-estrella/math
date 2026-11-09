# Copyright 2026 Myeongjin Kang. MIT.
from pathlib import Path
import json,hashlib,re,difflib,stat
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');C=B/'frontier/campaigns/2026-10-14';O=C/'t088p133-manuscript-review-r1';R=C/'t088p133-manuscript-r2';P=R/'packet/public';R1=C/'t088p133-manuscript-r1/packet/public';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=(R1/'main.tex').read_text();b=(P/'main.tex').read_text();diff=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='r1/main.tex',tofile='r2/main.tex'));assert diff==(P/'qa/main-r1-to-r2.diff').read_text()
counts={}
for env in ['theorem','lemma','proposition','proof']:
 pattern=r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
 aa=re.findall(pattern,a,re.S);bb=re.findall(pattern,b,re.S);assert aa==bb;counts[env]=len(aa)
core=lambda v:v[v.index('\\section{Facet geometry'):v.index('\\section{Positioning,')]
new=re.sub(r'% BEGIN R2 FORMAL USE-SITE NOTE.*?% END R2 FORMAL USE-SITE NOTE\n\n','',b,flags=re.S);assert core(a)==core(new)
unchanged=['witness-tables.tex','support/author-certificate.py','support/independent_certificate.py','support/certificate-witness.json','support/geometry_control.py','support/reproduce.py','build.sh','bootstrap.py']
for f in unchanged:assert (P/f).read_bytes()==(R1/f).read_bytes(),f
origin=json.loads((P/'formal/origin.json').read_text());assert len(origin)==53
for rel,v in origin.items():assert h(P/rel)==h(B/v['original'])==v['sha256'],rel
# Authenticate eight actual pinned source bodies by Git-blob SHA1 and length (no git invocation).
tree=json.loads((B/'sources/preprints-tree.json').read_text());index={v['path']:v for v in tree['tree']};rr=[]
for q in (C/'t088p133-proof-r3/packet/private/upstream/preprints').rglob('*'):
 if q.is_file():
  rel=q.relative_to(C/'t088p133-proof-r3/packet/private/upstream').as_posix();data=q.read_bytes();v=index[rel];blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert blob==v['sha'] and len(data)==v['size'];rr.append({'path':rel,'sha256':h(q),'git_blob':blob,'bytes':len(data),'body_read':'SourceP full; Petty introduction only; other bodies hash-only'})
assert len(rr)==8
pdf=P/'output/pdf/main.pdf';rebuilt=O/'work/extracted/packet/public/output/pdf/main.pdf';assert h(pdf)==h(rebuilt)=='c4e15a10f86623abe2919c36f4863971cea611d705dd3bcbc9684cff260a8647'
results={'actual_diff_matches':True,'qa_script_change':'one-line expansion from main+witness to all supplied non-bibliography TeX, correctly adds formal appendix coverage; not a proof/support mutation','environments_identical':counts,'mathematical_core_identical_except_delimited_formal_note':True,'r1_support_bytes_identical':unchanged,'formal_origin_53_match':True,'pinned_bodies':rr,'pdf_rebuild_identical':True,'pdf_sha256':h(pdf),'pdf_pages_individually_inspected':list(range(1,21)),'resolution_dpi':125,'page20':'reference13 readable, harmless sparse bibliography continuation; optional compacting only'}
(O/'evidence/source-comparison.json').write_text(json.dumps(results,indent=2));print(json.dumps({k:v for k,v in results.items() if k!='pinned_bodies'},indent=2))

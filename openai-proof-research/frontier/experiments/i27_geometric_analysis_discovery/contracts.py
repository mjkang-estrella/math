from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]; S=ROOT/'frontier/sources/i27_geometric_analysis_discovery'; P=S/'pinned';L=S/'literature'
manifest=json.loads((S/'source-manifest.json').read_text());by={x['path']:x for x in manifest['files']}
contracts=[]
for f in sorted(P.rglob('*.tex')):
 txt=f.read_text();path=str(f.relative_to(P));meta=by[path]
 for ma in re.finditer(r'\\begin\{(theorem|proposition|lemma|corollary|assumption)\}(.*?)\\end\{\1\}',txt,re.S):
  contracts.append({'path':path,'url':meta['url'],'git_blob':meta['git_blob'],'file_sha256':meta['sha256'],'start_line':txt[:ma.start()].count('\n')+1,'end_line':txt[:ma.end()].count('\n')+1,'labels':re.findall(r'\\label\{([^}]+)\}',ma.group()),'text':ma.group(),'sha256':hashlib.sha256(ma.group().encode()).hexdigest()})
(S/'source-contracts.json').write_text(json.dumps(contracts,indent=2)+'\n')
# Only actually read source passages, distinct from automatic statement inventory.
read_specs={
'An-L2-Einstein-Gap':{'build/source/main.tex':[(1,99999)]},
'Positively-curved-Einstein':{'build/sections/01-introduction.tex':[(1,115)]},
'Zero-Plane':{'build/sections/01-introduction.tex':[(1,92)],'build/sections/08-classification.tex':[(1,99999)]},
'A-closed-Ricci-flow':{'build/sections/01-introduction.tex':[(1,99999)],'build/sections/06-barriers.tex':[(1,100),(251,320)]},
'Bounded-scalar':{'build/sections/01-introduction.tex':[(1,99999)],'build/sections/02-static-input.tex':[(1,99999)],'build/sections/05-parabolic.tex':[(1,116),(314,384)],'build/sections/07-contradiction.tex':[(270,316)]},
'Path-selection':{'build/sections/01-introduction.tex':[(1,99999)],'build/sections/02-tree.tex':[(1,99999)],'build/sections/07-observables.tex':[(270,355)]},
'Almost-everywhere':{'build/sections/introduction.tex':[(1,99999)],'build/sections/signed-statement.tex':[(1,99999)]},
'A-Codimension-One':{'build/sections/01-introduction.tex':[(1,99999)],'build/sections/02-flat-scales.tex':[(1,99999)],'build/sections/04-fitting-frequency.tex':[(63,159),(630,815)],'build/sections/05-centered-blowup.tex':[(1,99999)],'build/sections/06-linearized-measures.tex':[(1,99999)],'build/sections/06b-density-centers.tex':[(1,99999)],'build/sections/07-dimension-reduction.tex':[(1,99999)]}}
def passage(f,lo,hi):
 lines=f.read_text().splitlines(keepends=True);hi=min(hi,len(lines));text=''.join(lines[lo-1:hi]);return {'path':str(f.relative_to(ROOT)),'start_line':lo,'end_line':hi,'text':text,'sha256':hashlib.sha256(text.encode()).hexdigest()}
passages=[]
for prefix,spec in read_specs.items():
 ds=[x for x in (P/'preprints').iterdir() if x.name.startswith(prefix)];assert len(ds)==1,(prefix,ds)
 for name,ranges in spec.items():
  for lo,hi in ranges:passages.append(passage(ds[0]/name,lo,hi))
(S/'source-read-passages.json').write_text(json.dumps(passages,indent=2)+'\n')
litspec={
'1505.03428v4.txt':[(285,344)],'2102.12840v3.txt':[(50,145)],'2408.11115v2.txt':[(63,185)],'2410.08667v2.txt':[(80,150)],'2606.01511v1.txt':[(255,380)],'2401.00279v1.txt':[(46,83)],'2509.21508v2.txt':[(14,48)],'2609.20647v1.txt':[(20,47)],'2503.00649v1.txt':[(80,110)],'2609.19979v1.txt':[(55,88)]}
lit=[]
for name,rr in litspec.items():
 for lo,hi in rr:lit.append(passage(L/name,lo,hi))
(S/'primary-read-passages.json').write_text(json.dumps(lit,indent=2)+'\n')
versions=[]
for f in sorted(L.glob('*.abs.html')):
 s=f.read_text();a=s.find('Submission history');b=s.find('</div>',a);hist=' '.join(re.sub('<[^>]+>',' ',s[a:b]).split());versions.append({'id':f.name.split('.abs.')[0],'history':hist,'metadata_sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
(S/'primary-versions.json').write_text(json.dumps(versions,indent=2)+'\n')
print(json.dumps({'source_statement_inventory':len(contracts),'source_read_passages':len(passages),'primary_read_passages':len(lit),'primary_version_histories':len(versions)}))

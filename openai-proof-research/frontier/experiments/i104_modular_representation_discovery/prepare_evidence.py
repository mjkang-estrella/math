"""Preparation only: create selective passage metadata. Never called by verify.py."""
import json,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'frontier/sources/i104_modular_representation_discovery'
rows=json.loads((BASE/'selected-inventory.json').read_text())
spec={
 'Donovans-':{'00_introduction.tex':[(1,None)],'07_extensions.tex':[(350,740)],'08_periodicity.tex':[(1,930)]},
 'Integral-':{n:[(1,None)] for n in ['01_introduction.tex','03_rigidity.tex','04_comparison.tex','05_sylow.tex','07_assembly.tex']},
 'The-Blockwise-':{'intro.tex':[(1,None)],'group.tex':[(1,839)],'valuations.tex':[(495,771)],'specialization.tex':[(1,730)],'consequences.tex':[(1,171)]},
 'Fiber-':{n:[(1,None)] for n in ['introduction.tex','projectivity.tex','support.tex','descent.tex','restricted.tex','consequences.tex']},
 'Tensor-Saturation-':{n:[(1,None)] for n in ['01-introduction.tex','05-columns.tex','06-zero-tail-completion.tex']}}
passages=[]
def add(path,ranges,url):
 raw=(ROOT/path).read_bytes(); s=raw.decode('utf-8',errors='replace');lines=s.splitlines()
 for lo,hi in ranges:
  hi=hi or len(lines);assert 1<=lo<=hi<=len(lines)
  selected='\n'.join(lines[lo-1:hi])+'\n'
  passages.append({'local':path,'url':url,'sha256':hashlib.sha256(raw).hexdigest(),'splitlines_count':len(lines),'lf_split_count':len(s.split('\n')),'first':lo,'last':hi,'passage_sha256':hashlib.sha256(selected.encode()).hexdigest(),'first_line':lines[lo-1],'last_line':lines[hi-1]})
for r in rows:
 for family,files in spec.items():
  if r['path'].split('/')[1].startswith(family) and Path(r['path']).name in files:
   add(r['local'],files[Path(r['path']).name],'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['path'])
external={
 'huang-yilmaz-author.pdf.txt':([(1,None)],'https://yilmazdeniz.bilkent.edu.tr/papers/awc-galois-functorial.pdf'),
 'ffz-blockwise-v2.pdf.txt':([(1,170),(1633,2057)],'https://arxiv.org/pdf/2512.15243v2'),
 'huang-category-v3.pdf.txt':([(1,1438)],'https://arxiv.org/pdf/2604.06166v3'),
 'huang-category-v1.pdf.txt':([(86,178),(180,617)],'https://arxiv.org/pdf/2604.06166v1'),
 'kessar-linckelmann-accepted.pdf.txt':([(645,713),(1082,1125),(1182,1331)],'https://openaccess.city.ac.uk/id/eprint/21525/1/characterrationality14Feb18.pdf'),
 'kumar-survey.pdf.txt':([(2500,2690)],'https://www.math.ucdavis.edu/~kapovich/EPR/eigensurvey2.pdf')}
for name,(ranges,url) in external.items():add(str((BASE/'external'/name).relative_to(ROOT)),ranges,url)
(BASE/'passages.json').write_text(json.dumps({'convention':'UTF-8 errors=replace; Python str.splitlines(); 1-based inclusive ranges; passage hash of lines joined by LF plus final LF. lf_split_count uses str.split(chr(10)) including trailing empty item.','passages':passages},ensure_ascii=False,indent=2)+'\n')
(BASE/'extraction-scope.json').write_text(json.dumps({'command':['pdftotext','-layout','INPUT','-'],'scope':'Only the eight external research PDFs; inherited 776 PDF representations are hash-checked, not re-extracted.','pdfs':[str(p.relative_to(ROOT)) for p in sorted((BASE/'external').glob('*.pdf'))]},indent=2)+'\n')
(BASE/'read-failures.json').write_text(json.dumps({'retained_events':[
 {'event':'initial shell read from default cwd','status':'failed path lookup; corrected by explicit workdir'},
 {'event':'arxiv HTML 2512.07369v2','status':'lookup failed; metadata lists v1; author PDF used separately'},
 {'event':'ffz-blockwise-v2.txt lookup','status':'failed; correct stored filename ffz-blockwise-v2.pdf.txt'},
 {'event':'large exploratory terminal outputs','status':'some truncated; bounded range reads used for complete relevant proofs'},
 {'event':'A5 p=2 t=7 identified with q=2','status':'falsified inference; t=17 is correct; both initial and corrected diagnostic records retained'}],
 'not_claimed':'These events were not passing verification runs or counterexamples to pinned results.'},indent=2)+'\n')
print(json.dumps({'passages':len(passages),'pdfs':len(list((BASE/'external').glob('*.pdf')))}))

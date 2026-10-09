from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i36_harmonic_analysis_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((OUT/'pinned-manifest.json').read_text()); passages=[];contracts=[]
for row in rows:
    rel=row['path'];p=ROOT/row['local'];lines=p.read_text().splitlines(keepends=True)
    read=('Erdos-similarity' in rel and ('/sections/' in rel or rel.endswith('references.bib'))) or ('Fourier-convergence' in rel and rel.endswith(('01-introduction.tex','11-fourier.tex')))
    if not read:continue
    text=''.join(lines);passages.append({'path':row['local'],'source_path':rel,'first_line':1,'last_line':len(lines),'sha256':sha(text.encode()),'scope':'entire indicated section/bibliography read; upstream proof accepted, not truth-audited'})
    for m in re.finditer(r'\\begin\{(theorem|proposition|corollary|lemma)\}(?:\[[\s\S]*?\])?[\s\S]*?\\end\{\1\}',text):
        block=m.group(0);labels=re.findall(r'\\label\{([^}]+)\}',block)
        contracts.append({'path':row['local'],'source_path':rel,'labels':labels,'first_line':text[:m.start()].count('\n')+1,'last_line':text[:m.end()].count('\n')+1,'text':block,'sha256':sha(block.encode()),'source_sha256':row['sha256']})
(OUT/'read-passages.json').write_text(json.dumps(passages,indent=2)+'\n')
(OUT/'source-contracts.json').write_text(json.dumps(contracts,indent=2)+'\n')
primary=[('adjacent-v1-pdf.txt',1,521,'Full theorem, proof, countable-family corollary, and stated lower-ratio limitation'),('progressions-v1.txt',35,95,'Question 1 and Theorem 1.1 distinguish all centers from center zero'),('progressions-v1.txt',427,480,'Proposition 3.3 and its parameter-integration proof'),('chlebik-v1.txt',700,810,'Relative-gap criterion and start of finite random-grid construction'),('variation-primary.txt',55,90,'Theorems 1.1-1.2; range p>r-prime and restricted endpoint')]
log=[]
for name,a,b,note in primary:
 p=OUT/'literature'/name;lines=p.read_text().splitlines(keepends=True);b=min(b,len(lines));block=''.join(lines[a-1:b]);log.append({'path':str(p.relative_to(ROOT)),'first_line':a,'last_line':b,'sha256':sha(block.encode()),'purpose':note})
for k in range(3,12):
 p=OUT/f'literature/kolountzakis-pages/page-{k:02}.png'
 log.append({'path':str(p.relative_to(ROOT)),'pdf_page':k,'sha256':sha(p.read_bytes()),'purpose':'Visual reading because PDF text encoding is unusable; statements and relevant random-grid proof'})
(OUT/'literature/read-passages.json').write_text(json.dumps(log,indent=2)+'\n')
versions=[]
for p in sorted((OUT/'literature').glob('*current.html')):
 text=p.read_text();ids=sorted(set(re.findall(r'(?:abs/|arXiv:)([0-9]{4}\.[0-9]{4,5}v[0-9]+)',text)))
 history=re.search(r'<h2>Submission history</h2>([\s\S]*?)(?:</div>|<div)',text)
 versions.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p.read_bytes()),'observed_version_ids':ids,'submission_history_html':history.group(0) if history else None,'withdrawn_notice':'This paper has been withdrawn' in text})
(OUT/'literature/version-record.json').write_text(json.dumps(versions,indent=2)+'\n')
assessment=json.loads((OUT/'literature/retrieval-assessment.json').read_text())
assessment['text_extraction_limits']=[{'name':'kolountzakis-correct-primary','issue':'pdftotext returns garbled glyph mappings; text is not used for mathematical reading. Pages 3-11 rendered at 1500px and visually read.','render_warning':'Syntax Warning: Bad bounding box in Type 3 glyph; inspected PNGs legible.'}]
assessment['not_relied_on']=['kolountzakis-primary (wrong paper)','survey-v1 for current status or proof','twofold-v2 and rajchman-v1 as theorem premises','withdrawn-current as a theorem']
(OUT/'literature/retrieval-assessment.json').write_text(json.dumps(assessment,indent=2)+'\n')
print(json.dumps({'source_passages':len(passages),'exact_contracts':len(contracts),'literature_passages_or_pages':len(log),'version_records':len(versions)}))

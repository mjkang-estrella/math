"""Freeze exact proof passages, source statement contracts and runtime metadata."""
from pathlib import Path
import hashlib,json,re,sys,platform,subprocess
S=Path('frontier/sources/i29_common_base_entropy'); E=Path('frontier/experiments/i29_common_base_entropy')
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,obj):(S/name).write_text(json.dumps(obj,indent=2)+'\n')
manifest=json.loads((S/'pinned-manifest.json').read_text()); passages=[];contracts=[]
def passage(path,a=1,b=None,role='read proof passage'):
 p=Path(path);lines=p.read_text().splitlines(keepends=True);b=min(b or len(lines),len(lines));txt=''.join(lines[a-1:b]);passages.append({'path':str(p),'first_line':a,'last_line':b,'role':role,'text':txt,'sha256':sha(txt.encode())})
for row in manifest:
 p=Path(row['local'])
 if p.suffix!='.tex':continue
 text=p.read_text()
 # Retained statement contracts; selection does not imply reading every retained companion.
 for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(.*?)\\end\{\1\}',text,re.S):
  contracts.append({'path':str(p),'environment':m.group(1),'labels':re.findall(r'\\label\{([^}]+)\}',m.group()),'first_line':text[:m.start()].count('\n')+1,'last_line':text[:m.end()].count('\n')+1,'text':m.group(),'sha256':sha(m.group().encode())})
 if ('Approximate-counting-of-common-bases' in str(p) and p.name=='main.tex') or 'Common-Integer-Polymatroid' in str(p):passage(p,role='complete required-source mathematical body')
 elif 'Entropy-and-Face-Dimension' in str(p) and p.name in ['03-entropy.tex','05-weighted.tex']:passage(p,role='generic entropy and weighted variational proof interface')
 elif 'Cell-Bounded' in str(p) and p.name=='signatures.tex':passage(p,role='two factorial lifts and explicit sufficient-condition warning')
 elif 'Cell-Bounded' in str(p) and p.name=='integer-signatures.tex':passage(p,1,520,role='balanced-summation proof and tree-marginal application')
 elif 'Cell-Bounded' in str(p) and p.name=='transport.tex':passage(p,1,200,role='full-support two-lift transport interface; subsequent proof not used')
 elif 'Exact-Uniform' in str(p) and p.name=='signatures.tex':passage(p,1,160,role='softened weight and laminar signature interface')
 elif 'Exact-Uniform' in str(p) and p.name=='introduction.tex':passage(p,1,125,role='algorithm scope comparator')
for f in ['i25-matching-entropy-improvement-resumed.md','i13-fresh-discovery.md']:
 p=S/'inputs/frontier/iterations'/f
 if f.startswith('i13'):
  lines=p.read_text().splitlines();a=next(i+1 for i,l in enumerate(lines) if l.startswith('## 4'));b=next((i for i,l in enumerate(lines[a:],a) if l.startswith('## 5')),len(lines));passage(p,a,b,role='I13 projected common-base obstruction')
 else:passage(p,role='authorized full R011 fallback')
for f in ['i25-rooted-entropy-proof-r2.md','i25-rooted-entropy-novelty-r3.md']:passage(S/'inputs/frontier/reviews'/f,role='prior independent review')
primary={'aov-v2.txt':[(1030,1590),(1640,1750)],'ao-v1.txt':[(105,165),(480,600)],'gurvits-v11.txt':[(120,230)],'chen-liu-pdf.txt':[(190,350),(674,820)],'schweitzer-2011.14406v2.txt':[(65,100),(265,345)],'blp-2008.05907v3.txt':[(835,940)]}
for f,ranges in primary.items():
 for a,b in ranges:passage(S/'literature'/f,a,b,role='primary theorem/proof comparison; not full-paper read claim')
write('source-contracts.json',contracts);write('read-passages.json',passages)
versions=[]
for p in sorted((S/'literature').glob('*current.html')):
 t=p.read_text();v=sorted(set(re.findall(r'\b\d{4}\.\d{4,5}v\d+\b',t)),key=lambda s:int(s.split('v')[-1]));title=re.search(r'<meta name="citation_title" content="([^"]+)',t)
 versions.append({'path':str(p),'title':title.group(1) if title else None,'versions_in_retained_page':v,'highest_retained_version':v[-1] if v else None,'sha256':sha(p.read_bytes())})
write('current-versions.json',versions)
write('environment.json',{'python':sys.version,'platform':platform.platform(),'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','cwd':str(Path.cwd()),'write_scope':['frontier/iterations/i29-common-base-entropy.md',str(S)+'/',str(E)+'/'],'query_record_note':'Earlier result dumps are retained as returned. search-final.json includes exact query arguments and a fresh response; no reconstruction of omitted early query arguments is claimed.'})
print(json.dumps({'source_statement_contracts':len(contracts),'read_passages':len(passages),'current_version_pages':len(versions)}))

"""One-shot I69 evidence writer. Not called by offline replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,platform
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i69_global_algebra_rounding_budget'
OLD=ROOT/'frontier/sources/i65_linked_symmetric_algebra_rounding'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,d): (S/n).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
passages=[]
def add(path,a,b,scope):
 p=ROOT/path; data=p.read_bytes(); lines=data.splitlines(keepends=True)
 assert 1<=a<=b<=len(lines),(path,a,b,len(lines))
 piece=b''.join(lines[a-1:b])
 passages.append(dict(path=path,first_line=a,last_line=b,file_sha256=sha(data),passage_sha256=sha(piece),text=piece.decode(),read_scope=scope))
for r in json.loads((OLD/'passages.json').read_text()):
 if '/pinned/' in r['path']:add(r['path'],r['first_line'],r['last_line'],'Actual pinned proof operation; applicability audit, not upstream truth audit')
pinbase='frontier/sources/i65_linked_symmetric_algebra_rounding/pinned/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/build/manuscript/'
add(pinbase+'transport.tex',160,245,'Affine normalization and inverse-P bound; actual source operation')
ranges={'fox':[(1,35),(530,795),(760,907),(900,1025),(1156,1330)],'fox-sectional':[(408,447),(674,697)],'kitaev':[(210,368)],'bk':[(65,150),(155,250),(345,490)],'bdhr':[(330,412)],'cpv':[(385,460)],'ppt':[(1,90),(215,400)],'bds':[(419,493)],'auddy':[(890,972),(2218,2290)],'poinsot':[(1185,1228)]}
for name,rr in ranges.items():
 for a,b in rr:add(f'frontier/sources/i69_global_algebra_rounding_budget/primary/{name}-pdf.txt',a,b,'Selected actual primary statement/proof passage; not full-paper certification')
put('passages.json',passages)
inputs=[]
for r in json.loads((S/'inputs.json').read_text()):
 p=ROOT/r['path']; full=(r['path']=='AGENTS.md' or any(x in r['path'] for x in ['/i53-','/i59-','/i61-','/i65-linked','/i55-','/i56-','/i63-','/i64-','/R014-']))
 inputs.append(dict(path=r['path'],sha256=r['sha256'],read_scope='FULL' if full else 'STRUCTURED OR SELECTED STATUS INSPECTION; frozen entire for provenance',lines=len((S/'inputs'/r['path']).read_text().splitlines())))
put('read-contracts.json',dict(inputs=inputs,passages='passages.json',pins='26 immutable pinned files inventoried; only identified passages are claimed read.',primary='Selected passages, not full-paper proof certification. Steiner companion discovery only.',catalogue='Inventory/search evidence does not mean all 749 manuscripts were read.'))
versions=[]
for r in json.loads((S/'primary/manifest.json').read_text()):
 if 'text_path' not in r:continue
 p=ROOT/r['text_path']; t=p.read_text(); v=re.findall(r'arXiv:\s*[^\s\[]+',t[:5000]); old=OLD/'primary'/p.name
 versions.append(dict(name=r['name'],served_markers=v,path=r['text_path'],sha256=sha(p.read_bytes()),same_text_as_i65=old.exists() and old.read_bytes()==p.read_bytes(),first_lines=t.splitlines()[:15]))
put('primary/versions.json',versions)
put('analytic-verdicts.json',{'scope':'Author independent audit of deductions used, not external independent review or evidence-based theorem certification','original_pass_without_repairs':['I65 linked superoperator identity on all matrices','I65 simplicial normalization, sign, ordered E, exact unrenormalized chain','I65 partial-transpose composition and limited obstruction scope','I65 arbitrary-B sign rounding and reverse projection inequality','I65 supplied near-square dilation with singular polar completion'],'original_gaps_retained':['AR_K and exact B=I','General linked dephasing entrance','Finding near-square factors','Uniform adaptive mixed-mass budget'],'original_repairs_made':[],'new_proved_partials':['Complete-chain terminal and small-c accounts','Exact combined residual change','Logarithmic greedy budget for supplied scaled simplicial direct sums','Global supplied-dilation bound for multiscale sums and tensor products','Walsh pair-flat and one-partition block obstruction','Explicit scalar unitalization residual and normalization'],'new_failed_methods':['Monotonicity of R and Phi_dimension(R) on natural cap-one intermediate class','Strict-improvement pair-coordinate algorithm','One-shot bounded coordinate-block reconstruction'],'acceptance':'No nomination; eight findings unchanged; parent independent proof/significance reviews not commissioned by child.'})
put('local-read-failures.json',[{'command':'sed -n 160,245p frontier/sources/i65_linked_symmetric_algebra_rounding/pinned/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/sections/transport.tex','returncode':2,'stderr':'sed: can\'t read frontier/sources/i65_linked_symmetric_algebra_rounding/pinned/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/sections/transport.tex: No such file or directory\n','resolution':'Correct existing path build/manuscript/transport.tex read successfully, lines 160-245; no source edited.'}])
p=subprocess.run(['pdftotext','-v'],capture_output=True,text=True)
put('environment.json',dict(python=sys.version,platform=platform.platform(),pdftotext_stdout=p.stdout,pdftotext_stderr=p.stderr,pdftotext_returncode=p.returncode,verification_scope='Offline immutable bytes and finite arithmetic only. No universal mathematical claim follows from PASS.'))
print(json.dumps({'passages':len(passages),'contracts':len(inputs),'pdf_versions':len(versions)}))

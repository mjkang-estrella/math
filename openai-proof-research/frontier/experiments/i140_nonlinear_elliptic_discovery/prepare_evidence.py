"""Preparation only; no corpus copying or ancestor verifier execution."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3];S='frontier/sources/i140_nonlinear_elliptic_discovery';OLD='frontier/sources/i137_crystalline_coherence'
def obj(p):return json.loads((R/p).read_text())
def put(n,d):(R/S/n).write_text(json.dumps(d,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def rec(p):
 b=(R/p).read_bytes();return {'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
rs=[json.loads(x) for x in (R/S/'reads.jsonl').read_text().splitlines()]
reads=[]
for i,d in enumerate(rs):
 if i==0:continue # initial I137 1-253 display truncated; complete replacements recorded
 if i in (6,7):
  # The fully visible portions of the combined truncated display; missing portions were reread before gate.
  d=dict(d);d['start'],d['end']=(335,567) if i==6 else (23,92)
  ls=(R/d['path']).read_text().splitlines();d['ending']=ls[d['end']-1];d['passage_sha256']=hashlib.sha256('\n'.join(ls[d['start']-1:d['end']]).encode()).hexdigest();d['display_note']='complete visible part of truncated combined display; complementary complete reread separately recorded'
 if '/corpus/preprints/' in d['path']:d['pinned_url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/'+d['path'].split('/corpus/preprints/',1)[1]
 reads.append(d)
put('read-manifest.json',{'passages':reads,'convention':'UTF-8 splitlines including PDF form feeds; LF joined without appended LF; complete visible passages only'})
ctx=obj(S+'/context-manifest.json')
# Preserve original gate record unchanged. Verify all mandatory decoded line positions are covered by completed displays.
for d in ctx:
 covered=set()
 for rr in reads:
  if rr['path']==d['decoded']:covered.update(range(rr['start'],rr['end']+1))
 assert covered==set(range(1,d['lines']+1)),d['path']
put('original-audit-verdicts.json',{'A137':{k:'PASS without repairs' for k in ['Delta L systole quantifiers','deletion saturation markings','actual normals and supports','triangular dual and degree six','rotational and translational monodromy','disk buffer contractibility','triangle crossings and adjacent polar rotations','uniform gradient and injection','image disks and original site bijection','original Delaunay compatibility','physical disk FJM','bounded overlap averaging','affine nodal bound','zero deficit','aspect ratio limits','slow wave and two grain compatibility']},'R1_R7':{k:'PASS without repairs' for k in ['R1 normalizations cancellation convergence','R2 arbitrary directed subset and self images','R3 kernels gamma E1 tails','R4 all directed short pairs deletion adaptive cutoff entrances','compact mixture consequence','R5 full Fourier subgroup identity','R6 ordered movement and scaling','R7 smooth remainder uniform errors and exponents']},'unresolved_not_asserted':['global labels across defects','interface energy','arbitrary near minimizer defect preserving screening','weighted boundary origin quantitative a priori target'],'original_I134':'original-scoped PASS retained including displayed common constant','I125_literal':'FAIL: ValueError: canonical inventory; unchanged original seal','I125_ordering_only':'distinct PASS receipt; not rerun','I122_general_Lambda':'FAIL retained','accepted_count':8,'nomination':None})
flat={d['path']:d for d in obj(OLD+'/immutable-flat.json')['files']}
for d in obj(OLD+'/seal.json')['files']:flat[d['path']]=d
for p in [OLD+'/seal.json','frontier/iterations/iteration137-crystalline-coherence-task.json','frontier/experiments/i137-parent-verification.json','frontier/experiments/i116-parent-verification.json','frontier/experiments/i131_soft_summary_stability/extract_html.py']:
 flat[p]=rec(p)
for d in ctx:flat[d['path']]={k:d[k] for k in ('path','bytes','sha256')}
for d in reads:
 if not d['path'].startswith(S+'/'):flat[d['path']]={k:d[k] for k in ('path','bytes','sha256')}
for d in obj(S+'/snapshots.json'):
 if not d['drift']:flat[d['live']]=rec(d['live'])
for p in ['sources/preprints-tree.json','sources/CONTENTS.md']:flat[p]=rec(p)
for p in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:flat.pop(p,None)
assert not any(re.search(r'/(?:i|iteration)(138|139)',p) for p in flat)
put('immutable-flat.json',{'corpus_map':'frontier/sources/i113_online_optimization_discovery/search-domain.json','files':[flat[p] for p in sorted(flat)],'note':'One flat immutable traversal. Ancestor receipts/diagnostics byte-verified, not executed. No corpus copies.'})
put('inherited-references.json',[flat[p] for p in sorted(flat) if '/experiments/' in p and ('parent-' in p or p.endswith('/diagnostics.json'))])
domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json');wanted={d['path'] for d in reads}
put('selected-inventory.json',[d for d in domain if d['local'] in wanted or d['original_local'] in wanted])
expr={'audit_interfaces':r'holonomy|monodromy|FJM|self.image|regular part|Gamma\(|E1\(', 'elliptic_models':r'infinity.harmonic|p-harmonic|Lane.Emden|H[eé]non|affine.maximal|affine.Bernstein', 'quantifier_gates':r'half.space|boundary|coefficient|origin|subcritical|complete|scaling|pressure'}
found={k:[] for k in expr};scope={}
for d in reads:scope.setdefault(d['path'],set()).update(range(d['start'],d['end']+1))
for p,ns in sorted(scope.items()):
 ls=(R/p).read_text().splitlines()
 for n in sorted(ns):
  for k,x in expr.items():
   for m in re.finditer(x,ls[n-1],re.I):found[k].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
put('focused-lexical.json',{'scope':'union of completed reading ranges only, all path types; not a semantic/full-corpus search claim; zero-based character offsets; Python re.I; every nonoverlapping occurrence per expression','expressions':expr,'occurrences':found,'counts':{k:len(v) for k,v in found.items()}})
put('read-history.json',{'mandatory_gate':'context-reading.json, preserved unchanged; every decoded line covered in read-manifest.json','truncated_attempts':['Initial broad ledger output truncated; scoped ledger passages subsequently read.','Initial I137 decoded 1-253 display truncated; complete replacements 1-89,90-147,148-253.','Combined I134335-588/I1311-92 display truncated at junction; visible I134335-567/I13123-92 retained, complete134568-588/1311-22 rereads before audit.','Broad discovery rg patterns and combined web/discovery/verify output exceeded output budgets; search output was not counted as proof reading.','Broad snapshot keyword display truncated; scoped accepted-count and current iteration passages read.'],'failed_requests':['U appendix wildcard discovery matched no file; actual 08-arithmetic-verification.tex was located and read.','Guessed ANU affine.pdf returned HTTP404; correct 1-Invent00.pdf retrieved.'],'retrieval_records':'retrievals.json; successful content fetched/extracted once; unsuccessful retrieval retained; snippets and unvisited leads not proof','rendered_and_seen':[{'pdf':S+'/external/'+stem+'.pdf','page_one_based':page,'image':S+'/external/'+stem+'-theorem.png','command':['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1500','-png','-singlefile']} for stem,page in [('bungert',4),('pqs',9),('qs',14),('tw-2000',11)]],'overlap_discovery':'rg across iteration Markdown excluding active i138/i139 and owned i140; exact relevant matches I02 and I130; broader noisy expression discarded; actual relevant prior passages are in read-manifest','representation':'PDF discovery rg uses LF lines; recorded completed reads use splitlines including form feeds. HTML uses immutable I131 deterministic extractor, including MathML alttext and final LF.'})
print(json.dumps({'flat_references':len(flat),'passages':len(reads),'lexical_occurrences':sum(map(len,found.values()))}))

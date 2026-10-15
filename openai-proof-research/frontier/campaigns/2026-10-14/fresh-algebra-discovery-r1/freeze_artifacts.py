#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Freeze the selected source contracts, honest read extents and output inventory."""
import hashlib,json
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
CY='inputs/pinned/preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/'
UN='inputs/pinned/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,obj):(ROOT/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def read(path,ranges=None,mode='selected full-text passages',notes=''):
 data=(ROOT/path).read_bytes();lines=data.decode().splitlines(keepends=True)
 if ranges=='all':ranges=[(1,len(lines))]
 return {'path':path,'sha256':sha(data),'mode':mode,'notes':notes,'line_count':len(lines),'ranges':[{'start_line':a,'end_line':b,'slice_sha256':sha(''.join(lines[a-1:b]).encode())} for a,b in (ranges or [])]}
def locate(path,start,end=None):
 lines=(ROOT/path).read_text().splitlines();a=next(i for i,l in enumerate(lines,1) if start in l)
 b=next((i for i,l in enumerate(lines[a:],a+1) if end and end in l),len(lines))
 return {'path':path,'start_line':a,'end_line':b,'locator':start}
def main():
 reads=[
 read('inputs/context/AGENTS.md','all','full'),
 read('inputs/context/sources/upstream.json','all','full'),
 read('inputs/context/sources/CONTENTS.md',[(4668,4697)],notes='Catalogue entry 205 only; discovery, not theorem evidence. Other catalogue content not claimed read.'),
 read('inputs/context/sources/preprints-tree.json',mode='structured path selection',notes='Parsed complete tree to select the two manuscript prefixes and authenticate Git blob IDs; not every record read.'),
 read('inputs/context/frontier/iterations/i21-signed-saxl-dominance.md',[(1,195),(273,289)],notes='Prior project credit, especially section 2.1; its checks were not rerun or treated as current independent checks.'),
 read(CY+'README.md','all','full'),read(UN+'README.md','all','full'),
 read(CY+'build/paper.tex','all','full'),read(UN+'build/main.tex',[(1,82)]),
 read(CY+'build/sections/introduction.tex','all','full'),
 read(CY+'build/sections/specht-tools.tex','all','full'),read(CY+'build/sections/dominance.tex','all','full'),
 read(CY+'build/sections/band-quotient.tex',[(1,155)]),
 read(UN+'build/sections/introduction.tex','all','full'),read(UN+'build/sections/preliminaries.tex','all','full'),
 read(UN+'build/sections/balance.tex',[(1,130),(297,330)]),
 read('inputs/primary/harman-ryba-2023.txt','all','full',notes='Published article, title/license pages, all sections, proofs and references.'),
 read('inputs/primary/ikenmeyer-2015.txt',[(1,155),(250,500)],notes='v2; sections 1-2, start and end of 3, full sections 4-5, section 6 and references. Middle of section 3 not claimed read.'),
 read('inputs/primary/bbs-2021.txt',[(1,185),(300,338),(1310,1380)],notes='Published version. Front matter, initial modular discussion, strengthened conjecture and beginning of section 5 through Theorem 5.2 proof. Remainder keyword-searched only.'),
 read('inputs/primary/bessenrodt-bowman-2023.txt',[(1,45),(123,150),(330,480)],notes='arXiv v3. Front matter, section 1.4, selected section 3 including Theorem 3.7. Remainder keyword-searched only; published theorem text not substituted.'),
 read('inputs/pinned/LICENSE',[(1,150)],notes='Apache 2.0 heading and grants/redistribution conditions; unmodified full license archived.'),
 read('inputs/pinned/README.md','all','full'),
 ]
 represented={x['path'] for x in reads}
 for p in sorted((ROOT/'inputs/pinned').rglob('*.tex')):
  path=str(p.relative_to(ROOT))
  if path not in represented:reads.append(read(path,mode='keyword scan only',notes='Scanned for regular, integral, characteristic, unit, factorial and sum-letter terms; no full reading claimed.'))
 for p in sorted((ROOT/'inputs/primary').glob('*.pdf')):
  reads.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p.read_bytes()),'mode':'binary authentication only','notes':'Reading was through the separately hashed text extraction; no visual/PDF-wide reading claimed.'})
 for path in ['candidate.md','tensor_controls.py','projection_controls.py','run_checks.py','verify_artifacts.py','authenticate_inputs.py','freeze_artifacts.py','RIGHTS.md','LICENSE-CODE','literature-comparison.md','exploration-notes.md']:
  reads.append(read(path,'all','own artifact: authored or fully reviewed'))
 save('read-manifest.json',{'date':'2026-10-14','reader':'current research continuation','scope':'Actual source reading in this continuation only; no predecessor or parent read silently inherited','no_parent_implementation_used':True,'reads':reads})
 contracts=[
 {'id':'OAI-CY-POLYTABLOID','source':locate(CY+'build/sections/specht-tools.tex','\\begin{lemma}[Alternating blocks','\\end{proof}'),'hypotheses':'Finite position set; ordered blocks; column lengths theta; complex alphabet large enough.','conclusion':'The complex orbit of alternating initial-letter blocks is S^theta.','credit':'Inherited word/polytabloid construction. Candidate proves its own integral identification by definition, without lifting complex irreducibility.'},
 {'id':'OAI-CY-SUM-DEFICIT','source':locate(CY+'build/sections/dominance.tex','We construct a surjection','By \\Cref{lem:young-rule}'),'hypotheses':'Every m>=1; staircase repeated-row vector; pair output a+b-1; output r repeated r times.','conclusion':'Q(v_R tensor v_R)=(-1)^(sum binom(r,2)) product(r!) t_m, with t_m stabilizer the row Young subgroup.','credit':'Inherited local sum, whole square-deficit identity, factorial coefficient, and complex permutation-module quotient.'},
 {'id':'OAI-CY-SAXL','source':locate(CY+'build/sections/dominance.tex','\\begin{theorem}[Cyclic staircase support]','\\end{theorem}'),'hypotheses':'Every m>=1 and lambda partition of N=m(m+1)/2; specified row/column generator; complex field.','conclusion':'Every S^lambda occurs in C[G](v_R tensor v_C).','credit':'User accepts source truth; not required as a premise of the present integral proof.'},
 {'id':'OAI-CY-SECTORS','source':locate(CY+'build/sections/band-quotient.tex','\\begin{lemma}[Induction from coordinate sectors]','\\end{proof}'),'hypotheses':'Complex G-module with transitive position-sector decomposition, z in one sector.','conclusion':'Induced module on the stabilizer orbit is isomorphic to the full G-orbit span, with coordinate inverse.','credit':'Inherited position-sector recognition; candidate regular-word identification proved directly.'},
 {'id':'OAI-UN-MAIN','source':locate(UN+'build/sections/introduction.tex','\\begin{theorem}\\label{thm:main}','\\end{theorem}'),'hypotheses':'Every positive n except 2,4,9; complex symmetric-group representations.','conclusion':'Some irreducible has tensor-square support containing every irreducible.','credit':'Companion checked; not an integral regular inclusion and not used to prove the target.'},
 {'id':'OAI-UN-BALANCE','source':locate(UN+'build/sections/balance.tex','\\subsection{Separating components','The local support guarantees'),'hypotheses':'Specified column-block components with ordered output ranges and fixed output cardinalities and sums, over C.','conclusion':'Coordinate separation realizes induced support from local square images.','credit':'Inherited sum-letter separation method; not a new part of the candidate.'},
 {'id':'I21-REPEATED-ROW','source':locate('inputs/context/frontier/iterations/i21-signed-saxl-dominance.md','### 2.1','### 2.2'),'hypotheses':'Complex staircase V, row subgroup H, source pair projection with nonzero factorial scalar.','conclusion':'The coset map C[G/H] to C[G](v_R tensor v_R) is injective and onto its orbit span, hence identifies M^rho.','credit':'Already-existing project deduction, wholly credited, not counted again.'},
 {'id':'HR23-THEOREM-2.4','source':locate('inputs/primary/harman-ryba-2023.txt','Theorem 2.4.','Corollary 2.5.'),'hypotheses':'Any partition mu; ordinary complex permutation and Specht representations. C(mu) has i parts mu_i-mu_(i+1).','conclusion':'M^mu tensor S^mu contains M^C(mu). At mu=rho, C(mu)=(1^N).','credit':'Together with I21 already gives ordinary complex regular inclusion.'},
 {'id':'HR23-MODULAR','source':locate('inputs/primary/harman-ryba-2023.txt','3. Proof using Modular Representation Theory','References'),'hypotheses':'Every staircase, characteristic 2 over an algebraically closed field; projectivity of the 2-core Specht module.','conclusion':'Every projective indecomposable is a direct summand of the staircase cube (second proof and Remark 3.3).','credit':'Known modular summand occurrence, not novelty. Does not state a specified integral regular orbit with a unit retraction.'},
 {'id':'IK15-BETA','source':locate('inputs/primary/ikenmeyer-2015.txt','4     Construction','6    Hooks'),'hypotheses':'Triangular position set, first layers rows and columns, alternating initial-letter palettes.','conclusion':'beta(i,j)=m+2-i-j uniquely survives the row/column palette constraints; used for a nonzero contraction.','credit':'Entire labeling and palette uniqueness antecedent credited.'},
 {'id':'BBS21-STRENGTHENED','source':locate('inputs/primary/bbs-2021.txt','Strengthened Saxl Conjecture.','Generalised Saxl Conjecture.'),'hypotheses':'Characteristic 2; staircase degree.','conclusion':'Conjectures all indecomposable projectives in the square, not cube.','credit':'Known problem framing, not proved by candidate.'},
 {'id':'BBS21-PROJECTIVITY','source':{'path':'inputs/primary/bbs-2021.txt','start_line':1310,'end_line':1380},'hypotheses':'Characteristic 2, staircase 2-core.','conclusion':'Its Specht module is simple projective, square decomposes into projectives; Theorem 5.2 gives ordinary square positivity for height-zero characters.','credit':'Inherited modular approach, not new here.'},
 {'id':'BB23-3.7','source':{'path':'inputs/primary/bessenrodt-bowman-2023.txt','start_line':330,'end_line':480},'hypotheses':'arXiv v3; staircase rho_k and any lambda of its size.','conclusion':'Multiplicity of rho_k in Sym^2[lambda] minus its multiplicity in exterior^2[lambda] is 1 for lambda=rho_k and 0 otherwise.','credit':'Known square-splitting/projective-character identity, different target.'}
 ]
 for c in contracts:
  src=c['source'];data=(ROOT/src['path']).read_bytes();lines=data.decode().splitlines(keepends=True);src['file_sha256']=sha(data);src['slice_sha256']=sha(''.join(lines[src['start_line']-1:src['end_line']]).encode())
 save('source-contracts.json',{'source_pin':PIN,'accepted_true_per_user':True,'no_upstream_audit':True,'contracts':contracts,'candidate_increment':'Specified triple tensor, three-letter equality filter, refined content and coefficient +1 produce an integral G-linear retraction for all m and every base ring; significance pending.'})
 entries=[]
 for p in sorted(ROOT.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name in ['output-manifest.json','SHA256SUMS']:continue
  b=p.read_bytes();entries.append({'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b),'role':'archived_input' if p.is_relative_to(ROOT/'inputs') else 'candidate_or_evidence'})
 save('output-manifest.json',{'frozen_utc':datetime.now(timezone.utc).isoformat(),'author':'Myeongjin Kang','affiliation':None,'status':'ready_for_independent_fullproof_and_contribution_review','proof_gate':'pending','contribution_gate':'pending','manuscript_gate':'pending','campaign_count':'2/10 per user; unchanged','candidate_scope':'all m>=1; N=m(m+1)/2; z=v_R tensor v_R tensor v_C; split regular Z[S_N] summand; all commutative unital base rings','pin':PIN,'no_subagents':True,'no_parent_implementation_read':True,'no_staging_commits_uploads_or_shared_edits':True,'hash_rule':'All files except this manifest and SHA256SUMS; SHA256SUMS also covers this manifest. No recursive self-hash.','files':entries})
 covered=entries+[{'path':'output-manifest.json','sha256':sha((ROOT/'output-manifest.json').read_bytes())}]
 (ROOT/'SHA256SUMS').write_text(''.join(f"{x['sha256']}  {x['path']}\n" for x in sorted(covered,key=lambda x:x['path'])))
 print(json.dumps({'artifacts':len(entries),'candidate_sha256':sha((ROOT/'candidate.md').read_bytes()),'output_manifest_sha256':sha((ROOT/'output-manifest.json').read_bytes()),'sha256sums_sha256':sha((ROOT/'SHA256SUMS').read_bytes())},indent=2))
if __name__=='__main__':main()

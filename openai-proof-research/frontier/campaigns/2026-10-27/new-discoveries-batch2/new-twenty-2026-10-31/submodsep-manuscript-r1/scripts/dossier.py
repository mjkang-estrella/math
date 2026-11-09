from pathlib import Path
import json,hashlib,shutil
L=Path(__file__).resolve().parents[1];P=L.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda p:json.loads(p.read_text())
def write(n,o):(L/n).write_text(json.dumps(o,indent=2)+'\n')
b=J(L/'receipts/inputs-before.json');a={n:H(P/n) for n in b};assert a==b
write('receipts/inputs-after.json',a)
assert all(H(L/'evidence'/n)==v for n,v in b.items())
write('receipts/input-integrity.json',{'pass':True,'frozen_files':len(b),'originals_unchanged':True,'copies_byte_identical':True})
parents={}
for n in ['replay-result.json','registry-refresh.json']:
 p=P/'submodsep-parent-final-r1'/n
 if p.exists():
  before=H(p);dest=L/'evidence/submodsep-parent-final-r1'/n;dest.parent.mkdir(exist_ok=True)
  shutil.copy2(p,dest);assert H(p)==H(dest)==before
  parents[n]={'status':'present','sha256_before':before,'sha256_after':H(p),'receipt':J(dest)}
 else:parents[n]={'status':'pending'}
write('receipts/parent-final.json',parents)
shutil.copy2(L/'evidence/expanded-corpus-r198/raw/341850.jsonl',L/'341850.jsonl')
r=J(L/'receipts/recomputation.json')
write('receipts/raw-record.json',{'path':'341850.jsonl','sha256':H(L/'341850.jsonl'),'recorded_provenance_matches':r['raw_file_sha256']==r['recorded_raw_sha256'],'file_includes_terminal_newline':(L/'341850.jsonl').read_bytes().endswith(b'\n')})
pages=sorted((L/'qa').glob('approved-page-*.png'));assert len(pages)==6
write('receipts/page-qa.json',{'status':'PASS','inspection':'All six final pages individually viewed by the drafting assistant through view_image; checked equations, all rows, signs, readable type, page numbers, margins and absence of clipping/overlap. AI visual QA, not human approval.','pdf_sha256':H(L/'paper.pdf'),'page_count':len(pages),'render_command':'pdftoppm -scale-to 1400 -png paper.pdf qa/approved-page','pages':{str(p.relative_to(L)):H(p) for p in pages}})
disc=[
 'Retention report: journal retention NOT DETERMINED; later root ruling permits packaging with qualification. Do not infer journal-text equivalence.',
 'Review raw reference says 341850.json; actual frozen filename is 341850.jsonl. File hash matches recorded provenance, including newline.',
 'Parent replay extraction field names kirchhoff-parent-final-r1/safe_extract.py rather than the separation lane. Preserved verbatim as a cross-lane script reference; no inference of extraction failure or verification of that external script.',
 'Discovery/review HOLD dispositions precede root r2 PROCEED TO ACCEPTANCE PACKAGING; chronological decisions, not inconsistent mathematical checks.',
 'Raw MathDB open status and appended informal commentary are historical metadata; neither establishes novelty or current status.'
]
write('receipts/discrepancies.json',disc)
idx=[]
for p in (L/'evidence').rglob('receipt.json'):
 try:
  obj=J(p)
  if isinstance(obj,dict):
   rec={'receipt':str(p.relative_to(L)),'receipt_sha256':H(p)}
   for k in ['url','utc','status','sha256']:
    if k in obj:rec[k]=obj[k]
   body=p.parent/'body'
   if body.is_file():
    rec['preserved_body_sha256']=H(body)
    if isinstance(obj.get('sha256'),str):rec['recorded_body_hash_matches']=obj['sha256']==H(body)
   idx.append(rec)
 except (ValueError,OSError):pass
write('receipts/source-copies-index.json',idx)
results={'mathdb_id':341850,'title':'A Four-Edge Obstruction to Submodular Separation of Quadratic Boolean Monomial Images','status':'DRAFT; AI-assisted; root alone accepts','credit':0,'accepted':False,'campaign_context':{'count':43,'target':60,'prior':39},'page_count':6,'fresh_recomputation':{'pass':r['pass'],'cycle_bound':r['cycle_bound'],'symmetric_bound':r['bound'],'permutations':r['permutations'],'expanded_submodular_rows':r['expanded_submodular_rows'],'touched_masks':r['touched_masks'],'small_cases':r['small_cases']},'lean':{'fresh_execution':False,'endpoint':'Separation.source_existence_refuted : not Separation.SeparationExistence','packet_sha256':H(L/'lean-packet.zip'),'byte_identical':True,'safe_extraction':'PASS','recorded_independent_review':'PASS; 45 local declarations; allowed axioms propext, Classical.choice, Quot.sound'},'parent_final':parents,'journal_version_of_record':'unread; retention not certified; qualified limitation','credit_scope':'Application of Elbracht-Kneip-Teegen Lemma 4.1 / Corollary 4.2; no new general obstruction and no priority claim','discrepancies':disc,'input_integrity':'PASS','pdf_sha256':H(L/'paper.pdf'),'files':{'pdf':'paper.pdf','source':'paper.ms','source_zip':'paper-source.zip','full_zip':'full-dossier.zip','lean_packet':'lean-packet.zip','proof':'PROOF.md','guide':'REPRODUCE.md','qa':'qa/','receipts':'receipts/'}}
write('results.json',results)
summary=f"""# {results['title']}

DRAFT with OpenAI Codex assistance; no human authors or affiliations asserted.
MathDB 341850; no acceptance and zero credit assigned by this lane.

Six pages. Fresh exact recomputation PASS: four-edge cycle 0 <= -4;
13-row certificate over all 120 permutations, 1,080 submodular row instances,
365 touched masks, zero residual coefficients, 0 <= -840.
All four feasible cases (d,r)=(2,2),(3,2),(3,3),(4,2) PASS exact rational checks;
elementary-inequality counts: 6, 240, 672 and 11,520.
No Lean, lake, leanchecker, SAT or ILP solver executed here.

The shortest proof applies Elbracht-Kneip-Teegen, Lemma 4.1 / Corollary 4.2.
No new general obstruction, priority claim or resolution of modular submodular
minimization itself is made. The larger certificate is the supplied Lean proof.

Packet SHA256 {H(L/'lean-packet.zip')}, byte-identical.
Safe extraction PASS. Historical strict formal checks are recorded, not reenacted.
Parent-final replay and registry receipts are present: replay verdict
{parents.get('replay-result.json',{}).get('receipt',{}).get('verdict','pending')};
registry verdict {parents.get('registry-refresh.json',{}).get('receipt',{}).get('verdict','pending')}.
All {len(b)} initially frozen inputs and copies match before/after hashes.
All six final PDF pages were rendered and individually inspected.

Journal version of record remains unread. Retention report says NOT DETERMINED;
root r2 permits packaging with that explicit qualification. The review's
.json/.jsonl mismatch and parent receipt's cross-lane extraction-script reference
are preserved in receipts/discrepancies.json. No mathematical discrepancy found.

Deliverables: paper.pdf; paper.ms plus scripts/layout.tmac; PROOF.md; results.json;
REPRODUCE.md; 341850.jsonl; qa/approved-page-1.png through approved-page-6.png; receipts/; evidence/;
lean-packet.zip; paper-source.zip; full-dossier.zip; MANIFEST.sha256;
DELIVERABLES.sha256. Full ZIP contains payload and its manifest. Outer archive
verification and package receipts avoid self-hash circularity.
"""
(L/'SUMMARY.md').write_text(summary)
proof="""# Exact proof dossier: MathDB 341850

DRAFT with AI assistance. No human authors, affiliations, new general obstruction
or priority claim. Journal version of record unread; retention not certified.

## Setting and theorem

Index outputs by all subsets S of [d] with |S|<=r, including empty S.
phi(x) records their monomials, and F is its image. Submodularity is
f(A intersect B)+f(A union B)<=f(A)+f(B).
At (r,d)=(2,5), n=1+5+10=16, no submodular integer function has f<=-1 on F
and f>=0 off F. Thus preprint Conjecture 3.33 fails without its evaluation clause.

## Shortest proof, applying Elbracht-Kneip-Teegen

On the constant-one face, bit labels (least significant first) are
0,1,2,3,4,01,02,03,04,12,13,14,23,24,34.
Good masks contain exactly all pairs of their singleton support.
The review supplies these four outer dependency edges:

| a | b | good c | meet | join | bad companion |
|---:|---:|---:|---:|---:|---:|
"""
for row in r['cycle']:proof+='| '+' | '.join(str(row[k]) for k in ['a','b','c_good','meet','join','other'])+' |\n'
proof+="""
All a,b and companion masks are bad. For every row submodularity implies
h(b)<=h(a)+h(c)-h(companion)<=h(a)-1. The endpoints form a cycle, so summing
gives 0<=-4. This applies Elbracht, Kneip and Teegen, The Structure of Submodular
Separation Systems, arXiv:2103.13162v2, Lemma 4.1 and Corollary 4.2.
It even excludes real-valued separators with these quantitative signs.
Shortest describes the proof presented, not certified graph-girth minimality.

## Independent symmetric proof (the supplied Lean argument)

Define g(m)=sum_sigma h(sigma m) over all 120 permutations. Coordinate renaming
preserves meet, join and goodness; g is submodular and orbit invariant, <=-120
on good masks and >=0 on bad masks. The complete weighted support follows.
For submodular rows, terms are (meet,+1),(join,+1),(a,-1),(b,-1).
Good rows contribute +weight*g(point); bad rows contribute -weight*g(point).

"""
proof+='\n'.join('    '+line for line in json.dumps(r['support'],indent=2).splitlines())+'\n'
proof+="""
All expanded coefficients on actual masks cancel. Good weight 5+2=7 yields
-600-240=-840, so 0<=-840. The fresh script derives actions from definitions,
ignoring supplied orbit tables. Full receipt: receipts/recomputation.json.

## Small feasible cases and formal correspondence

Four supplied face vectors are rationally reconstructed and checked with exact
Fraction arithmetic. Elementary two-bit inequalities imply full submodularity
by telescoping diminishing returns. H(z,m)=h(m)+C*(1-z), C>=-min h, is submodular,
nonnegative on the constant-zero slice, and agrees on the constant-one face.
Clearing denominators gives integer full-cube witnesses in receipts/witness-d-r.json.

Separator.lean models the entire allowed Boolean lattice by subset-labeled
coordinates; phi is filtered powerset and includes empty. Certificate.lean
embeds the face, proves actual permutation identities and the symmetric
contradiction, then proves:
Separation.source_existence_refuted : not Separation.SeparationExistence.
The universal assertion ranges over every d,r with r<=d. Specialization at
d=5,r=2 refutes bare existence, hence the stronger evaluation-time assertion.
A separate numeric-coordinate bijection and complexity model are not formalized.

The six-member packet is byte-identical. Strict replays, 45-declaration audits
and allowed axioms (propext, Classical.choice, Quot.sound) are recorded evidence;
this task executed no formal checker. See receipts/parent-final.json for root
replay and bounded registry screen, including the extraction-path oddity.
Upstream mathlib is trusted, not fully rebuilt.

The result blocks the universal separator premise of the proposed
SUBMOD-MIN-MOD_M reduction (Proposition 3.34, Corollary 3.35), not the
optimization problem itself. Source quotation and references: paper.ms/PDF.
The unread journal and non-exhaustive prior-art review remain limitations.
"""
(L/'PROOF.md').write_text(proof)
print('Documents, six-page QA receipt, parent copies and input integrity PASS')

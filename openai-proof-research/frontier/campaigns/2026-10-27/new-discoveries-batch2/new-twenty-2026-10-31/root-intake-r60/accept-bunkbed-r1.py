"""Root final packet and acceptance record for MathDB 382297. Documentary only; no root Lean. Root hand-checked the short proof earlier and read every page of the final paper."""
import os,resource,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,shutil,zipfile
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();lp=P/'ledger.json';led=read(lp)
assert led['accepted_new']==len(led['accepted'])==57 and led['target_new']==80 and not (P/'transitive-bunkbed-acceptance.json').exists() and 382297 not in {int(x['mathdb_id']) for x in led['accepted']}
F=P/'transitive-bunkbed-root-final-r1';R=P/'transitive-bunkbed-formal-independent-review-claude-r1';A=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';Q=P/'transitive-bunkbed-primary-qualification-sol-r2'
ir=read(P/'transitive-bunkbed-formal-independent-review-parent-integration-r1.json');ar=read(P/'transitive-bunkbed-endpoint-assembly-formal-parent-integration-r23.json');qr=read(P/'transitive-bunkbed-qualification-parent-integration-r2.json')
assert ir['root_disposition']=='TECHNICAL_PASS_ADOPTED_PENDING_PAPER_AND_ROOT_ADJUDICATION' and ar['root_disposition']=='LITERAL_ENDPOINT_KERNEL_CHECKED_INDEPENDENT_AUDIT_NEXT' and qr['root_disposition'].startswith('PROSPECTIVE_SCIENTIFIC_PASS')
assert sha(R/'MANIFEST.json')==ir['manifest_sha256'] and sha(A/'MANIFEST.json')==ar['manifest_sha256'] and sha(Q/'SHA256-MANIFEST.json')==qr['manifest_sha256']
order=read(R/'packet/BUILD-ORDER.json');hashes=read(R/'packet/SOURCE-HASHES.json');assert len(order)==33 and all(sha(R/'src'/(m+'.lean'))==hashes[m] for m in order) and all(sha(A/'src'/(m+'.lean'))==hashes[m] for m in order)

# Paper: the audit paragraph in regular type with a bold run-in head. Status and proof text unchanged.
rf=F/'source/bunkbed-transitive-tournaments.roff';s=rf.read_text();cor=read(F/'qa/ROOT-CORRECTIONS.json')
key='Independent audit. A separate reviewer';assert s.count(key)==1
i=s.index(key);before=s[:i];after=s[i:]
assert before.rstrip().endswith('.ft B'),before[-80:]
end=after.index('\n');para=after[:end];rest=after[end+1:];assert rest.startswith('.ft R'),rest[:40]
before=before.rstrip()[:-len('.ft B')].rstrip()+'\n'
new=before+'.ft B\nIndependent audit.\n.ft R\n'+para[len('Independent audit. '):]+'\n'+rest[len('.ft R\n'):];rf.write_text(new)
ps=F/'qa/doc.ps';pdf=F/'output/pdf/bunkbed-transitive-tournaments.pdf'
r=subprocess.run(['groff','-Tps',str(rf)],capture_output=True);assert r.returncode==0 and not r.stderr.strip(),r.stderr;ps.write_bytes(r.stdout)
r2=subprocess.run(['ps2pdf',str(ps),str(pdf)],capture_output=True);assert r2.returncode==0,r2.stderr;ps.unlink()
for q in F.glob('qa/page-*.png'):q.unlink()
assert subprocess.run(['pdftoppm','-r','150','-png',str(pdf),str(F/'qa/page')],capture_output=True).returncode==0
txt=subprocess.run(['pdftotext','-layout',str(pdf),'-'],capture_output=True,text=True).stdout;pages=txt.count('\f');assert pages==6 and 'credit 0' not in txt.lower() and 'INDEPENDENT AUDIT STATUS' not in txt and 'theorem bunkbed_E7_transitive' in txt
cor['corrections'].append(dict(kind='layout',before='audit paragraph entirely bold',after='regular type with a bold run-in head'));(F/'qa/ROOT-CORRECTIONS.json').write_text(json.dumps(cor,indent=2)+'\n')

# Source-only certificate.
readme='''The bunkbed conjecture for transitive tournaments - MathDB 382297 - source-only certificate

This archive contains the 33 Lean modules whose final theorem is Bun.bunkbed_E7_transitive, in src/, plus audit and control modules in audit/. PINS.json gives Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and executable hashes. Upstream libraries are trusted read-only.

To rebuild: create an empty build directory, set LEAN_PATH to build followed by the pinned mathlib and dependency library paths, then for each module in BUILD-ORDER.json in order run lean -j1 -M3500 -DwarningAsError=true -o build/MODULE.olean src/MODULE.lean and leanchecker MODULE, with LEAN_NUM_THREADS=1. Use specific imports as shipped. A 6 GiB address-space limit is too small for this toolchain's import mapping; the checked runs used 32 GiB of address space and a 6 GiB real-memory guard. No olean is shipped. SOURCE-HASHES.json binds every production source.

An independent reviewer performed a fresh extracted replay of all 33 modules from an empty build. Only propext, Classical.choice and Quot.sound are transitive axioms. See FINAL-REVIEW.md and review.json.

Limits: bounded prior-art search; the final journal version of Przybylowski, DOI 10.1016/j.ejc.2025.104289, was not read; upstream libraries were not rebuilt; the relabeling of an abstract transitive tournament to Fin n is not formalized; no peer review, priority or worldwide novelty is claimed.
'''
zp=F/'output/bunkbed-382297-source-only.zip'
with zipfile.ZipFile(zp,'w',zipfile.ZIP_DEFLATED) as z:
 def add(name,data):
  info=zipfile.ZipInfo(name,date_time=(2026,11,9,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,data)
 for m in sorted(order):add(f'src/{m}.lean',(R/'src'/(m+'.lean')).read_bytes())
 add('audit/AuditFinal.lean',(A/'src/AuditFinal.lean').read_bytes());add('audit/AuditClosure.lean',(R/'src/AuditClosure.lean').read_bytes());add('audit/ControlE.lean',(R/'src/ControlE.lean').read_bytes())
 add('PINS.json',(R/'PINS.json').read_bytes());add('BUILD-ORDER.json',(R/'packet/BUILD-ORDER.json').read_bytes());add('SOURCE-HASHES.json',(R/'packet/SOURCE-HASHES.json').read_bytes());add('README.txt',readme.encode());add('FINAL-REVIEW.md',(R/'FINAL-REVIEW.md').read_bytes());add('review.json',(R/'review.json').read_bytes())
(F/'source/README.txt').write_text(readme)
for n,q in {'independent-FINAL-REVIEW.md':R/'FINAL-REVIEW.md','independent-review.json':R/'review.json','second-qualification-REVIEW.md':Q/'REVIEW.md','second-qualification-PROOF.md':Q/'PROOF.md'}.items():shutil.copyfile(q,F/'evidence'/n)
views=dict(utc=now,pdf=str(pdf.relative_to(F)),sha256=sha(pdf),pages=[dict(page=i,path=f'qa/page-{i}.png',sha256=sha(F/f'qa/page-{i}.png')) for i in range(1,7)],root_reading='Root read the full text and viewed all six pages of the preceding build; the final build changes only the audit paragraph from bold to regular type. Legible; no clipping, overlaps or missing formulas.',quotations_checked='All direct quotations from Hollom were matched against the supplied journal text.')
save(F/'qa/root-archival-visual-QA.json',views)
accept=dict(utc=now,mathdb_id=382297,title='The bunkbed conjecture for transitive tournaments',status='accepted_in_new_eighty_campaign',credit=1,campaign_ordinal=58,exact_endpoint=['Bun.bunkbed_E7_transitive','Bun.prob_layer_true_le_false','Bun.card_token','Bun.card_out'],scope='For every n and all u,v : Fin n, the number of outcomes on the n*n tokens of the transitive tournament T_n bunkbed in which (u,false) reaches (v,true) is at most the number in which it reaches (v,false). One independent fair horizontal token per arc per layer, one shared bidirectional vertical token per index, reachability as reflexive transitive closure, fixed endpoints.',source_targets=['MathDB382297','Hollom arXiv 2406.01790 Definitions 1.1-1.4, Model 4.5, Conjecture 6.4','European Journal of Combinatorics 128 (2025) 104188, model D7'],paper=str(pdf.relative_to(P)),editable_paper=str(rf.relative_to(P)),proof_packet=str(zp.relative_to(P)),independent_review=str((R/'FINAL-REVIEW.md').relative_to(P)),keyed_gates=str((R/'review.json').relative_to(P)),root_integrity=['transitive-bunkbed-endpoint-assembly-formal-parent-integration-r23.json','transitive-bunkbed-formal-independent-review-parent-integration-r1.json','transitive-bunkbed-qualification-parent-integration-r2.json'],validation='Thirty-three modules compiled and kernel-checked from an empty build twice: in the assembly lane and, from a sealed archive, in the independent review. Reviewer read all modules; transitive closure of 6913 constants has only the three permitted axioms and no unsafe or partial constant; Lean controls at n=1 and n=2; statement fidelity PASS against the source and the literal. Root verified receipts, hashes and the mathlib pin.',axioms=['propext','Classical.choice','Quot.sound'],pins=dict(Lean='4.34.1',mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612'),substantive_reason='Resolves the exact infinite family posed by Hollom as Conjecture 6.4, in the correct model, after the statement was shown to fail for general acyclic digraphs. It is not a scope, domain or endpoint repair. The source calls the case more difficult than expected and says complete-graph methods lack the needed symmetries. The proof finds the exact sufficient statistic that completeness of the order provides.',contrary_scope_assessment='The proof is short and elementary and uses an old reflection idea; E7 is an instance of an immediately derived column-homogeneous extension, which carries no separate credit. No complete applicable prior-to-target bridge was found despite direct attempts through injections, the van Hintum-Lammers and Leander arguments and the Przybylowski paper. Significance is recorded as modest.',novelty_standard='Qualified bounded source-primary investigation, not worldwide priority certification.',prior_limits='The final journal version of Przybylowski, DOI 10.1016/j.ejc.2025.104289, is closed and unread; the supplied arXiv v2 is not final-equivalence evidence. Registry roots closed. Four searches in total across two reviews found no proof or disproof.',process_adjudication='Disclosed and judged non-substantive: the second qualification read the raw line after the author proposal; the assembly lane ran verify_frozen once without its argument and one read-only one-liner outside its runner; the independent reviewer ran display filters and one scratchpad edit outside its runner; earlier Pi lanes inspected signatures before first writes. Certificate content rests on fresh replay and independent audit rather than on those histories.',trust_limits='Upstream Lean, mathlib and their oleans are trusted through pins and were not rebuilt. Reviewers are AI systems, not human referees. The relabeling of an abstract transitive tournament to Fin n is not formalized and is trivial.',paper_corrections='Root corrected Remark 4.1 and status text only; see qa/ROOT-CORRECTIONS.json. The main proof was not changed.',not_claimed=['Worldwide novelty or publication priority','Human peer review','Separate credit for the column-homogeneous extension','Any statement for general acyclic digraphs'],model_note='Proof by GPT-6.1 Sol; Lean by GLM-5.3 Flash, DeepSeek V4.1 Flash and GPT-6.1 Sol; independent audit by Claude Opus 5.5; paper drafted by DeepSeek V4.1 Flash and corrected by root.',artifact_sha256=dict(paper=sha(pdf),roff=sha(rf),packet=sha(zp),independent_review=sha(R/'FINAL-REVIEW.md')))
save(F/'ACCEPTANCE.json',accept);save(P/'transitive-bunkbed-acceptance.json',accept)
files=sorted(q for q in F.rglob('*') if q.is_file() and q.name!='SHA256-MANIFEST.json');save(F/'SHA256-MANIFEST.json',dict(count=len(files),files=[dict(path=str(q.relative_to(F)),sha256=sha(q),bytes=q.stat().st_size) for q in files]))
led['accepted'].append(dict(mathdb_id=382297,file='transitive-bunkbed-acceptance.json',utc=now));led['accepted_new']=58;led['status']='active_research_58_of_80_accepted'
led['latest_root_acceptance']=dict(utc=now,mathdb_id=382297,credit=1,accepted_new=58,target_new=80,previous_accepted=39,record='transitive-bunkbed-acceptance.json',qualifications='Bounded prior art; acyclic final unread; modest significance; AI-only review.')
for c in led['candidates']:
 if int(c['mathdb_id'])==382297:c['status']='accepted_in_new_eighty_campaign';c['credit']=1;c['acceptance']='transitive-bunkbed-acceptance.json'
led['process_notes'].append(dict(utc=now,item='382297 accepted as result 58 by root after second qualification, literal Lean endpoint, independent formal audit and paper.'));lp.write_text(json.dumps(led,indent=2)+'\n')
print(json.dumps(dict(accepted_new=58,target_new=80,total=97,pages=pages,pdf=sha(pdf),packet=sha(zp),files=len(files))))

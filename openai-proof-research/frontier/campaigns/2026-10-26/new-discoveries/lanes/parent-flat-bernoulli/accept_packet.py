"""Finalize acceptance only after checking the fresh extracted strict replay."""
from pathlib import Path
import hashlib, importlib.util, json, re, zipfile
R=Path(__file__).resolve().parents[2];C=R/'candidates/hetyei';E=R/'build/hetyei-packet-audit-v1/hetyei'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
a=(E/'build/verified/audit.json').read_bytes()
assert a==(C/'verification/parent-audit.json').read_bytes()==(C/'verification/independent-audit.json').read_bytes()
j=json.loads(a);assert j['status']=='PASS' and j['declarations']==117 and len(j['modules'])==16
logs=[E/'build/verified'/ (Path(x['path']).stem+'.log') for x in j['modules']];assert all(p.stat().st_size==0 for p in logs)
checks=(E/'build/verified/Checks.log').read_text();assert checks.count('depends on axioms:')==117
assert checks.count('depends on axioms: [propext, Quot.sound]')==3
assert checks.count('depends on axioms: [propext, Classical.choice, Quot.sound]')==114
# Parent has read every actual report in full, including both closed endpoints.
p=R/'candidate-packets/319292-hetyei-proof.zip'
with zipfile.ZipFile(p) as z:
 assert z.testzip() is None
 payload={n.removeprefix('hetyei/'):z.read(n) for n in z.namelist()}
 manifest=json.loads(payload['MANIFEST.json'])
 assert len(payload)==99 and len(manifest)==98
 for n,h in manifest.items():
  assert sha(payload[n])==h==sha((C/n).read_bytes())==sha((E/n).read_bytes()),n
spec=importlib.util.spec_from_file_location('builder',Path(__file__).with_name('build_packet.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert m.archive_bytes(payload)==p.read_bytes()
receipt=sha(a)
accept={
 'status':'ACCEPT: all five independent gates and fresh extracted strict replay PASS',
 'discovery_count_credit':1,'combined_outcome_number':22,'mathdb_id':319292,
 'source_target':'Hetyei arXiv0912.0573v1 Conjecture6.10, explicit count formula(16)',
 'theorem':'For every n>=12, kappa_n<n*kappa_(n-1); equivalently K_n<n*K_(n-1) for every n>=11, with literal finite ordered-composition factorial counts.',
 'scope':'ONE combined full all-order source-conjecture resolution. The source enumeration theorem is credited upstream; all explicit finite count, composition, factorial, matrix, spectral, recurrence and limit bridges proved. Helpers, finite checks, source sign typo and metadata corrections uncounted.',
 'formal_declarations':117,'formal_modules':16,
 'parent_independent_extracted_receipt_sha256':receipt,
 'all_extracted_types_and_axioms_read_by_parent':True,
 'axioms':j['axioms'],'all_module_logs_zero_bytes':True,
 'packet':str(p.relative_to(R)),'packet_sha256':sha(p.read_bytes()),
 'archive_members':99,'archive_payload_manifest_files':98,
 'archive_readback_manifest_and_deterministic_rebuild':'PASS',
 'extracted_replay':str((E/'build/verified/audit.json').relative_to(R)),
 'paper_sha256':sha((C/'paper.pdf').read_bytes()),
 'independent_review_sha256':sha((C/'reviews/final/review.md').read_bytes()),
 'review_reconciliation':'reviews/parent-final-addendum.md','reviewed_originals_preserved':69,
 'manuscript_corrections':'Presentation only: matrix moment A notation, abstract wording and operational status prose. Original reviewed tex/PDF/log/QA retained; all mathematics, formal sources and verifier unchanged. Release paper rendered and all3pages inspected.',
 'source_limits':['Final published JCTA body inaccessible; actual source arXiv read','Sterling2018 final body paywalled; Timber thesis chapter read, not final article'],
 'novelty_limits':['Two independent bounded prior-art screens found no known resolution or direct subsuming theorem; no worldwide-priority guarantee','Keyword/citation-index coverage is incomplete; no proof inferred from empty MathDB or citation counts','Classical spectral, convexity and Faulhaber ingredients credited, not claimed new'],
 'historical_thread_read':'Completed final T3 result position107 read in full; entire independent review/provenance and all117 extracted actual type/axiom reports read by parent.',
 'acceptance_note':'Post-extraction acceptance record outside immutable self-hashed archive. Historical credit0 snapshots describe preacceptance state.'}
ledger=json.loads((R/'ledger.json').read_text());assert ledger['discovery_count']==21 and len(ledger['accepted'])==21 and not (C/'acceptance.json').exists()
write(C/'acceptance.json',accept)
ledger['accepted'].append({'number':22,'mathdb_id':319292,'path':'candidates/hetyei','title':'All-order adjacent-count inequality for the flat Bernoulli game','status':accept['status'],'formal_declarations':117,'formal_modules':16,'discovery_count_credit':1,'scope':accept['scope'],'novelty_limit':'Final JCTA/Sterling body and comprehensive worldwide coverage remain unavailable; bounded independent screen found no known resolution. No worldwide-priority claim.','packet':accept['packet'],'packet_sha256':accept['packet_sha256'],'acceptance':'candidates/hetyei/acceptance.json','receipt_sha256':receipt})
ledger['candidates']=[x for x in ledger['candidates'] if x.get('mathdb_id')!=319292];ledger['discovery_count']=22;write(R/'ledger.json',ledger)
s=(R/'RESULTS.md').read_text().replace('**21/30**','**22/30**');last='| 21 | Uniform Burnside-Gautschi conjecture for interpolated gamma values, MathDB372858 | 49 | [Paper](candidates/schmidlin/paper.pdf) | [ZIP](candidate-packets/372858-schmidlin-proof.zip) |';assert last in s
s=s.replace(last,last+'\n| 22 | All-order flat-Bernoulli adjacent-count conjecture, MathDB319292 | 117 | [Paper](candidates/hetyei/paper.pdf) | [ZIP](candidate-packets/319292-hetyei-proof.zip) |')
s+='\nOutcome22 proves Hetyei Conjecture6.10 for every n>=12 using the literal ordered-composition factorial count. The source enumeration theorem and classical spectral/power/Faulhaber facts are credited. All117 declarations in16modules pass parent, independent and fresh extracted strict replays with byte-identical receipts; every extracted type/axiom report was read. The99-member deterministic packet passes readback, all98 payload hashes and byte-identical rebuild. All69 original reviewed files are preserved; the release paper has presentation-only changes and all3pages were inspected. Published JCTA/Sterling and bounded-search limits remain explicit. No helper, typo, metadata-correction or worldwide-priority claim.\n';(R/'RESULTS.md').write_text(s)
s=(R/'NEXT.md').read_text().replace('**21/30**','**22/30**').replace('active;9further','active;8further')
s+='\n2026-10-27 Hetyei ACCEPTED as outcome22: all five independent gates plus fresh extracted117/16 strict replay PASS. Receipt '+receipt+', deterministic99-member packet '+accept['packet_sha256']+'. All117 extracted types/axioms read, all16 logs empty. Original69 reviewed files preserved; release paper3pages clean, presentation-only changes. Only the complete source Conjecture6.10 counts. Prior-art/source-access limits retained; MathDB2002companion grouping error documented without credit. Earlier pending-review/credit0 checkpoints superseded only by candidates/hetyei/acceptance.json.\n';(R/'NEXT.md').write_text(s)
print(json.dumps({'accepted':22,'target':30,'packet_sha256':accept['packet_sha256'],'receipt_sha256':receipt},indent=2))

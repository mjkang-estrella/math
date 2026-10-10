"""Assemble flat references and honest read receipts; never seals or runs ancestors."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i154_dimension_independent_oracle_tolerance'
E='frontier/experiments/i154_dimension_independent_oracle_tolerance'
OLD='frontier/sources/i152_algorithmic_sampling_reconstruction_discovery'
assert not (R/S/'seal.json').exists()
def data(p):return json.loads((R/p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,x):(R/p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def receipt(p,a=1,z=None):
 b=(R/p).read_bytes();ls=b.decode().splitlines();z=z or len(ls)
 return dict(local=p,start=a,end=z,line_count=len(ls),file_sha256=sha(b),passage_sha256=sha('\n'.join(ls[a-1:z]).encode()),ending=ls[z-1],convention='splitlines; LF join without appended LF')
passages=data(S+'/display-log.json')
# Two ledger displays were truncated and are NOT credited as complete readings.
passages=[x for x in passages if x['local'] not in [S+'/snapshots/README.md',S+'/snapshots/frontier/README.md']]
# Actual complete reads before the logger, and a parallel display whose logger update raced.
for p,a,z in [(S+'/direct-context.txt',1,150),(S+'/direct-context.txt',151,310),(S+'/direct-context.txt',311,709),(S+'/snapshots/AGENTS.md',1,None),(S+'/snapshots/sources/upstream.json',1,None),(S+'/primary/inexact.txt',434,560)]:
 x=receipt(p,a,z)
 if x not in passages:passages.append(x)
passages=sorted(passages,key=lambda x:(x['local'],x['start'],x['end']))
save(S+'/read-manifest.json',{'passages':passages,'scope':'Actual new display ranges, with truncation recoveries in reading-notes. Hash checking is not semantic reading. Ledger excerpts only; no full-ledger claim.'})
old=data(OLD+'/inheritance.json');refs={x['path']:x['sha256'] for x in old['immutable']}
anchors=old['anchors']+[dict(base=OLD,seal=OLD+'/seal.json',sha256=sha((R/OLD/'seal.json').read_bytes()),inventory=OLD+'/inventory.json')]
for a in anchors:
 refs[a['seal']]=a['sha256']
 for p,h in data(a['seal'])['sha256'].items():refs[p]=h
for x in data(S+'/input-freeze.json'):
 if x['path'] not in old['live_ledgers']:refs[x['path']]=x['sha256']
for x in data(S+'/overlap-search.json')['refs']:refs[x['path']]=x['sha256']
for x in passages:
 if not x['local'].startswith(S+'/'):refs[x['local']]=x['file_sha256']
inherited_passages=old['inherited_passages']+data(OLD+'/read-manifest.json')['passages']
for x in inherited_passages:refs[x['local']]=x['file_sha256']
assert not any(re.search(r'/(?:i|iteration)(151|153)[-_]',p) for p in refs)
save(S+'/inheritance.json',dict(anchors=anchors,immutable=[dict(path=p,sha256=h) for p,h in sorted(refs.items())],inherited_passages=inherited_passages,lexical_records=old['lexical_records']+[OLD+'/lexical-search.json'],live_ledgers=old['live_ledgers'],scope='Flat immutable references only; no active I151/I153 binding, no ancestor execution or corpus copying.'))
# Correct this round's descriptive domain label; the computed positions/bytes are untouched.
ov=data(S+'/overlap-search.json');ov['scope']='Frozen prior-report domain excluding active I151/I153 and own I154; completed I150 is an ordinary lexical reference only; family numbers are not iteration numbers.';save(S+'/overlap-search.json',ov)
domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json');bylocal={x['local']:x for x in domain}
save(S+'/selected-source-bindings.json',[bylocal[p] for p in sorted({x['local'] for x in passages if x['local'] in bylocal})])
notes={
 'original_audit_completed_before_discovery':True,
 'mandatory_task_sha256':'f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379',
 'decoded_reading':{'mandatory_stream_lines':709,'inherited_unique_stream_lines':7800,'unique_pieces':2232,'decoded_coverage_records':3570,'paragraph_coverage_records':2022,'parent':'All fields read; stdout decoded exactly equals result; parent_review separately read in full. Original parent bytes remain a distinct snapshot.'},
 'truncated_displays':[
  'Inherited context 1-500: recovered 90-125 and 120-240.',
  'Inherited context 1101-1800: recovered 1200-1220 and 1220-1510.',
  'Inherited context 2151-2700: 86-token omitted area recovered 2449-2465.',
  'Inherited context 4401-4850: 187-token omitted area recovered 4678-4694.',
  'Initial combined live-ledger output and later README 1-67/frontier README 1-90 were truncated; no full semantic-read credit. Current I152 paragraphs, accepted-count scope, TEN-FINDINGS 713/721/723 and iterations README 1833-1845 were inspected; snapshots bind all bytes.',
  'A late diagnostic print of old decoded field names produced a 65210-token truncated display. No new semantic-read credit; all 2232 decoded pieces had already been read through the 7800-line stream.',
  'Two independent primary reads raced when recording display-log.json; the fully displayed inexact 434-560 receipt is restored in read-manifest.json. Future logged reads were sequential.'
 ],
 'failed_retrievals_or_paths':[
  'A search for i112/pdf-bindings.json failed: that path does not exist. The existing search-domain.json contains all 776 bindings.',
  'Attempted overlap passage i128-mixed-jet-operations.md failed (wrong filename). Recovered actual i128-statistical-learning-discovery.md 91-101.',
  'Cloud PDF extraction exited zero with font-type mismatch warning; exact stderr retained in additional-retrieval.json.',
  'Springer URLs redirected through cookies_not_supported parameters but returned 200 PDF/HTML; actual final URLs and bytes retained.'
 ],
 'primary_versions':{'shifted1':'arXiv 2311.14520 v1; published IEEE TIT 2025 record distinguished','shifted3':'arXiv 2412.17997 v1 plus distinct June 11 2026 journal PDF; operative Section 3.1 read in both','inexact':'arXiv 1710.00095 v4 (February 23 2024)','picard':'arXiv 2609.06906 v2 (September 29 2026)','cloud':'arXiv 2609.38710 current metadata retained; only complete Theorem 1.1 interface read, not whole proof','chen-liu':'2610.06724 v1; unary-capacity and arithmetic operative proofs read','hhp':'1708.02216 v1; full inherited extracted text read','stochastic':'PMLR 336 chen26g 2026; relevant proof ranges only'},
 'no_ancestor_runs':True,'inherited_pdf_reextractions':0,'corpus_copies':0,
 'normalization':'UTF-8 replacement decode and Python splitlines for lexical records; zero-based Unicode codepoint spans. Passage convention is stored per record; SHA-256 is on bytes or stated LF-joined passage. Raw PDF and extracted text hashes are distinct.',
 'scope':'Evidence reading and finite replay are not universal-proof, contribution, priority, acceptance or human/formal certification.'
}
save(S+'/reading-notes.json',notes)
print(json.dumps({'immutable_references':len(refs),'read_passages':len(passages),'inherited_passages':len(inherited_passages),'anchors':len(anchors)},indent=2))

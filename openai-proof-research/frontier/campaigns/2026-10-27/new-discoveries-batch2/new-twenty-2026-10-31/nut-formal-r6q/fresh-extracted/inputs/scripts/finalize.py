from pathlib import Path
import hashlib,json,re,zipfile,collections
r=Path(__file__).resolve().parents[1]
replay=json.loads((r/'fresh-extracted/logs/replay.json').read_text())
assert replay['status']=='PASS PARTIAL r3b PACKET ONLY'
receipts=replay['receipts'];assert len(receipts)==115
assert all(c['cap_reason'] is None for c in receipts)
audit=(r/'fresh-extracted/logs/strict-AuditR3.log').read_text()
count=int(re.search(r'LOCAL_TOTAL (\d+)',audit).group(1))
by_module=collections.Counter(re.findall(r'MODULE some\s+(\S+) DECL ',audit))
# The audit pretty-printer may parenthesize Option values; collect exact module lines too.
module_lines=[x for x in audit.splitlines() if 'MODULE ' in x and ' DECL ' in x]
assert len(module_lines)==count
for row in json.loads((r/'inputs-before.json').read_text()):
 assert hashlib.sha256(Path(row['source']).read_bytes()).hexdigest()==row['sha256']
 assert hashlib.sha256((r/row['copy']).read_bytes()).hexdigest()==row['sha256']
for p in (r/'inputs/nut-formal-r2/formal').glob('*.lean'):
 assert (r/'formal'/p.name).read_bytes()==p.read_bytes()
mods=json.loads((r/'modules.json').read_text())
for m in mods:
 assert (r/'formal'/(m+'.lean')).read_bytes()==(r/'fresh-extracted/formal'/(m+'.lean')).read_bytes()
maxmem=max(c['peak_private_bytes'] for c in receipts);wall=sum(c['wall_seconds'] for c in receipts)
result={'365943':{'status':'partial_zero_credit','required_endpoint':'finite_obstruction : Nut8.FiniteObstruction','endpoint_exists':False,'endpoints':[], 'exact_statement':'∀ C ε s, Nut8.Admissible C ε s → ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)', 'declaration_counts':{'all_local_including_generated':count,'audited_modules':len(mods)-1,'strictly_compiled_modules':len(mods)},'completed':['B1 permutation and structural switching invariances and refutation transport','B2 finite extension closure computations, without graph induction','B4 signs for an explicitly ordered parent tree, without graph-to-parent extraction','B5 first 32 r2 certificates'], 'missing':['universal graph coverage induction and graph encoding bridge','augmentation completeness','graph-to-tree and normalized-matrix membership bridges','remaining 9140 normalized certificates','B6 composition'], 'graph_counts':[1,1,2,6,10,29,64,194],'extension_counts':[1,3,14,45,117,384,1158],'new_certificate_records_checked':32,'replay':{'status':replay['status'],'calls':len(receipts),'wall_seconds_sum':wall,'peak_sampled_private_bytes':maxmem,'audit':'fresh-extracted/logs/strict-AuditR3.log','receipts':'fresh-extracted/logs/replay.json','negative_lean_controls':5,'existing_olean_refusal':True},'input_files':32,'inputs_unchanged':True,'inherited_lean_modules_byte_identical':True,'development_log_limitation':'Some failed development logs were overwritten; final extracted replay logs complete','source_packet':'nut-r3b-source.zip','self_accepted':False}}
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(r/'SUMMARY.md').write_text(f'''# MathDB 365943 r3b: incomplete Part B, zero credit

The required theorem `finite_obstruction : Nut8.FiniteObstruction` was not
proved. No unconditional endpoint exists and this packet does not meet the
assignment's acceptance gate. No result is self-accepted and counts are unchanged.
GAPS.md lists the precise remaining obligations.

Implemented and strictly replayed:

- B1: permutation invariance of Admissible; cofactor relabelling; sign-free
  structural switching invariance; determinant and principal-cofactor switching
  invariance in arbitrary dimension; refutation transport.
- B2 finite data: lists of sizes 1, 1, 2, 6, 10, 29, 64, 194, with 1,722 explicit
  extension isomorphism certificates, including 1,158 at the final step. Every
  eligible neighbor mask for every listed source is kernel checked against
  explicit target and permutation data. Generic checker soundness is proved.
  The universal connected-graph induction is still absent.
- B4 algebra: a well-founded parent-tree sign construction, sign values and
  normalization of parent-edge signs and weights. Connected-graph extraction
  of such parent data remains absent.
- B5: the first 32 r2 matrix certificate records, using the byte-identical
  sparseDet correctness theorems. The remaining 9,140 records are not checked.
  The trial took 25.92 seconds and 2.44 GB sampled private memory; extrapolation
  to a full run is only a planning estimate. B3 and B6 remain unimplemented.

Fresh source-only extraction `fresh-extracted` passed strict sanitized rebuild,
separate leanchecker for all {len(mods)} scheduled modules, and all-declaration audit of
{count} local declarations including generated declarations. The audit prints
module, full type, opaque-inclusive body, unsafe/partial/axiom flags and
transitive axioms. Only propext, Classical.choice and Quot.sound occur. Five
Lean negative controls were rejected and the existing-olean refusal control
passed. All {len(receipts)} replay calls stayed within caps; summed process wall
time was {wall:.2f} seconds and peak sampled private memory was {maxmem:,} bytes.
Full audit: fresh-extracted/logs/strict-AuditR3.log. Receipts:
fresh-extracted/logs/replay.json.

All 32 assigned files were hash-bound before/after and copied with hash identity,
including the required r2 archive hash. One auxiliary canonical-refinement script
was copied and bound when adapted; auxiliary-input.json distinguishes it from
the initial manifest. All inherited Lean files, including Nut, FiniteGrammar
and VerifiedDet, remain byte-identical. Only new modules were added. Failed
local development trials reused log filenames, so some earlier logs were
overwritten; this full-log requirement deviation is recorded in
logs/development-history.md. The final extracted replay logs are complete.

No child agents, git commands, other-lane writes, shared ledger edits, network
requests, browser tabs, external messages or publication were used. No background
jobs remain at handback. No prior-art gate was repeated and no novelty clearance
is claimed. Source-only packet: nut-r3b-source.zip; replay: REPRODUCE.md;
statement mapping: statement-correspondence.md. Root alone adjudicates acceptance.
''')
files=[p for p in (r/'formal').glob('*.lean') if p.name != 'Audit.lean']+[p for p in (r/'scripts').glob('*.py') if p.name not in ['check.py','finalize.py']]+[r/x for x in ['replay.py','modules.json','graph-extensions.json','graph-modules.json','closure-modules.json','certificate-modules.json','inputs/nut-formal-r2/all-normalized-certificates.json','SUMMARY.md','GAPS.md','REPRODUCE.md','results.json','statement-correspondence.md','inputs-before.json','inputs-after.json','auxiliary-input.json']]
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(r/'packet-manifest.json').write_text(json.dumps({'files':manifest,'proof_sources_match_fresh_replay':True,'source_only':True},indent=2)+'\n')
files.append(r/'packet-manifest.json')
with zipfile.ZipFile(r/'nut-r3b-source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,p.relative_to(r))
sha=hashlib.sha256((r/'nut-r3b-source.zip').read_bytes()).hexdigest()
(r/'nut-r3b-source.zip.sha256').write_text(sha+'  nut-r3b-source.zip\n')
print(json.dumps({'audit_declarations':count,'replay_calls':len(receipts),'wall_seconds':wall,'peak_private_bytes':maxmem,'packet_sha256':sha}))

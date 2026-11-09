from pathlib import Path
import json,hashlib,zipfile,difflib,re
L=Path('source'); old=zipfile.ZipFile('frozen-input.zip')
def sha(b): return hashlib.sha256(b).hexdigest()
def writej(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
# Exact documentary copies only; no executable or generated Lean outputs copied.
review=Path('../sol-polyomino57-full-final-review-r1'); root=Path('../root-polyomino57-final-review-freeze-r1')
items=[(review,n) for n in ['review.md','provenance.json','fresh-audit.json','FINAL-REVIEW-RESULT.json','failures.json','before.json','after.json','exact-results.json','exact-results-packed.json','http.json','registry-results.json','r3-current-delta.json','cached-primary-history.json','fresh-replay/REPLAY-RECEIPT.json','fresh-replay/declaration-inventory.json','fresh-replay/extracted/logs/FinalAudit.log']]
items += [(root,n) for n in ['ROOT-REPLAY-RECEIPT.json','ROOT-REPLAY-COMPARISON.json','root-fresh-replay/declaration-inventory.json','root-fresh-replay/extracted/logs/FinalAudit.log']]
items += [(Path('../root-polyomino57-acceptance-r1'),'REVIEW-ADOPTION.json')]
evidence=[]
for base,n in items:
 p=L/'evidence'/base.name/n;p.parent.mkdir(parents=True,exist_ok=True);b=(base/n).read_bytes();p.write_bytes(b)
 evidence.append(dict(origin=str((base/n).resolve()),packet_path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
p=L/'paper.txt';t=p.read_text();repls={
'Research candidate | 29 October 2026 | integrated final review pending':'Research candidate | 29 October 2026 | proof replay and final review completed',
"The frozen worker replay passed; root verified source hashes and audit records but had not replayed this completed component at adoption. This lane's own fresh extracted strict replay passed all 2023 compilation stages and audited all 5924 declarations. Its receipt and full audit log are in replay-evidence/. The actual records match the frozen inventory, including types and origins. The inherited receipt remains separately labeled. Independent integrated final review and root's acceptance replay remain separate gates.":"The original manuscript worker replay, root's full extracted replay and independent final review replay have passed: 2022 mathematical modules plus FinalAudit and all 5924 actual records. Their receipts and audits are in replay-evidence/ and evidence/. All records have identical types, origins, axioms and flags. This status-only edition ran no new full replay; identity of all 2023 source hashes binds it to those completed replays. Root acceptance is tracked separately.",
'Root explicitly retained eligibility for final review, not acceptance:':'Root retained one-family eligibility subject to the final packet, with acceptance tracked separately:',
'This is a candidate manuscript and final-review packet. Credit remains zero; campaign counts are 5/30 additional and 35/60 total. Root owns acceptance. No optimality, least failure, general-n construction, asymptotic bound or performance claim follows.':'Proof replay and independent final review are completed. Novelty remains bounded by the documented searches and access gaps; the substantive dissent remains standing. Root owns acceptance, tracked separately. No optimality, least failure, general-n construction, asymptotic bound or performance claim follows.',
"This lane's first version probe failed":"The original manuscript lane's first version probe failed",
"Root's final independent reviewer and final acceptance replay are still required. Neither successful packaging nor this lane's replay substitutes for that decision.":"Root and independent final replays and the integrated final review are complete. The reviewer disclosed uncapped small metadata/text helpers; this prevents an unqualified all-protocol PASS. This edition adds no full replay and preserves those failures. Root's final packet inspection and acceptance decision remain separate."
}
for a,b in repls.items(): assert t.count(a)==1,a;t=t.replace(a,b)
p.write_text(t)
p=L/'build_pdf.py';t=p.read_text();assert t.count('candidate for independent final review')==1;p.write_text(t.replace('candidate for independent final review','proof replay and final review completed'))
p=L/'README.md';t=p.read_text();a=t.index('Credit 0.');b=t.index('\n\nRead paper.pdf',a);t=t[:a]+"Credit 0; no acceptance transaction. Campaign counts remain root-owned (6/30 additional, 36/60 total at handoff). Root full replay and independent integrated final review are complete. Root retains one-family eligibility subject to this final packet; the original substantive EXCLUDE dissent remains standing. Author-code404, fresh-history gaps and bounded prior-art coverage remain. Historical uncapped metadata helpers prevent an all-protocol PASS."+t[b:]
t=t.replace("This lane's complete fresh extracted replay passed; its evidence is in replay-evidence/.","The original manuscript lane's complete fresh extracted replay passed; its evidence is in replay-evidence/. The root and independent reviewer also completed fresh replays; exact receipts, inventories and audits are in evidence/. This edition ran no new full replay: all 2023 source hashes and 5924 records are identical.")
t=t.replace('Full final independent review and root acceptance replay are outstanding.','Final independent review and root replay are complete; root packet inspection, current registry delta reconciliation and acceptance remain separate.')
t=t.replace('polyomino57-final-review.zip','polyomino57-final-edition.zip');p.write_text(t)
p=L/'PROVENANCE.json';v=json.loads(p.read_text());v.update(independent_integrated_review='Completed; mathematical/formal/artifact PASS; borderline eligibility; standing dissent and procedural qualifications retained',root_acceptance_replay='Completed; ROOT-REPLAY-RECEIPT and COMPARISON in evidence; acceptance transaction separate',additional=6,total=36,substantive='Root retains one-family eligibility subject to final packet; original EXCLUDE dissent standing; no acceptance',final_edition_input_archive_sha256=sha(Path('frozen-input.zip').read_bytes()),final_edition_new_full_replay=False,final_edition_evidence=evidence);writej(p,v)
# Inherited procedural notes remain literally unchanged. New failures separately documented.
(L/'FINAL-EDITION-NOTES.md').write_text('''# Final edition scope and qualifications

This edition makes only status, provenance, footer and artifact-metadata changes. No proof source, mathematical paragraph, theorem display or authorship is changed. No new full Lean replay was run. Exact 2023-source identity and all 5924 actual record identities bind this edition to the completed root and independent replays. The sole compiler helper exception remains unsafe=false partial=true axiom=false for Polyomino57.attachCheck._unsafe_rec.

Original FAILURE-NOTES.md, inherited notes, all prior evidence and the standing EXCLUDE dissent remain byte-identical. The reviewer disclosed uncapped small metadata/text helpers. Historical cache writes and protocol failures are not erased by this edition. No unqualified protocol perfection or worldwide novelty is asserted.

The PDF skill marker failed under AS512MiB (Node segmented table reservation, exit133); an attempted lower-memory option was unsupported (exit9); jitless also failed (exit133). Caps were not increased and no successful marker is claimed. User resource constraints take precedence over the skill's marker prerequisite. Full local resource receipts are external to the source packet; sampling at45ms does not exclude shorter transients. An initial exec request used an as-yet nonexistent cwd and did not run; it was retried after creating the assigned lane. No external contact, git, browser, acceptance or count transaction occurred.
''')
# Metadata-only verifier extension: final root/reviewer evidence, identical full records and source binding.
p=L/'verify_packet.py';t=p.read_text();needle="pdfhash=sha(E/'paper.pdf')";assert t.count(needle)==1
extra='''# Final edition exact evidence binding; no new Lean run is implied.
evidence=json.loads((E/'PROVENANCE.json').read_text())['final_edition_evidence']
for v in evidence:
 p=E/v['packet_path'];assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes']
for lane,receipt_name,inventory_name in [
 ('root-polyomino57-final-review-freeze-r1','ROOT-REPLAY-RECEIPT.json','root-fresh-replay/declaration-inventory.json'),
 ('sol-polyomino57-full-final-review-r1','fresh-replay/REPLAY-RECEIPT.json','fresh-replay/declaration-inventory.json')]:
 d=E/'evidence'/lane;r=json.loads((d/receipt_name).read_text())
 assert r['status']=='PASS' and r['modules']==2022 and r['declarations']==5924
 assert r['source_manifest_sha256']==sha(E/'source-manifest.json')
 assert sha(d/inventory_name)=='bb24a892d49115ba1538de2994a2452088cad156d091ed69fa960f09cb50e4c9'
 assert json.loads((d/inventory_name).read_text())==inv
 log=d/('root-fresh-replay/extracted/logs/FinalAudit.log' if lane.startswith('root-') else 'fresh-replay/extracted/logs/FinalAudit.log')
 b=re.findall(r'AUDIT (\\S+) (\\S+)\\nTYPE (.*?)\\nAXIOMS (.*?)\\nFLAGS ([^\\n]+)',log.read_text(),re.S)
 assert [dict(origin=o,name=n,type=t,axioms=a,flags=f) for o,n,t,a,f in b]==inv
'''
p.write_text(t.replace(needle,extra+needle))
# Exact change report against immutable archive, excluding later generated PDF/QA/manifest.
changes=[]
for n in old.namelist():
 b=(L/n).read_bytes()
 if b!=old.read(n):
  changes.append(n)
  if n.endswith(('.txt','.md','.py','.json')):
   Path('edit-report.diff').open('a').write(''.join(difflib.unified_diff(old.read(n).decode().splitlines(True),b.decode().splitlines(True),fromfile='frozen/'+n,tofile='final/'+n)))
writej(Path('prebuild-edit-report.json'),dict(changed=changes,added=[str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in old.namelist()],evidence=evidence))
print('Prepared',changes,'evidence files',len(evidence))

import resource,signal,json,datetime,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
p=Path('review.md');s=p.read_text();s=s.replace('**Provisional while my fresh Lean replay runs. No acceptance or credit.** This document will receive the actual fresh replay result before handoff.','**FINAL: mathematical/source/formal/artifact gates PASS with the stated source/prior limits; substantive eligibility borderline; literal all-helper resource protocol NOT fully satisfied. No acceptance or credit.**')
s=s.replace('## Lean and trust gate — PENDING my complete fresh replay','## Lean and trust gate — PASS on my complete fresh replay')
s=s.replace('The eventual fresh audit must agree on every actual type/origin/transitive-axiom/flag record, not just the name set or a printed total.','My fresh audit agrees on every actual type/origin/transitive-axiom/flag record, not just the name set or a printed total.')
s=s.replace('The actual final types must be','The actual final types are')
s=s.replace('The saved earlier history observations remain inherited:', 'I also copied and read the actual cached primary history bodies as cached-primary-history.json; these are historical retrievals, not fresh access:')
s=s.replace('Python computational scripts install AS512MiB/CPU210/wall230, BLAS/OMP1.','The substantive Python computational scripts install AS512MiB/CPU210/wall230, BLAS/OMP1.')
needle='## Manuscript and deterministic artifact gates — PASS'
a=json.loads(Path('fresh-audit.json').read_text())
add='''### Fresh result and complete actual audit

Own fresh replay completed all2023 compilation stages plus its version probe, with2022 empty mathematical logs. The independent `fresh_audit.py` reparsed the new FinalAudit log and compared every field of every5924 unique record to both the fresh JSON and the frozen inventory. All match. It rechecked the exact AllCases dependency closure, all2023 extracted source hashes, all five closed endpoint types, every actual origin, all axiom sets and every safety flag. The only partial exception remains the specified attachCheck compiler artifact; there are no new exceptions.

Evidence is **fresh-replay/REPLAY-RECEIPT.json**, **fresh-replay/declaration-inventory.json**, **fresh-replay/extracted/logs/FinalAudit.log**, and **fresh-audit.json**. The top-level copied REPLAY-RECEIPT.json is a frozen input receipt, not my replay. My receipt SHA256 is `321894adeab9a81b8121e7adde4117eee33efe79b0d14c8fd27c4a5dba71178a`; new actual-record inventory SHA256 is `bb24a892d49115ba1538de2994a2452088cad156d091ed69fa960f09cb50e4c9`. Maximum sampled groupRSS was2,910,035,968bytes (2775.2265625MiB), below2800MiB; maximum stage wall35.109seconds; summed stage time3036.119seconds. There were no failed Lean stages, threshold increases or inherited root results. 45ms sampling does not certify absence of shorter transients.

`before.json` and `after.json` anchor the archive and copied immutable receipts before/after review. The final check also compares all2023 source hashes to the root's frozen extracted input, without reading its live replay output. All remain identical. My first postcheck failed closed because Path('.').parent resolved the sibling freeze path incorrectly; I corrected only my helper and reran it successfully. This was not an input-byte discrepancy.

'''
s=s.replace(needle,add+needle)
s+='''
## Final gate disposition and handoff

| Gate | Independent verdict |
| --- | --- |
| Literal source/minimum/orientation/holes | PASS, with fresh-history and author-code access gaps |
| Ordinary proof and all70 finite cases | PASS |
| Fresh strict Lean closure and actual5924-record audit | PASS |
| Seven-page manuscript/read evidence | PASS; known status-only5/35→6/36 correction deferred |
| Byte-identical PDF/ZIP and frozen sources | PASS |
| Bounded current prior/subsumption screen | PASS as documented no-known-match evidence, no absence guarantee |
| Substantive scope | Borderline ELIGIBLE for one full refutation; r3 EXCLUDE dissent preserved |
| Literal every-helper resource protocol | NOT fully satisfied: small metadata/text snippets lacked explicit caps |

No unqualified all-gates/procedural PASS is claimed. The complete mathematical counterexample and its fresh certificate are validated; the significance judgment and disclosed procedural deviation remain for root to adjudicate. Strongest unresolved objections are unavailable author data/history, bounded specialist coverage, and the narrow finite nature of the contribution. This review changes no acceptance, ledger or count.
'''
p.write_text(s)
fails=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lean_failures=[],own_failures=[dict(stage='exact checker first development run',reason='forced-cell kind was initially recognized only as forced; failed closed on absent Forced730Data',evidence='exact-checks-first-failure.log'),dict(stage='exact checker second development run',reason='SmallCase uses an unpacked Fin4 mask table rather than rowOf; failed closed',evidence='exact-checks-second-failure.log'),dict(stage='final byte comparison first attempt',reason="Path('.').parent gave wrong sibling path; FileNotFoundError; fixed helper only; final after.json PASS"),dict(stage='read-only exploration',reason='Tried unshipped refresh.py and nonexistent formal/run.py; actual run.py is at packet root; no mutation')],protocol_deviation='Initial fixed-input copy/extraction/hash and several metadata/read/text-edit Python snippets did not each install explicit helper resource limits. All substantive computation and all Lean child stages capped; not an assertion of literal every-helper conformance.',inherited_failure_notes=['extracted/FAILURE-NOTES.md','extracted/local-failures.json','extracted/inherited/FAILURE-NOTES.md'])
Path('failures.json').write_text(json.dumps(fails,indent=2)+'\n')
# Anchor inherited primary-history copy against the original without modifying it.
hist=Path('cached-primary-history.json');original=Path('../sol-polyomino57-preliminary-review-r1/web-primary-history.json');assert hist.read_bytes()==original.read_bytes()
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),credit=0,root_acceptance=False,mathematical_verdict='PASS',formal_verdict='PASS',artifact_verdict='PASS',substantive_verdict='borderline ELIGIBLE; independent dissent retained',resource_protocol_verdict='NOT fully satisfied for small metadata/text snippets; substantive and Lean stages capped',fresh_audit=a,source_limits=['author-code404','fresh-history inaccessible','bounded prior-art search'],counts=[6,36])
Path('FINAL-REVIEW-RESULT.json').write_text(json.dumps(r,indent=2)+'\n')

from retrieve import *
import xml.etree.ElementTree as E
# Administrative interpretation is a dated snapshot, not a scientific immutability claim.
admin={}
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/n).read_text())
 admin[n]={k:([{z:x.get(z) for z in ['number','title','status','source_target','scope']} for x in v] if isinstance(v,list) and all(isinstance(x,dict) for x in v) else v) for k,v in d.items()}
(L/'administrative-reading.json').write_text(json.dumps(admin,indent=2))
refs=json.loads((L/'history-freeze.json').read_text());hits=[]
for r in refs:
 p=pathlib.Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 s=p.read_text(errors='replace')
 for term in ['Ramm','0603631','Gasull','2012.02524','Niculescu','Prajitura','Bownik','Rzeszotnik','Foss','Khoshnevisan','Kolountzakis','gated','rigid cubic']:
  for line in s.splitlines():
   if term.lower() in line.lower():hits.append({'path':str(p),'term':term,'excerpt':line[:1500]})
(L/'history-supplement.json').write_text(json.dumps(hits,indent=2));print('supplement hits',len(hits));print(json.dumps(hits)[:5000])
ids='1905.08230,2012.02524,2009.09410,math/0603631,1408.0142,math/0510518,0909.0462,1611.01905,1201.5156,1905.01736,1802.08400'
data=fetch('https://export.arxiv.org/api/query?id_list='+ids,'versions.xml')
ns={'a':'http://www.w3.org/2005/Atom'}
chron=[]
if data:
 for e in E.fromstring(data).findall('a:entry',ns):
  chron.append({'id':e.findtext('a:id',namespaces=ns),'title':e.findtext('a:title',namespaces=ns),'published':e.findtext('a:published',namespaces=ns),'updated':e.findtext('a:updated',namespaces=ns),'authors':[x.findtext('a:name',namespaces=ns) for x in e.findall('a:author',ns)]})
(L/'chronology.json').write_text(json.dumps(chron,indent=2))
source=[]
for line in (L/'sourcebytes.jsonl').read_text().splitlines():
 r=json.loads(line);assert hashlib.sha256(pathlib.Path(r['path']).read_bytes()).hexdigest()==r['sha256'];source.append(r)
(L/'provenance.json').write_text(json.dumps({'research_date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':source,'administrative':'snapshot only','history':'direct hash references, no recursive copies','registry':'No current public proof-registry head obtained. Forbidden routes parked. NO novelty clearance.','r223_limit':'r223 direct report not separately copied/read; r224/r225 summaries describe its screened exclusions. Bounded history screening is not exhaustive.','resource_caps':{'AS':536870912,'groupRSS':536870912,'CPU_seconds':210,'wall_seconds':230},'scope':'all writes assigned lane, no shared/git/public/browser/MathDB/Lean/manuscript/children/count changes'},indent=2))
(L/'SUMMARY.md').write_text('''# r227 handback

Ten distinct attributed unresolved-at-source/provisionally open analytic, probabilistic and geometric families were screened across 2005–2021. These are not ten certified currently open problems. SCOUTING.md states exact quantified scopes, versioned URLs, nearest bodies actually available, mechanisms and access limits. Current public proof-registry heads and citation completeness remain uncleared.

Two provisional survivors ranked: the Bownik–Weber annular wavelet interval (via Bownik–Rzeszotnik2019 Problem2.7), then Gasull2020 Problem9 on positive singular periodic ODE solutions. No third padded lead. ATTACK.md sustains a full Fourier-energy/coercivity route and an opposite-phase cancellation route for the wavelet target. The Bessel bound is proved; the universal lower-bound/classification step remains open in this lane. Rational orbit checks are finite evidence only.

PROOF.md gives two complete routes to Simic's literal smooth-convex sharp constant1/4 and an exact sparse-block refutation of Niculescu–Prajitura's weighted-density implication. Both are held as elementary routine constructions, with the complete classical bridges and strongest eligibility objections stated. Neither is nominated or counted. A same-author MMPP public-resolution claim was caught; its stated proof PDF404 is preserved and not retried.

No complete eligible discovery is proposed. Root alone accepts/counts:9 additional/39 total/next40 unchanged. No shared/git/public/browser/MathDB/Lean/manuscript edits and no children. Manifest excludes itself and the verification receipt; the verifier is run separately under the fixed helper guard after all other writes.
''')
(L/'discovery.md').write_text('''# Disposition

No acceptance recommendation and no discovery credit. Two source-endpoint calculations are complete ordinary arguments but held as routine, not new discoveries. The strongest fresh provisional survivor remains mathematically incomplete at the exact lower frame bound. Its missing universal measurable inequality and alternative counterexample criterion are explicit in ATTACK.md. Current prior-art clearance and original adjacent-range proof-body retrieval remain material prerequisites.
''')
(L/'progress.md').write_text('''# Progress

Frozen compact coordination reports and administrative snapshots; screened author/object aliases before target investment, with supplemental aliases after Ramm/Gasull retrieval. Retrieved versioned primary bodies once and bound extraction bytes before reading. Read source questions and bounded actual proof contexts, keeping inaccessible older originals explicit. Developed exact wavelet coefficient formula and two routes; preserved unsuccessful cancellation balls. Completed sharp-constant and sparse-density calculations, then rejected their nomination as routine. Wrote compact source/chronology/history receipts. Final source and manifest verification is a separate guarded invocation; only its receipt states pass/fail.
''')
(L/'FAILURES.md').write_text('''# Preserved failures and limitations

- failures.jsonl preserves the exact1802.08400v3 PDF404. No retry, HEAD loop, browser, mirror/proxy/TLS workaround or public-resolution body claim.
- Initial API output and multi-body excerpt output were too large and truncated in tool output. Later bounded reads targeted actual source statements. Whole-paper reading is not claimed. Raw files remain bound.
- Narrow live wavelet/polling queries have poor recall, including an irrelevant quantum-gate paper. Empty/noisy search is not a prior-art certificate.
- No current GitHub/public proof-registry head was retrieved; previously denied API/raw/codeload/diff/patch routes were not attempted. ScienceDirect and Google challenge routes were not attempted.
- r223 was covered indirectly through compact r224/r225 coordination and the direct SCOUTING history screen, not a standalone complete r223 audit.
- Wavelet rational graph balls do not produce vanishing boundary quotient; this is failure of one trial family, not a proof of a lower bound or refutation of a stronger helper. No L2 witness has been produced.
- Original2003 frame proof, older Ramm references, Gasull cited p=5/3 construction and broad specialist citation histories remain unread. No assumptions are supplied from those unread bodies.
- First finalize.py failed its original-before/after assertion because active r226 changed. failures.jsonl and original-recheck.json preserve that event and both hashes. Initial copies remain unchanged; current originals are checked against separately recorded later hashes. No independent adversarial review, formal certificate, manuscript, priority guarantee or discovery acceptance exists for this lane.
''')
(L/'RUN.md').write_text('''# Bounded replay

From this lane, run the following commands. Every Python/helper/retrieval/hash/edit operation uses the specified external guard; no cap increase. Network retrieval is optional and should not be repeated on parked failures.

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python checks.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py
```

checks.py uses rational arithmetic only, no external packages. It checks finite graph identities and exact polynomial quadrature values. Its assertions do not certify the universal wavelet source question or worldwide novelty. verify.py independently checks source/history bindings and final manifest, then writes only verification-receipt.json. Re-running checks.py deterministically reproduces its manifested output.
''')
# Freeze all remaining derived scientific extraction bytes too, before final rereading.
derived=[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in (L/'primary').glob('*.txt')]
(L/'all-text-bindings.json').write_text(json.dumps(derived,indent=2))
# Verify original/copy bindings after research, no scientific modification.
for r in json.loads((L/'freeze.json').read_text())['refs']:
 assert r['sha256']==hashlib.sha256(pathlib.Path(r['copy']).read_bytes()).hexdigest()
for r in json.loads((L/'original-recheck.json').read_text()):
 assert hashlib.sha256(pathlib.Path(r['path']).read_bytes()).hexdigest()==r['sha256']
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2))
print('manifest files',len(manifest))

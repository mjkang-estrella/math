from pathlib import Path
import json,re,hashlib,datetime
L=Path(__file__).resolve().parents[1]
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert 'ALL_PASS' in (L/'logs/replay.log').read_text()
mods=(L/'evidence/order.txt').read_text().splitlines();assert len(mods)==54
rows=[]
for m in mods:
 vals=[]
 for phase in ('build','check'):
  s=(L/f'logs/{phase}-{m}.log').read_text();matches=re.findall(r'elapsed=([\d.]+) max_rss_kib=(\d+) exit=(\d+)',s)
  assert len(matches)==1 and matches[0][2]=='0',(m,phase,s[-500:]);assert 'RSS_WATCHDOG' not in s
  tm,rss,rc=matches[0];vals.extend([float(tm),int(rss)])
 rows.append({'module':m,'lean_seconds':vals[0],'lean_rss_kib':vals[1],'checker_seconds':vals[2],'checker_rss_kib':vals[3]})
audit=(L/'logs/independent-audit.log').read_text();assert 'Independent local metadata audit PASS' in audit and 'exit=0' in audit
for endpoint in ('even_case','mathdb_354228'):
 a=re.search(r"'Antimagic.Round7A\."+endpoint+r"' depends on axioms: \[([^]]*)\]",audit)
 assert a,endpoint
 assert set(a[1].split(', '))=={'propext','Classical.choice','Quot.sound'},a[1]
assert 'exit=0' in (L/'logs/independent-check.log').read_text()
before={}
for name in ('input-before.json','additional-input-before.json'):
 before.update(json.loads((L/'evidence'/name).read_text()))
chain=json.loads((L/'evidence/hash-chain.json').read_text());before.update(chain['input_hashes'])
after={p:hashfile(Path(p)) for p in before};assert before==after
(L/'evidence/input-after.json').write_text(json.dumps(after,indent=2))
(L/'evidence/input-before-combined.json').write_text(json.dumps(before,indent=2))
assert not any(json.loads((L/'evidence/source-scan.json').read_text()).values())
spot=json.loads((L/'evidence/spotcheck.json').read_text())
table='| Module | Lean s | Lean RSS KiB | Checker s | Checker RSS KiB |\n|---|---:|---:|---:|---:|\n'+''.join(f"| {r['module']} | {r['lean_seconds']:.2f} | {r['lean_rss_kib']} | {r['checker_seconds']:.2f} | {r['checker_rss_kib']} |\n" for r in rows)
(L/'evidence/module-timing-rss.md').write_text(table)
(L/'evidence/module-timing-rss.json').write_text(json.dumps(rows,indent=2))
downloads={str(p.relative_to(L)):hashfile(p) for p in sorted((L/'downloads').rglob('*')) if p.is_file()}
(L/'evidence/download-hashes.json').write_text(json.dumps(downloads,indent=2))
gates={'A':{'verdict':'PASS','reason':'Literal graph definitions, nonempty least spectrum, source structural certificate and arbitrary-tree isomorphism bridge meet ruling (i)-(iv). Totalized graph definitions cause no endpoint domain mismatch.'},'B':{'verdict':'PASS','reason':'Corrected fresh extraction: all 54 strict module builds and all 54 explicit-module leanchecker calls pass. Independent metadata audit and both endpoint axiom reports pass. Preliminary run excluded.'},'C':{'verdict':'PASS','reason':'Exact frozen construction predicates are fully discharged; before/after manifests and earlier archive source bytes agree with final extracted modules.'},'D':{'verdict':'PASS','reason':f"Independent frozen-formula transcription passes {len(spot['cases'])} parameter cases, including all 15 required cases; negative controls detected."},'E':{'verdict':'QUALIFIED_PASS','reason':'No resolution found in bounded arXiv abs / OpenAlex refresh; listing failures and two unread closed-access leads remain. Attribution in final packet is correct.'}}
result={'mathdb_id':354228,'role':'INDEPENDENT FORMAL-FIDELITY AND FINAL REVIEW, NOT acceptance','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archive_sha256':hashfile(L.parent/'antimagic-formal-r7a/source.zip'),'gates':gates,'overall':'PROCEED TO ACCEPTANCE PACKAGING','accepted':False,'credit':0,'root_decides':True,'replay':{'modules':54,'strict_builds':54,'explicit_module_checker_calls':54,'driver':'scripts/replay.sh','resource_wrapper':'scripts/capped.sh','metadata_audit':'ReviewAudit.lean','axioms':['propext','Classical.choice','Quot.sound'],'local_declarations':len((L/'evidence/local-metadata.tsv').read_text().splitlines()),'timings':'evidence/module-timing-rss.json','preliminary_run_excluded':True},'numerical':spot,'input_hashes_unchanged':True,'limitations':['Initial wrapper missed timeout child process group; initial run excluded and fully repeated with corrected wrapper.','Expanded-corpus source copies are HTML/text, not PDF; published PDF checked from prior-review read-only cache.','arXiv listing requests failed (400/404).','Sarath-Prajeesh body unavailable (empty 202); Premalatha et al. body unavailable (403, no retry).','No exhaustive prior-art or novelty certification.'],'evidence':['evidence/input-before-combined.json','evidence/input-after.json','evidence/hash-chain.json','evidence/mathdb-354228.raw.jsonl','evidence/source-before.sha256','evidence/download-hashes.json','evidence/source-scan.json','evidence/local-metadata.tsv','logs/replay.log','logs/independent-audit.log']}
(L/'review.json').write_text(json.dumps(result,indent=2)+'\n')
text='''# Independent formal-fidelity and final review: MathDB 354228

**Recommendation: PROCEED TO ACCEPTANCE PACKAGING. This is a review, not acceptance; credit remains 0 and root decides.**

Reviewed archive: `../antimagic-formal-r7a/source.zip`, SHA-256 `987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175`. Review performed independently, with no children, git operations, external messages, publication, uploads or browser tabs. All new files are in this lane. The other lanes and pinned toolchain/packages were read-only.

| Gate | Verdict | Finding |
|---|---|---|
'''+''.join(f"| {k} | {v['verdict']} | {v['reason']} |\n" for k,v in gates.items())+'''
## A. Fidelity and C. architecture

'''+(L/'evidence/fidelity-notes.md').read_text()+'''
## B. Independent replay and process discipline

The driver is my own `scripts/replay.sh`, with dependency order computed by `scripts/prepare.py`; no formalization-lane driver was executed. `scripts/extract.py` checks the exact archive hash, absolute/parent/backslash paths, file types/links, file sizes and absence of bundled olean/ilean/shared libraries before extracting into a new empty directory. Each local module is compiled separately with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`, followed by `leanchecker <explicit module>`. Mathlib's read-only `.git/HEAD` was inspected without git: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

A wrapper defect was discovered in the preliminary run: GNU timeout created its own process group, so the monitor could miss the heavy child. That run was stopped and preserved under `preliminary/`, and is excluded from validation. The extraction, order preparation and complete replay were repeated with corrected `timeout --foreground`. Every process in the qualifying run used the same caps: taskset CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, aggregate process-group RSS watchdog 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR/cache. No limit was raised. `evidence/corrected-process-groups.txt` records the corrected grouping. The preliminary mistake is disclosed rather than claimed compliant retroactively.

All 54 builds and 54 checkers passed in the qualifying run; complete output is in `logs/build-*.log`, `logs/check-*.log` and `logs/replay.log`. Both final endpoints report exactly propext, Classical.choice and Quot.sound. My separate `ReviewAudit.lean` enumerates all imported Antimagic-module and Antimagic-named constants, rejecting unsafe, partial, implemented_by, extern, added axioms and _unsafe_rec metadata. The source scanner independently excludes nested comments and strings before searching sorry, admit, axiom, native_decide, ofReduceBool and implemented_by. Results are in `evidence/local-metadata.tsv`, `evidence/source-scan.json` and `logs/independent-audit.log`. The audit module itself was strictly compiled and explicitly checked. Imported frozen audit modules additionally perform dependency-closure audits; their claims were not substituted for the independent local metadata check.

'''+f"Local metadata declarations checked: {result['replay']['local_declarations']}. Peak per-process RSS over module builds/checkers: {max(max(r['lean_rss_kib'],r['checker_rss_kib']) for r in rows)} KiB.\n"+'''
The before/after input maps include the archive, all extracted Lean modules, source/corpus/ruling inputs, recorded inheritance manifests and earlier archives/results; all agree. `evidence/hash-chain.json` records exact checked paths and module counts, independently comparing earlier zip member bytes and lane files against the final extraction. The MathDB literal is corpus chunk 0008, exact line 3529, copied including its newline to `evidence/mathdb-354228.raw.jsonl`; its raw-line hash and full chunk hash are recorded, not reconstructed from JSON.

## D. Independent numerical spot-check

My `scripts/spotcheck.py` is a new direct transcription of AntimagicLabel.lean, including truncated natural subtraction, all depth-two branches, sigma and the binary row-two patch. It explicitly constructs graph edges and accumulates weights/degrees. It checks the entire label interval, every adjacent pair, leaf count and exact number of colors. It imports or executes no earlier checker. Run capped with python3 -I; `logs/spotcheck.log` and `evidence/spotcheck.json` preserve results.

'''+f"All {len(spot['cases'])} cases pass. Depth ranges: "+', '.join(f"t={t}: n=1..{max(r['n'] for r in spot['cases'] if r['t']==t)}" for t in (2,4,6))+'''. This includes every required t in {2,4,6}, n in {1,2,3,4,5}. Larger cases stay below 500,000 edges. Removing the binary patch fails properness at (2,3); duplicating a label fails bijectivity at (4,3). These diagnostics support the review and are not used as a proof.

## E. Prior art and attribution

'''+(L/'evidence/prior-art-notes.md').read_text()+'''
## Per-module timings and peak RSS

RSS is /usr/bin/time maximum resident set in KiB for each process invocation; the independent watchdog enforces the aggregate process-group limit. Times include the capped command. Full machine-readable rows are in `evidence/module-timing-rss.json`.

'''+table+'''
## Handoff

No mathematical or formal fix is required by gates A-D. Package the final unconditional Round7A endpoints and retain corrected published attribution, all replay evidence and gate E's limitations. Do not advertise the bounded search as a proof of novelty. Root alone decides acceptance and any credit.
'''
(L/'REVIEW.md').write_text(text)
print(json.dumps({'overall':result['overall'],'gates':{k:v['verdict'] for k,v in gates.items()},'modules':len(rows),'cases':len(spot['cases'])}))

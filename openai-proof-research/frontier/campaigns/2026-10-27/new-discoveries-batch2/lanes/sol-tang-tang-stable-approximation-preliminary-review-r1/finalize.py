from pathlib import Path
import hashlib,json,datetime,shutil
D=Path(__file__).resolve().parent
B=D.parent.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,obj): (D/name).write_text(json.dumps(obj,indent=2)+'\n')
# Administrative snapshots only, never require a mutable ledger to remain unchanged.
for p,name in [(B/'AGENTS.md','batch-AGENTS.md'),(B.parents[3]/'AGENTS.md','ancestor-AGENTS.md')]:
    shutil.copyfile(p,D/'administrative'/name)
variants=[]
for label,old in [('tang','1908.10024v1'),('glp','1607.03036v1')]:
    for ext in ['pdf','txt']:
        f=D/'frozen'/(old+'.'+ext);g=D/'live'/(label+'-current.'+ext)
        variants.append({'inherited':str(f.relative_to(D)),'current':str(g.relative_to(D)),'inherited_sha256':H(f),'current_sha256':H(g),'byte_identical':H(f)==H(g)})
write('variant-comparison.json',variants)
pub=json.loads((D/'published-access.json').read_text())
pub.update(scientific_body=False,challenge='HTTP200 Incapsula Request unsuccessful; STOP publisher route, no iframe/script/PDF followup')
write('published-access.json',pub)
access=json.loads((D/'access.json').read_text())+json.loads((D/'additional-access.json').read_text())+[pub]
frozen=json.loads((D/'frozen-inputs.json').read_text())
for r in frozen['inputs']:assert H(Path(r['original']))==H(Path(r['copy']))==r['sha256']
write('provenance.json',{'review_date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'assigned_lane':str(D),'source_freeze':frozen,'live_access':access,'administrative_snapshots':[{'path':str(p.relative_to(D)),'sha256':H(p),'bytes':p.stat().st_size} for p in sorted((D/'administrative').iterdir())],'frozen_originals_after_reading':'17/17 match','variant_comparison':variants,'current_registry_heads':'NOT obtained; inherited denied routes parked','history':'Immutable inherited history-references.json reused; not retraversed; no absence-as-novelty inference','count_state':{'additional':9,'total':39,'next':40,'edits':False},'guard':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'environment':['OPENBLAS_NUM_THREADS=1','OMP_NUM_THREADS=1','PYTHONDONTWRITEBYTECODE=1']}})
(D/'FAILURES.md').write_text('''# Preserved failures and limitations

The complete inherited failure log is frozen/FAILURES.md. Its overbroad inventory/truncated extraction outputs, overwritten first history alias file, fixed-block obstruction, inconsistent source labels and n/2n typography, unverified registry heads, and finite-width residual truncation remain preserved; none is repaired into favorable evidence.

This review also initially used an overbroad rg inventory and a broad multi-source extraction, producing truncated output. Bounded rereads of the actual Tang pp10–13 and GLP Section4 supplied the passages used. No conclusion relies on unseen truncated output. One later broad administrative rg was truncated; capped Python fully parsed both snapshots and printed relevant records.

The first administrative copy used the same AGENTS.md basename for batch and ancestor, so the ancestor overwrote that administrative copy. Both were already read directly; finalization separately snapshots batch-AGENTS.md and ancestor-AGENTS.md. Scientific source files were not affected.

The classical Stieltjes/Bernstein book URL https://www.math.tu-dresden.de/sto/schilling/rls-books/bernstein/BNF.pdf timed out after 22 seconds. No body or theorem from it is claimed. No retry.

The journal page returned HTTP200 but only a 1165-byte Incapsula Request unsuccessful incident/challenge. The initial automated keyword classifier omitted Incapsula; bounded manual inspection recognized it immediately. Final access metadata classifies it correctly. No iframe, script, browser, alternate publisher route or bypass was attempted. Published problem wording remains unverified.

Current public proof-registry heads and old inaccessible historical intervals remain parked, not cleared. No forbidden GitHub API/raw/codeload/diff/patch, ScienceDirect or challenged Google route was attempted. No 403/429 retry. No external account, browser, git, shared count/index, Lean, MathDB or manuscript change.

The exact-title Liggett arXiv query had zero entries. This does not prove absence of a manuscript or a proof. Full Liggett2018, complete specialist citers, and exhaustive classical proof bodies are unread. No inference of favorable novelty.
''')
guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(D/'RUN.md').write_text(f'''# Reproduction

All Python, retrieval, extraction subprocesses, writes and hashes ran under the fixed supplied helper, except permitted native bounded reads and apply_patch. No cap raises. Every invocation set OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. Helper fixes AS and sampled process-group RSS at 512MiB, CPU at 210s and wall at 230s. Retrieval used bounded urllib reads and timeouts, no browser.

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python {guard} python {D}/checks.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python {guard} python {D}/finalize.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python {guard} python {D}/verify.py
```

Independent check run: exit0, sampled peak group RSS17174528 bytes, wall0.241s. Initial freeze exit0 /7962624bytes /0.041s. Main live retrieval exit0 /24887296bytes /22.883s (one recorded timeout). PDF extraction/admin parsing exit0 /36720640bytes /0.121s. Crossref/title retrieval exit0 /24031232bytes /0.922s. Publisher denial retrieval exit0 /24174592bytes /0.201s, transport success but scientific access failure. New retrieval URLs, dates, response hashes and status are in access.json, additional-access.json and published-access.json. All retrieved bodies were saved and hashed before scientific inspection. The numerical checks are not proofs of bounded transport width.

Manifest creation is followed by a separate guarded verifier invocation. Its receipt is deliberately excluded from the manifest along with the manifest itself. Re-running checks changes check-results.json and requires finalization and verification again.
''')
files=[p for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']]
write('manifest.json',{'exclusions':['manifest.json','verification-receipt.json'],'files':[{'path':str(p.relative_to(D)),'sha256':H(p),'bytes':p.stat().st_size} for p in files]})
print(json.dumps({'manifest_files':len(files),'frozen_originals_after_reading':len(frozen['inputs']),'variants':variants}))

import pathlib,json,hashlib,datetime,xml.etree.ElementTree as E,shutil
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=L/'SCOUTING.md';p.write_text(p.read_text().replace('Imchit–Saejung','Pongsriiam–Termwuttipong'))
shutil.copyfile(L.parents[5]/'AGENTS.md',L/'administrative'/'ancestor-AGENTS.md') if (L.parents[5]/'AGENTS.md').exists() else None
ns={'a':'http://www.w3.org/2005/Atom'};chron=[]
for x in E.parse(L/'frozen/chronology.xml').findall('a:entry',ns):
 chron.append({k:x.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
(L/'chronology.json').write_text(json.dumps(chron,indent=2))
rows=[]
for p in sorted((L/'primary').rglob('*.pdf')):
 q=L/'frozen'/p.name;assert h(p)==h(q)
 text=L/'frozen'/(p.name+'.txt');assert text.exists()
 rows.append({'original':str(p.relative_to(L)),'copy':str(q.relative_to(L)),'sha256':h(p),'text':str(text.relative_to(L)),'text_sha256':h(text),'url':'https://arxiv.org/pdf/'+(('math/' if p.name.startswith('0606194') else '')+p.stem)})
(L/'source-map.json').write_text(json.dumps(rows,indent=2))
# Pinned canonical index: immutable reference, no historical-tree duplication.
p=L.parents[5]/'sources/preprints-tree.json'
# Resolve from known repository path, avoiding dependence on directory-depth guesses.
repo=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
shutil.copyfile(repo/'AGENTS.md',L/'administrative/ancestor-AGENTS.md')
p=repo/'sources/preprints-tree.json';before=h(p);data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==before
terms=['Komornik','Loreti','rotative','Vervaat','Foxall','Derrida','1003.1278','discrete Boole']
matches={t:t.lower() in data.decode(errors='replace').lower() for t in terms};assert h(p)==before
(L/'catalogue-screen.json').write_text(json.dumps({'path':str(p),'sha256':before,'matches':matches,'status':'old pinned index only; no current registry clearance'},indent=2))
(L/'SUMMARY.md').write_text('''# r243 handback

No complete new source result. Counts unchanged:9 additional/39 total/next40. Root alone decides acceptance.

SCOUTING.md gives eight distinct broad full-endpoint source-question rows, eleven older target-paper screens and three later primary comparison bodies. This falls short of eight fresh actionable survivors and of original-question-body verification for every historical attribution. Two ranked provisional leads: irregular truncated-cosine Bernstein inequality; discrete Boole converse. The first received two sustained routes, a960-configuration exploratory Gram sweep, and65-digit recalculation of six selected configurations. No counterexample survived. No PROOF.md is warranted.

discovery.md records the uniform Fourier obstruction and the complete classical confluent-limit calculation, without promoting either to the literal all-spacing theorem. Runnable bounded scripts, primary bytes, access logs and hashes are retained. No children, Lean, manuscript, shared edits, git or external mutations. Current proof-registry and worldwide-priority clearance are unavailable; forbidden routes were not retried.
''')
(L/'progress.md').write_text('''# Progress

Completed administrative snapshots; bounded canonical/history aliases; source freeze before scientific inspection; eight broad full-endpoint source-question rows; negative controls; later max-recursion and shift-space comparison bodies; two mathematical Bernstein routes;960 random configurations and65-digit selected recalculation. No universal proof or counterexample. Root count remains9/39/40. Assigned task is not counted as extra.

Next useful work: obtain a spacing-aware factorization/total-positivity theorem for the arbitrary irregular Gram matrix, or an exact negative minor. For discrete Boole, read a modern rational converse before algebraic investment. Other rows are defer/reject, not nominations.
''')
(L/'FAILURES.md').write_text('''# Preserved failures and limits

1. Initial filesystem inventory was overly broad and its output truncated; no scientific conclusions use unseen output. Several exploratory keyword displays were also truncated; selected statements were subsequently read with bounded native ranges.
2. numpy/scipy attempt failed: `OpenBLAS error: Memory allocation still failed after 10 retries, giving up.` Guard exit1, sampled groupRSS69771264, wall0.24054s. It failed before calculations. Fixed512MiB AS/groupRSS, CPU210 and wall230 were not raised. Replaced by standard-library code; current calculate.py is the runnable replacement, not the original failed version.
3. Legacy arXiv math/0606194v3 retrieval succeeded but the frozen/math subdirectory was absent. http.jsonl preserves the copy failure. Original retained, copied locally and hash-verified before any scientific reading; freeze-repair.json records repair. No network retry.
4. Exploratory Simpson/Jacobi small negatives were numerical artifacts in the selected65-digit rechecks; no counterexample or interval certificate. Some floating gaps were minutely belowπ and were explicitly rescaled at65 digits.
5. Cryptographic noise made the discrete-logarithm prior query poor coverage. No negative search result is priority clearance.
6. No GitHub API/raw/codeload/diff/patch, ScienceDirect or Google-challenge route was attempted. No403/429/challenge encountered on permitted arXiv routes. Old denied intervals stay parked. Current registry head, broad citers, subscription databases and original bodies for every historical attribution remain unverified.
7. Interior dates differ from arXiv identifiers in Foxall and Vavasis bodies; API metadata and actual body dates are retained without inventing chronology.
8. No complete ordinary source result, no PROOF file, no acceptance recommendation. General Banach-space, all-p embedding and all-spacing Bernstein endpoints remain open in this packet.
''')
(L/'provenance.md').write_text('''# Provenance

Scientific originals in primary/ and byte-identical frozen/ copies were hashed before extraction/read and compared after. Extraction hashes recorded before reading in extractions.jsonl. A local legacy-path freeze repair preceded reading. The selected recent reports in freeze.json were independently copied once; no recursive archive/history tree was copied. Broader history-screen*.json references were hash-frozen before term inspection and verified immediately after; final verifier checks them again. Administrative files are time-of-task snapshots, not assertions that live shared files stay fixed.

http.jsonl records literal URLs, UTC retrieval times, bytes, response status and SHA256. source-map.json binds actual PDFs/text. chronology.json is primary API metadata; a version suffix does not authenticate its interior date. Upstream pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (8Oct2026) is an old catalogue check, not a current public-registry head. No blocked routes retried and no worldwide novelty claim.

All Python, network retrieval, source copying, hash computation and computational checking ran through the assigned existing helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1, fixed AS/groupRSS512MiB CPU210s wall230s. Native bounded reads/apply_patch used as authorized. All persistent new files are in this lane. Guarded command stdout/stderr logs retained for successful calculations; initial failed diagnostic preserved verbatim in FAILURES.md. manifest.json excludes itself and receipt.json. verify.py is run separately after final writes.
''')
(L/'RUN.md').write_text('''# Bounded replay

From repository cwd, prefix every command with:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`

Then `python <this-lane>/calculate.py`, `python <this-lane>/refine.py`. Both are exploratory, not proof checkers. Network re-fetch is unnecessary: frozen bytes suffice. work.py documents bounded retrieval/extraction/history procedures. Do not rerun build.py after manifest generation. Run `python <this-lane>/verify.py` as a separate final process; it verifies every manifest entry, primary/text hash pair, selected copied reports and immutable history references, then writes only receipt.json. No cap raises.
''')

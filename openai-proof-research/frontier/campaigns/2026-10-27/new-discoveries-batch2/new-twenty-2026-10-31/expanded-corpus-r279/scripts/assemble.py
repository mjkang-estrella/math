import datetime, hashlib, json, re, resource, time
from pathlib import Path

resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6 * 1024**3, 6 * 1024**3))
start = time.monotonic()
p = Path(__file__).resolve().parent.parent
sha = lambda b: hashlib.sha256(b).hexdigest()
reservation = json.loads((p / 'reservation.json').read_text())
expected = (p / 'reservation.sha256').read_text().split()[0]
assert sha((p / 'reservation.json').read_bytes()) == expected
records = json.loads((p / 'extracted-records.json').read_text())
assert set(records) == set(map(str, reservation['ids'])) and len(records) == 20

# Dispositions are discovery decisions, never acceptance or independent certification.
notes = {
365880: ('park_uniform_ramsey', 'Conjecture 7.1, arXiv v1 p.16; introduction definitions and concluding quantifiers read.', 'Clique-hypergraph Ramsey does not preserve induced nonedges of arbitrary F. Need a uniform induced-host construction with the exact tower height and linear top argument.', '365880v1', ['365880v1.txt'], 'No proof or credible full uniform construction; all-n and all-F scope cannot be replaced by complete F.'),
404032: ('exclude_source_theorem', 'OWR PDF pp.68–70: definitions, Theorem 2, counting corollary and absorption overview read.', 'The literal assertion is the printed Theorem 2, not an unanswered existence question. New proof investment would reproduce a source theorem.', '404032', ['404032.txt'], 'Source theorem is decisive for exclusion. The full Keevash–Sah–Sawhney journal absorption proof was not read; 2025 PLMS publication located by search.'),
404651: ('park_uniform_shuffle', 'OWR PDF pp.15 and 33: literal conjecture, example 652134, factor graph, Tutte proposition, extreme-window proposition read.', 'Three ordinary approaches recorded in ordinary-attempts.md. Need acyclicity for every k, or an all-length shuffle-avoiding family, not just one bad window or a new finite k.', '404651', ['404651.txt'], 'Source already reports acyclicity through k=5. Full primary citing literature not exhausted; no new route qualifies.'),
403683: ('park_uniform_girth', 'OWR PDF pp.47–48: Theorems 1–3, Conjecture 4 and odd-girth Theorem 5 read.', 'The known odd-girth construction does not exclude short even cycles. Full same-girth control for arbitrary F remains missing.', '403683', ['403683.txt'], 'No claimed new construction. Full companion article proofs and later journal corrections not exhaustively read.'),
400235: ('park_uniform_discrepancy', 'OWR PDF p.8: array definition, boxes, full Conjecture 1 and probabilistic motivation read.', 'Subgroup boxes defeat the naive addition-table construction; arbitrary-box mixing for arbitrarily large arrays in every dimension remains missing.', '400235', ['400235.txt'], 'Neither this failed construction nor random-array motivation supplies a Latin array or a full counterexample.'),
399542: ('exclude_source_theorem', 'OWR PDF pp.22,24–25: Branden theorem, probabilistic precursor and direct-sum partition proof. arXiv1412.0245 partition proof read.', 'The exact delta(k epsilon,m)/k assertion is already the printed theorem, with its direct-sum proof.', '399542', ['399542.txt','399542-prior.txt'], 'Upstream interlacing/root-bound dependency proofs not all read. Exclusion does not require a new independent proof.'),
397840: ('park_analytic_scope', 'OWR PDF p.52: equivalent lambda-harmonic Conjecture 2 and stated spectral/one-dimensional cautions read.', 'Negativity in L2 alone is insufficient; need a negative direction in the constrained lambda-harmonic solution space for every smooth bounded domain and lambda>lambda1.', '397840', ['397840.txt'], 'No finite certificate route; original preceding conjecture and full subsequent analytic literature not completely audited.'),
339293: ('park_uniform_rainbow', 'arXiv1805.07564 v1–v3 Conjecture 10.2 and surrounding known-extremes discussion; v3 Lemma 9.5 and its augmentation proof read.', 'Need (1-epsilon)m equal-size rainbow forests for every k under one epsilon-dependent m. Sparse or spanning special regimes do not cover the uniform statement.', '339293v3', ['339293v1.txt','339293v2.txt','339293v3.txt'], 'All arXiv version target passages checked; full 2019 journal body and every long proof not read.'),
335299: ('park_infinite_classification', 'arXiv1702.04499 v1/v2 Conjectures 3–4, conditional Theorem 6, generating-function proof opening read; Integers2019 source obtained.', 'The coefficient identity gives a precise route but not the global periodic-zero/sign classification. Theorem 6 is conditional, not a resolution.', '335299v2', ['335299v1.txt','335299v2.txt','335299-journal.txt'], 'Integers PDF cached and extracted; full journal proof not claimed read. Later search hit 2111.07754 concerns a different finite-hole problem, body unread.'),
359497: ('hold_latest_journal_unread', 'arXiv2308.07101v1 Conjecture 8.2, minimal-decomposition independence remarks; ITCS2024 Conjecture17 and surrounding discussion read.', 'A bound on number of decompositions is not a bound on the span of one-variable factors. Need field-uniform support dimension for every minimal decomposition.', '359497v1', ['359497v1.txt','359497-journal.txt'], 'Latest JLMS2026 DOI10.1112/jlms.70485 identified. Direct full-body request returned403 and stopped. ITCS PDF is a conference publication, not the latest journal version.'),
374489: ('exclude_prior_public_refutation_claim', 'arXiv2604.27868v1 pp.44–48 Conjecture7.4, puncture dimension count and equivalence Theorem7.5; Figure11 inspected. October citing paper and Prajapati2026 reduction read.', 'Prajapati2608.08478v1 Corollary6 explicitly refutes (5,3,F2); Proposition5 is computational and was not rerun. October2610.17570 also reports failure and solves (4,3).', '374489v1', ['374489v1.txt','374489-citing.txt','374489-obstruction.txt'], 'Public prior claim is enough to withhold new discovery credit. No independent SAT/certificate/classification validation, journal certification or Lean refutation claimed.'),
364968: ('exclude_published_refutation', 'Source2409.17724v1 introduction and construction discussion; Li–Tang–Zhan2410.23702 Theorem1 proof opening and explicit constructions pp.8–10 read. Figures1–3 visually inspected.', 'Prior graph G8 consists of two K4 copies and three connecting edges as printed, with n=8,m=15<49/3. The published general construction already refutes the literal bound.', '364968v1', ['364968v1.txt','364968-prior.txt'], 'Full lower-bound case analysis not audited, unnecessary for prior counterexample exclusion. Latest journal version and all citing works not certified complete.'),
400249: ('park_extremal_classification', 'OWR PDF pp.35–36: exact class definition, Conjecture1, asymptotic theorem and known Gruslys–Letzter value result read; historical r38 source-family hits retained.', 'Knowing the minimum value g(n,e) for large n does not classify every extremizer for every n,e. Equality cases in symmetrization remain unproved here.', '400249', ['400249.txt'], 'No endpoint/misprint exploitation. Gruslys–Letzter full published equality proof not read; no classification-clearance claim.'),
375790: ('park_PED_classification', 'arXiv2607.03894v1 §2.2 full definitions/bijection, Theorem3.12 statement and several proof cases, Theorem5.2 recurrence proof and Conjecture5.3 read.', 'Three sustained ordinary routes recorded: four-cycle replacement, connected-component product bounds, and white-set branching. No equality-sensitive recurrence or better finite witness obtained.', '375790v1', ['375790v1.txt'], 'Source contains the triangle separation, path/forest/chordal results and cycle recurrence already. Full Theorem3.12 proof and all algorithm sections not read; no new-source-object clearance.'),
403553: ('exclude_source_theorem', 'OWR PDF p.28: Theorem1 matches literal7k+1 statement. Nguyen2206.00561 introduction and known-bounds discussion also read.', 'This is the stated Girao–Narayanan theorem, not an unanswered question. Later Nguyen paper explicitly cites and strengthens it.', '403553', ['403553.txt','403553-prior.txt'], 'Full original and successor proofs not read; no independent new proof claimed.'),
353260: ('park_all_integer_chromatic_values', 'arXiv2201.04499v1 Conjecture6.1, surrounding exact-value gaps and Theorem5.1 coloring restrictions read.', 'Monotonicity in b permits jumps and does not prove attainment of every integer k>=7. Need matching upper and lower bounds at a b for every k.', '353260v1', ['353260v1.txt'], 'Figure6/7 text and restrictions read, figures not visually inspected; no proposed coloring. Current all citing proofs and journal corrections not fully audited.'),
355457: ('park_fixed_distance_extension', 'arXiv2207.12531v1/v2 Conjecture1.4; v3 Theorems1.5–1.7, Conjecture1.8 and Table1.1 discussion read.', 'Published unspecified distance constant cannot simply be replaced by100. Arbitrary-palette wording defects would be endpoint corrections and are excluded.', '355457v3', ['355457v1.txt','355457v2.txt','355457v3.txt'], 'All three target passages checked, not all long technical proof bodies or companion parts. Fixed100 bridge unresolved.'),
401378: ('park_general_cone_classification', 'OWR PDF p.32: proper cones, K-nonnegativity, primitive bounds and full ray-face digraph definition read.', 'Simplicial case m=n is classical. General m>n requires face-lattice and linear-map compatibility; generic real feasibility merely restates the problem.', '401378', ['401378.txt'], 'No characterization of all m,n; full Barker–Tam and companion classification literature unread.'),
400749: ('exclude_source_theorem', 'OWR PDF p.46 definitions and lifting lemma; Petit1507.04315v2 Definitions2.10–2.12 and Theorem3.15 with proof read.', 'The source theorem already gives the exact holonomic module and smooth-support simplicity at rank>=2 via cohomology vanishing and Proposition3.8.', '400749', ['400749.txt','400749-prior.txt'], 'Not all earlier arXiv versions/journal body or lifting-lemma proofs read. Already-answered exclusion, no new DQ-module result.'),
401025: ('exclude_source_theorem', 'OWR PDF pp.78–80 governing equations and Theorem3; Ren–Zhang author manuscript §4.2, Theorem4.3 and proof beginning/Lemma4.4 read.', 'The literal local-uniqueness endpoint is explicitly Theorem3 in its own report and Theorem4.3 in the cited author manuscript.', '401025', ['401025.txt','401025-prior.txt'], 'Full CGO construction, proof ending and final journal typography not audited. Positivity/regularity conventions are inherited source hypotheses, not new corrected endpoints.'),
}
receipts = [json.loads(s) for s in (p/'receipts.jsonl').read_text().splitlines()]
result = {}
for i in reservation['ids']:
    key = str(i); v = records[key]; r = v['record']
    status, depth, gap, primary, files, limit = notes[i]
    line = (p/'raw'/f'{i}.jsonl').read_bytes()
    assert sha(line) == v['raw_sha256'] and json.loads(line) == r
    chunk = Path(v['chunk']); chunk_data = chunk.read_bytes()
    assert sha(chunk_data) == v['chunk_sha256']
    assert chunk_data.splitlines(keepends=True)[v['line']-1] == line
    source_inventory = []
    for name in files:
        f=p/'sources'/name
        source_inventory.append({'path':'sources/'+name,'sha256':sha(f.read_bytes()),'complete_file_read':False})
    result[key] = {
        'mathdb_id':i,'title':r['title'],'canonical_url':r['canonical_url'],
        'literal_statement':r['statement'],'statement_sha256':sha(r['statement'].encode()),
        'statement_hash_encoding':'UTF-8 of exact parsed statement string; no trailing newline',
        'raw_provenance':{k:v[k] for k in ['chunk','line','chunk_sha256','raw_sha256']},
        'raw_file':f'raw/{i}.jsonl','full_parsed_record':r,
        'disposition':status,'literal_read':True,'review_depth':depth,
        'ordinary_attempt_or_exclusion':gap,'remaining_gap_and_limits':limit,
        'ordinary_attempts_file':'ordinary-attempts.md','source_inventory':source_inventory,
        'receipt_file':'receipts.jsonl','historical_check':'history-matches.txt, history-title-source-check.json, historical-dispositions.json and reconciliation.md: bounded ID/title/URL/source-family searches; absence not clearance',
        'all_versions_target_checked': 'arxiv.org' in r['source_url'],
        'all_source_bodies_and_citing_proofs_read':False,'current_registry_clearance':False,
        'full_literal_solution_produced':False,'pi_execution_assignment':None,
        'lean_run':False,'independent_review':False,'credit':0,
    }
(p/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
registry = {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'openai_root_oid':re.search(r'currentOid":"([0-9a-f]{40})',(p/'sources/registry-openai.html').read_text()).group(1),
 'limits':['Public root HTML is not a current complete tree. No GitHub API called.',
 'LeanPool projects.yml and LeanPool.lean are current fetched routing indexes, not all theorem bodies.',
 'No new qualified candidate; no global priority, complete registry absence, or literature clearance claimed.',
 'Inherited trureturing direct access denials respected; no retry or alternate denied API route.'], 'indexes':[]}
patterns=[r'\b'+str(i)+r'\b' for i in reservation['ids']]+['puncturing','shuffle','perfect.edge.dominat','cyclic.neighborhood','subspace.steiner','triangular.edges','coinciding.representation']
for name in ['registry-pool.yml','registry-pool.lean']:
    t=(p/'sources'/name).read_text(); hits=[]
    for n,line in enumerate(t.splitlines(),1):
        if any(re.search(q,line,re.I) for q in patterns):hits.append({'line':n,'text':line})
    registry['indexes'].append({'file':'sources/'+name,'sha256':sha(t.encode()),'matches':hits})
(p/'registry-screen.json').write_text(json.dumps(registry,indent=2)+'\n')
checks={'expected_sha256':expected,'before_sha256':'24100ff5b8e8f843e3a12f79907c3aa93a68f88cf9814bd7180a9d0c4925995e',
 'after_sha256':sha((p/'reservation.json').read_bytes()),'exact20keys':len(result)==20 and set(result)==set(map(str,reservation['ids'])),
 'raw_chunk_replay':'PASS: every line, newline, full parsed record and complete chunk hash verified',
 'assignment_unchanged':True,'reserve_script_run':False,'reselection':False,'accepted_credit':0}
assert checks['after_sha256']==expected
(p/'reservation-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
inventory={'receipts':receipts,'read_depth':'Per-ID results.json gives actual passage depth; fetched/extracted is not read.',
 'figures_inspected':['figures/364968-prior-8.png','figures/364968-prior-9.png','figures/374489v1-44.png'],
 'latest_journal_gap':'359497 latest JLMS2026 full body 403; stopped. Other journal/correction coverage is bounded, not complete.'}
(p/'source-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
(p/'audit-log.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'script':str(Path(__file__).resolve()),'cpu_limit_seconds':120,'address_space_limit_bytes':6*1024**3,
 'wall_seconds':time.monotonic()-start,'cpu_usage':resource.getrusage(resource.RUSAGE_SELF).ru_utime,
 'notes':['Source fetch script uses two threads with 8-second per-request timeouts and shell timeout140s.',
 'Preliminary extraction, searches and page reads were short foreground inline Python commands; not all had explicit OS resource caps or persisted stdout. This logging limitation is not concealed.',
 'No mathematical execution, child agent, git operation, shared file write, browser action or publication.']},indent=2)+'\n')
manifest={str(f.relative_to(p)):sha(f.read_bytes()) for f in sorted(p.rglob('*')) if f.is_file() and f.name!='manifest.json'}
(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'records':len(result),'reservation':checks,'registry_matches':[len(x['matches']) for x in registry['indexes']],'files':len(manifest)}))

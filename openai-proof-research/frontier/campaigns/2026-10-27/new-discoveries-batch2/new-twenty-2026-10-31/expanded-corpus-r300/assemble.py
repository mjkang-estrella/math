exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=json.loads')[0])
import re
h=lambda b:hashlib.sha256(b).hexdigest()
reservation=json.loads((l/'reservation.json').read_text());ids=reservation['ids']
provenance=json.loads((l/'provenance.json').read_text());byid={p['id']:p for p in provenance}
info={
319291:('PARK_NO_FULL_GAME_SIMULATION','Conjecture 7.2, replacement definition and lead equivalence, lines 690–704','Follow-suit/discard simulation for arbitrary suits is unproved; single-suit strategy stealing does not transfer.'),
319346:('PARK_NO_SIGN_CONTROLLED_MINOR','Conjecture 1.4 and surrounding rank/table discussion, lines 790–806','Structural rank is insufficient for actual rational row independence. No nonzero minor or row dependence proved.'),
319348:('PARK_LITERAL_ISOMORPHISM_FIDELITY','Conjecture 2.2 and full adjacent explanation, lines 1793–1823','Source requires good connected structures, extra A1 hypotheses and uniqueness up to isomorphism. No new intended counterexample or general rigidity proof.'),
319360:('PARK_SUSTAINED_TEST_COMPARISON','Theorems 4.3/4.6/4.7, Lemmas 4.4–4.5 proof and Conjecture 4.8','Semantic toughness-to-factor implication does not imply passing a non-best sufficient degree test. Missing graphicality-aware conversion of a,b,q to a forbidden toughness index.'),
339277:('PARK_FLAGSHIP_NO_FULL_ROUTE','Original source body fetched, not technically read beyond literal corpus statement','Need both universal near transversals and odd full transversals. No exact augmenting mechanism or witness; no current-open certification.'),
316980:('EXCLUDE_PUBLIC_FULL_PROOF','Original Conjecture 6.2, Proposition 6.3 proof; Wotzlaw Theorem 4.6.1, Lemma 4.6.3 and Corollary 4.6.4 proofs','Exact two-range target printed and proved in Wotzlaw 2009 thesis pp.72–74. Broader graph-manifold conjecture is different.'),
317342:('EXCLUDE_PUBLIC_F_PLUS_ROUTINE_G_BRIDGE','Diao Definitions 1.1–1.2, Conjecture 7.4; Even-Zohar Theorem 2, Corollary 14, §3.3 selected argument','F piecewise-linearity explicitly public; finite monotone integer G has finitely many changes on compact intervals. Stricter continuity/endpoints not proved; no credit under either reading.'),
317350:('EXCLUDE_PUBLIC_INTENDED_HOLD_FIELD_SCOPE','Original statement fetched; Datta–Murai introduction, Theorem 4.3/Corollary 4.4 proof; Burton et al. §2.3 Theorems 2.3–2.7','Intended mod-2 result publicly solved in all relevant dimensions; arbitrary-field literal needs orientability. Historical original full proof dependencies not all read.'),
317478:('PARK_ALL_ITERATES_NO_PRESERVATION','Chen Conjecture 1.2 with adjacent definitions/background','Need an all-n all-iterate log-concavity invariant; RSK counts and first-order log-concavity do not supply it.'),
317479:('PARK_ALL_ITERATES_NO_POSITIVE_MODEL','Chen Conjecture 1.4 with adjacent definitions/background','Need coefficientwise positivity of every q-convex iterate, not scalar or first-order inequalities.'),
317480:('PARK_STATISTIC_AND_ALL_ITERATES','Chen Conjecture 1.8 including the extra clause and adjacent background','Maximum mutually crossing arcs is not total crossing pairs; no valid all-iterate positive model or exact refutation.'),
317512:('PARK_KERNEL_IDEAL_BRIDGE','Source §6 Conjecture 6.8 and preceding representation-ring discussion','Settlement does not prove kernel generation by cross-ratio differences. Need exact ideal equality or a fully settled extension counterexample.'),
317604:('EXCLUDE_PUBLIC_FULL_PROOF','Original conjecture source fetched; actual journal §1.6 Lemma 1.9 and Corollary 1.10 including proofs','The exact large-n bound and equality classification are printed public results (2015).'),
317646:('EXCLUDE_PUBLIC_FULL_PROOF','Original latest introduction; Harcos–Károlyi–Kós Theorems 1–3, Lemma 4 and §2 full proof pp.3–5','Theorem 3 is exactly the odd-order finite abelian group target; additive/multiplicative notation is the only bridge.'),
317666:('PARK_SUSTAINED_EXACT_CONE_ROUTE','§3 Theorems 3.1/3.4, Examples 3.6–3.7 and lower-bound/conjecture paragraphs; inequalities and neighboring proof text','Topology-independent cone injection, compatible leaf deletion and fibre bound unproved; Helly does not bound exact intersection representation.'),
317722:('EXCLUDE_COMPLETE_CLASSICAL_BRIDGE','Raff §3 graph definition, §6 Theorem 6.1/Conjecture 2, thesis Chapter 3 repeated conjecture','Complete positive-root, collision/cancellation and integral minimum-annihilator bridge in ORDINARY-ATTEMPTS.md. Zero credit by full classical reduction, not ease.'),
317724:('EXCLUDE_COMPLETE_CLASSICAL_BRIDGE','Raff §6 Conjecture 4 and thesis Conjecture 8 minimum-order wording','Full Kk spectral specialization has k distinct nonzero exponential coefficients; Vandermonde proves minimum order k. Zero credit classical reduction.'),
317864:('PARK_NO_GRAPH_BASIS_POSITIVE_EXPANSION','Notation 1.11–1.13, Proposition 1.14 proof and Conjecture 1.17; extracted examples','Positive determinant values do not imply graph coefficients positive. All-degree cyclic cancellation unpaid. Graph images not visually inspected.'),
317985:('PARK_DISTINGUISH_Q_FROM_T_UNIMODALITY','Corollary 5.16 and Conjecture 5.17; Henderson–Wachs Theorem 1.2','Public t-unimodality theorem does not prove fixed-(cycle type,des,exc) q-unimodality. Missing a grading-preserving injection or representation.'),
318040:('EXCLUDE_LITERAL_DOMAIN_CORRECTION_PARK_INTENDED','§1.1 Xi degree-form definition, §4 Conjecture 4.2/Proposition 4.3 and parameter criterion; author HTML fetched','Xi are derived, not independent. Shared linear invariant and dimension mismatch in literal paraphrase give only a domain/transcription correction. Intended nullcone assertion unproved here.')}
out={}
for i in ids:
 p=byid[i];o=p['record'];p['statement_sha256_utf8']=h(o['statement'].encode())
 status,depth,gap=info[i]
 out[str(i)]={
  'mathdb_id':i,'title':o['title'],'literal_statement':o['statement'],'statement_sha256_utf8':p['statement_sha256_utf8'],
  'canonical_url':o['canonical_url'],'source_url':o['source_url'],
  'full_parsed_record':o,'raw_provenance':{k:v for k,v in p.items() if k!='record'},
  'raw_artifact':f'records/{i}.raw.jsonl','parsed_artifact':f'records/{i}.json',
  'disposition':status,'accepted_credit':0,'precise_gap_or_exclusion':gap,
  'review_depth':{'literal':'Full literal statement read; full raw/parsed record recovered.','primary_actual_read':depth,
   'historical_versions':'All versions listed by original abs page retrieved; older bodies not generally read. Fetching/hash/conversion is not technical reading. Raff source is single-version; the sustained recurrence targets also have the source thesis compared.',
   'latest_journal_corrections_citing_figures':'Incomplete except specifically named read journal proof; no universal literature clearance. No figures visually inspected. See inventory.'},
  'ordinary_attempts':'ORDINARY-ATTEMPTS.md',
  'history':'history-keyed.json; history-family-hits.txt; HISTORY-AND-REGISTRIES.md',
  'registry':'registry-heads.json; registry-matches.json; current candidate directory and imports/projects routing only',
  'source_qualification':'No new source-qualified endpoint. Public exclusions do not require asserting complete literature coverage; parked targets retain all source/novelty gaps.',
  'pi_plan':None,'pi_execution_authorized':False}
assert len(out)==20 and set(map(int,out))==set(ids)
(l/'results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
(l/'provenance.json').write_text(json.dumps(provenance,ensure_ascii=False,indent=2)+'\n')
inventory=[]
for f in sorted((l/'sources').iterdir()):
 if f.name.endswith('.receipt.json'):continue
 depth='Retrieved/hash or text conversion only; not a full technical read.'
 if f.name in ['openai-CONTENTS.md','omega-README.md','omega-Trureturing.lean','aim-README.md','pool-LeanPool.lean','pool-LeanPool_projects.yml']:depth='Bounded family-term screen; matching entry context routing only.'
 if f.name.startswith('pool-candidates'):depth='Bounded candidate directory/index term and path screen only; routing, not proof-body review.'
 if f.name.endswith('-head') or f.name.endswith('-commit'):depth='Current OID or date extraction; no full page read.'
 if f.name.endswith('-abs'):depth='Version and journal metadata extraction only.'
 if f.name.endswith('-pdf.txt'):
  stem=f.name[:-8]
  rows=[(i,info[i][1]) for i in ids if json.loads((l/f'records/{i}.json').read_text())['source_url'].endswith('/'+stem)]
  if rows:depth='; '.join(str(i)+': '+d for i,d in rows)
  if re.search(r'v\d+$',stem):depth='Historical version retrieved and converted, not technical read; no claim of full comparison.'
  extra={'snevily-1004.0253':'Theorems 1–3, §2 proof pp.3–5 and Lemma 4 read.', 'multiset-journal':'§1.4 target match, §1.5 theorem statements, §1.6 Lemma1.9/Cor1.10 full proof read.', 'stacked-murai':'Introduction source-history, Theorem4.3 and Corollary4.4 statement and proof read.', 'tight-construction':'§2.3 Theorems2.2–2.7 and definitions read; their original cited proofs not all read.', 'raff-thesis':'Chapter3 recurrence conjecture and minimum-order wording, selected neighboring text read; other chapters unread.', 'wotzlaw-thesis':'Theorem4.5.2, selected proof lemma passages, full §4.6 target proof/bridge pp.72–74 read. No full thesis proof audit.', 'evenzohar':'Theorem2, Corollary14, §3.3 selected formula/construction/sublinearity argument read; full proof of all sharp bounds not audited.', 'unimodal-henderson':'Introduction/Theorem1.2 only; not used as q-unimodality resolution.'}
  if stem in extra:depth=extra[stem]
 inventory.append({'path':str(f.relative_to(l)),'bytes':f.stat().st_size,'sha256':h(f.read_bytes()),'actual_read_depth':depth})
(l/'inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
after=h((l/'reservation.json').read_bytes());before=json.loads((l/'reservation-before.json').read_text())['sha256'];expected=(l/'reservation.sha256').read_text().split()[0]
assert after==before==expected
for i in ids:
 raw=(l/f'records/{i}.raw.jsonl').read_bytes();assert raw.endswith(b'\n');assert h(raw)==byid[i]['raw_sha256'];assert json.loads(raw)==out[str(i)]['full_parsed_record']
(l/'reservation-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'before':before,'after':after,'expected':expected,'match':True,'exact_id_count':20,'no_reselection_or_padding':True,'all_raw_newlines_preserved':True},indent=2)+'\n')
print('Validated exactly twenty keyed results; raw bytes, parsed records, statement hashes and reservation match.')

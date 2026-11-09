import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,sys,time
lane=pathlib.Path(__file__).resolve().parent
utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
def put(n,x):
 s=x if isinstance(x,str) else json.dumps(x,indent=2)+'\n'
 subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),n],input=s,text=True,check=True,stdout=subprocess.DEVNULL)
objections=[
 {'key':'O1','objection':'Standalone signs do not imply contextual order','resolution':'Winning strategies at every follower/partition discharge actual Theorem 11 proviso; only then infer contextual weak order.','state':'RESOLVED'},
 {'key':'O2','objection':'Numeric closure may silently replace a literal form by an equal canonical form','resolution':'Classical Theorem 3.3 proves literal sum/conjugate closure; no replacement used.','state':'RESOLVED'},
 {'key':'O3','objection':'Cancellation might assume the desired bidding inverse','resolution':'A+bar(A) classically zero is first transferred to contextual zero, then inverse translation used.','state':'RESOLVED'},
 {'key':'O4','objection':'Marker retention/transfer, losing states, terminal auctions and zero budgets','resolution':'Explicit simultaneous winning-region induction handles every opponent bid; complementary winning strategy makes zero optimal even at losing states.','state':'RESOLVED'},
 {'key':'O5','objection':'Strictness and fixed-budget/one-sided quantifiers','resolution':'Universal weak lift precedes single-partition strictness witness; all reasoning at the fixed b; one-sided interpolation proved separately.','state':'RESOLVED'},
 {'key':'O6','objection':'Author calls every complete classical/source adaptation explicitly excluded','resolution':'Printed campaign excludes routine corollaries, not all proofs using prior lemmas. Uniform cross-rule strategy transport is substantive candidate content; root adjudication remains.','state':'AUTHOR_EXCLUSION_NOT_ADOPTED'},
 {'key':'O7','objection':'Integer zero-bid proofs already contain the mechanism','resolution':'Related source proofs read; they cover canonical integer forms, not all numeric literal trees. General class-wide sign/marker transport needs the new invariant and cannot use canonicalization.','state':'SIGNIFICANCE_PASS_RECOMMENDATION'},
 {'key':'O8','objection':'Journal or subsequent work may change or subsume endpoint','resolution':'Publisher preview not body; bounded search yielded no lawful open full journal text. Thesis and announced follow-up remain leads.','state':'MATERIAL_HOLD'},
 {'key':'O9','objection':'No exact formal certificate','resolution':'No execution authorized; finite semantic infrastructure appears feasible but no checked endpoint/replay supplied.','state':'NOT_ESTABLISHED'}]
put('objections.json',{'355433':objections})
review={'355433':{'mathdb_id':355433,'role':'independent ordinary mathematics and qualification reviewer','disposition':'HOLD_JOURNAL_VERSION_PRIOR_CLEARANCE','ordinary_correctness':'PASS_RELATIVE_TO_NAMED_CLASSICAL_AND_SOURCE_THEOREMS','literal_arxiv_v2_fidelity':'PASS','journal_version_fidelity':'HOLD_MATERIAL_BODY_UNREAD','prior_novelty':'HOLD_BOUNDED_INVESTIGATION_NOT_CLEARANCE','significance':'PROVISIONAL_PASS_SUBSTANTIVE_STRATEGY_TRANSPORT_ROOT_ADJUDICATES','author_blanket_exclusion_adopted':False,'new_contribution':'All-follower/all-partition zero-bid sign-marker winning invariant on literal classical numeric forms; contextual order embedding after source lift; hereditary class characterization.','formal_feasibility':'PLAUSIBLE_SUBSTANTIAL_SEMANTIC_INFRASTRUCTURE_NO_EXECUTION','certificate':'NOT_ESTABLISHED','strict_replay':'NOT_PERFORMED','scope':'Every fixed natural total budget, all finite tests and chip/marker partitions; joint target quantifiers plus stronger separate one-sided conclusion','ordinary_review':'REVIEW.md','objections':'objections.json','source_inventory':'source-inventory.json','receipts':['bootstrap-receipt.json','frozen-before.json','frozen-after.json','reads.jsonl','history-receipt.json','access.json','web-evidence.json'],'manifest':'manifest.json','manifest_verification':'manifest-verification.json','pi_plan':None,'pi_dispatch':False,'children':False,'formal_execution':False,'accepted_credit':0,'campaign':{'accepted':52,'target':60,'delta':0},'next_smallest_useful_step':'Read lawful primary full journal/accepted text, compare auction, comparison theorem and final conjecture/class definitions; then resolve thesis/follow-up leads if public.'}}
put('review.json',review);put('keyed355433-review.json',review)
rows=[json.loads(l) for l in (lane/'reads.jsonl').read_text().splitlines()]
entries=[]
for i,r in enumerate(rows):
 r['receipt_id']='read-'+str(i+1)
 entries.append(r)
put('read-inventory.json',{'records':entries,'depth_caveat':'Selections are emitted ranges, not full-manuscript review. Metadata and access receipts read as routing. Empty v1 range 920:1020 produced no cognitive source read; later 740:765 actually read. Initial combined display had output truncation; applicable primary proof material and ranges itemized in REVIEW.','telemetry':'Self high-water only for read scripts; no retrospective samples. Tool transcript records actual successful command exits.'})
put('source-inventory.json',{
 'primary_proof_depth':[
 {'source':'../expanded-corpus-r361/sources/bidding.html.txt','depth':'Rules/contextual definitions 53:142; full Lemma10/Theorem11 proof 240:428; 449:484; final target 1070:1110; integer comparison/proof pattern 650:750. Combined tool output truncated parts of 449:484; no full-body claim. Critical strategy proviso and complete Theorem11 proof were actually visible.'},
 {'source':'../bidding-number-source-proof-ideation-r1/sources/classical.pdf.txt','depth':'Outcome/sign 160:205, group/order 284:510, numeric definition/interpolation/closure/totality 630:710. Actual proofs read; not canonical classification or full book.'},
 {'source':'../expanded-corpus-r361/sources/bidding-companion.html.txt','depth':'50:190 rules, zero-budget theorem and PSPE proof. Not full body.'},
 {'source':'../expanded-corpus-r361/sources/bidding-v1.html.txt','depth':'Narrow find plus final future-work 740:765; not full body.'},
 {'source':'../bidding-number-source-proof-ideation-r1/sources/survey.pdf.txt','depth':'335:447 actual contextual definitions/comparison passages; not full body.'},
 {'source':'https://arxiv.org/html/2507.04717v1','depth':'Primary web introduction/setup, section5 definitions and complete Lemma5.4 proof via find, epilogue via find; not full body. Classical only.'},
 {'source':'https://link.springer.com/article/10.1007/s00182-024-00909-z','depth':'Public preview/notes/dates only; journal body UNREAD.'}],
 'author_artifacts':'PROOF.md, REVIEW.md, review.json, read-inventory.json, source-inventory.json and access receipts read in full as emitted; not independent source substitutes.',
 'historical':'Allowlisted r361 results.json 355433 entry only; no unrelated historical body review.',
 'live_registry':'GET current repository heads only; body-wide novelty not cleared.',
 'missing_material':['Journal/accepted full text and substantive differences','2025 thesis Bidding Combinatorial Games','Announced subsequent numbers/infinitesimals bidding follow-up if public','Current project proof-body census'],
 'network_raw_receipts':'access.json', 'local_input_hash_receipts':'reads.jsonl and history-receipt.json'})
put('web-evidence.json',{'recorded_utc':utc,'kind':'Transcript references, not raw HTTP captures; no byte/hash/status fabricated','search_batches':[
 ['"Constructive comparison in bidding combinatorial games" accepted manuscript','"Constructive comparison in bidding combinatorial games" "conjecture" zugzwang','"bidding" "number characterization" proof'],
 ['"s00182-024-00909-z" pdf manuscript','"Urban Larsson" "zugzwang" "2025" bidding numbers'],
 ['"Prem Kant" "Bidding Combinatorial Games" thesis 2025 pdf','"bidding" "numbers and infinitesimals" Kant Larsson proof','"bidding" "classical" "zero-bid" numbers']],
 'primary_open_urls':['https://arxiv.org/abs/2207.11596','https://cris.technion.ac.il/en/publications/constructive-comparison-in-bidding-combinatorial-games/','https://link.springer.com/article/10.1007/s00182-024-00909-z','https://arxiv.org/html/2507.04717v1'],
 'finds':{'https://arxiv.org/html/2507.04717v1':['Lemma 5.4','bidding','5.1']},
 'new_primary_lead':'https://www.ieor.iitb.ac.in/node/3955 (search result defense announcement only, no thesis body)',
 'lead':'https://ludicum.org/cgtc-v/ (conference abstract search result only)',
 'denied_retries':False,'contact_or_accounts':False,'journal_full_body_obtained':False})
put('execution-receipt.json',{'utc':utc,'scope':'Finalization process only','allowed_cpus':sorted(os.sched_getaffinity(0)),'cpu_limit_s':120,'as_limit_bytes':6*1024**3,'self_high_water_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'children':'Every write child synchronous and reaped','no_group_peak_claim':True,'transcript':'All shell command exits and fetch-session completion are recorded by tools; no retrospective telemetry supplied'})
print('Review, objections and inventories written.')

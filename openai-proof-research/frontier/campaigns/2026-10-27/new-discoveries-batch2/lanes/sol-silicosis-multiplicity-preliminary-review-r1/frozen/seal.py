from pathlib import Path
import hashlib,json,datetime,platform
P=Path(__file__).resolve().parent;B=P.parent.parent;G=B/'lanes/root-edge-irregulator-current-prior-r1'
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
reg=json.loads((G/'CURRENT-REGISTRIES.json').read_text())
ctx=json.loads((P/'context-screen.json').read_text());ledger=json.loads((B/'ledger.json').read_text())
# Further reconcile credited families without printing full historical ledgers.
(P/'ledger-reconciliation.json').write_text(json.dumps({'utc':now,'accepted_count':ledger['accepted_count'],'total':ledger['total_accepted_count'],'next':ledger['next_global_outcome_number'],'accepted_titles':[r['title'] for r in ledger['accepted']],'lane_credit':0},indent=2)+'\n')
(P/'progress.md').write_text(f'''# r76 final progress — {now}

Solo lane complete for handback; no process intentionally left running.

1. Read source instructions/context; reconcile r57–r74, r75 and credited families.
2. Two primary questions screened; geometry excluded by public answer.
3. Full ordinary power-law multiplicity argument completed in PROOF.md.
4. Exact bounded checks passed. No numerical-only theorem or helper credited.
5. Substantive/VoR/semantic-prior clearance remains HOLD: no eligible nomination.

Mathematical gap: none for the stated multiplicity theorem. Suggested H/K
curvature is unproved and not needed. Strongest objection: routine classical
Descartes reduction. Literal equality-case existence correction is excluded.
Falsifier: actual source function with three positive roots at one positive
level, or finite positive-d transform increasing sign variation.

Counts remain 7 additional /37 total,next38; credit0. Root owns decisions.
No Lean/paper, git/cache access, API call, browser tab, child, contact, upload,
post, account mutation or write outside this lane.
''')
(P/'failures.md').write_text('''# Failures and access limits

* Initial context-summary scanner used frontier as its root, yielding zero
  summaries. Preserved context-screen-wrong-root.json; corrected to repository
  root and re-ran under identical caps:315 summaries. No novelty clearance was
  inferred from the bad scan.
* UAb exact public repository body returned HTTP403. Direct MO HTML returned
  HTTP403, although web public extraction supplied the question/answer proof.
  No direct retry or access bypass occurred.
* Web requested follow-up HTMLv3 and received404; inspected actual abstract
  next, which lists onlyv1, and retrieved that exactv1 PDF. Failed guessedv3 is
  not claimed to exist. A guessed incomplete Cambridge article route and DOI
  web lookup failed. VoR body equivalence remains unknown.
* First accepted-manuscript download and PDF extraction were performed as
  direct curl and capped pdftotext; the guard output is in the tool transcript,
  not a local receipt. All later scripts/fetch/extraction/checks used retained
  copied caps. No mathematical experiment ran without the guard.
* No numerical/CPU/RSS failures or raised caps. Fetch/prepare/check receipts
  retained. No GitHub API call was made; inherited403/429 restrictions respected.
* Source page search-engine crawl labels such as 'months ago' are not used
  as publication dates. arXiv histories and PDF imprints identify versions.
''')
files=[{'file':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(P.rglob('*')) if p.is_file() and p.name!='provenance.json']
prov={'sealed_utc':now,'python_version':platform.python_version(),'lane':'sol-fresh-source-discovery-r76','lane_credit':0,'counts_changed':False,'source_status':'Full ordinary multiplicity theorem; no eligible nomination; substantive/VoR/semantic-prior HOLD','http_fetches':json.loads((P/'fetch-records.json').read_text()),'initial_accepted_source':{'url':'https://strathprints.strath.ac.uk/70232/1/da_Costa_etal_EJAM_2019_Modelling_silicosis_structure_of_equilibria.pdf','file':'evidence/silicosis.pdf','file_mtime_utc':datetime.datetime.fromtimestamp((P/'evidence/silicosis.pdf').stat().st_mtime,datetime.timezone.utc).isoformat(),'mtime_is_not_http_header':True,'version':'received21Sep2019 accepted manuscript;19pages','sha256':sha(P/'evidence/silicosis.pdf')},'web_tool_access':{'date_utc':'2026-10-29','individual_request_timestamp_not_recorded':True,'successful_primary_urls':['https://mathoverflow.net/questions/447678/convex-functions-in-convex-sets','https://arxiv.org/abs/1901.10670','https://arxiv.org/abs/2109.01172','https://strathprints.strath.ac.uk/70232/1/da_Costa_etal_EJAM_2019_Modelling_silicosis_structure_of_equilibria.pdf'],'failed_urls':['https://arxiv.org/html/2109.01172v3','https://doi.org/10.1017/S0956792519000329','https://www.cambridge.org/core/journals/european-journal-of-applied-mathematics/article/modelling-silicosis-the-structure-of-equilibria/'],'search_leads_only':['https://www.gla.ac.uk/schools/mathematicsstatistics/events/details/?id=11464','https://www.dmg.tuwien.ac.at/drmota/CDG241.pdf'],'limits':'Web extraction supports bounded exclusion; not every result body downloaded; no browser tabs.'},'versions':{'main_arxiv':'1901.10670v1 2019-01-30T04:33:10Z; Section4 ending','main_accepted':'September2019 Section5 p18 conjecture;Eq3.10 and4.1','followup':'2109.01172v1 2021-09-02; Eq4 andProp1.1 piecewise-constant','classical':'Albouy–Fu1307.6842v1 Prop1/Section2','journal':'EJAM31(6)(2020)950-967; DOI10.1017/S0956792519000329;VoR comparison HOLD'},'registry_observation':reg,'context':ctx,'access_limits':['Supplied complete inventories at17:20UTC; head movement after that unknown','Path matches do not prove semantic absence; selected actual Lean theorem/proof bodies only','No GitHub API,git,bare-cache operation,proxy,bypass,security-challenge retry or absence inference','No worldwide priority,publication equivalence or substantive PASS claimed'],'caps':{'AS_bytes':536870912,'process_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'sampling_seconds':0.04,'BLAS_threads':1,'runner_sha256':sha(P/'capped_run.py'),'unchanged_r75_runner':sha(P/'capped_run.py')==sha(P.parent/'sol-fresh-source-discovery-r75/capped_run.py')},'manifest':files}
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps({'sealed_utc':now,'files':len(files),'credit':0,'checks':json.loads((P/'checks.json').read_text())['status'],'runner_unchanged':prov['caps']['unchanged_r75_runner']}))

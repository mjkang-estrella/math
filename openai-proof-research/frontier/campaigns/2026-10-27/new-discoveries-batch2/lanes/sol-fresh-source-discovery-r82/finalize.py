import json,hashlib,datetime,re
from pathlib import Path
P=Path(__file__).resolve().parent
B=P.parent.parent
R=B.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
context=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B/'lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json']
http=json.loads((P/'http.json').read_text())
heads={}
for repo in ['omega','openai']:
 s=(P/'sources'/f'{repo}-page.html').read_text()
 heads[repo]=sorted(set(re.findall(r'currentOid\\?":\\?"([0-9a-f]{40})',s)))
# Content-address every saved source, including the known-total PDF.
sources={str(p.relative_to(P)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in (P/'sources').iterdir() if p.is_file()}
prov={
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'lane':'sol-fresh-source-discovery-r82','solo':True,'credit':0,'nomination':False,
 'baseline':{'additional':8,'total':38,'counts_changed':False},
 'source_target':{'authors':['Eli R. DeWitt','William J. Keith'],'url':'https://arxiv.org/html/2507.13566v1','version':'v1 2025-07-17T23:02:26Z','label':'Section 5 Conjecture 1','ordinary_proof':'PROOF.md','all_n':True,'residue_zero_prose_claimed':False},
 'mathematical_dependency':{'url':'https://arxiv.org/pdf/1502.00366v4','version':'v4 2016-05-04','labels':['Theorem 1 p2','Theorem 5 p3'],'local':'sources/keith.pdf','retrieval_date_utc':'2026-10-29','observed_local_file_time_utc':datetime.datetime.fromtimestamp((P/'sources/keith.pdf').stat().st_mtime,datetime.timezone.utc).isoformat(),'scope':'Known unrefined totals, no upstream proof re-audit'},
 'context_inputs':{str(p):sha(p) for p in context if p.exists()},
 'root_registry_snapshot':json.loads((B/'lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json').read_text()),
 'live_html_observed_heads':heads,'registry_clearance':'HOLD: newer Omega HTML head; no complete newer tree obtained; pinned lexical-neighbor bodies read, not worldwide semantic clearance',
 'http_records':http,'source_files':sources,
 'screen_primary_urls':['https://arxiv.org/html/2508.00074v1','https://mathdb.com/p/369588/fayers-divisibility-conjecture-for-s-s-t-s-2t-dots-core-poly','https://link.springer.com/article/10.1007/s40687-025-00502-0','https://arxiv.org/abs/2408.14365','https://arxiv.org/html/2507.13566v1','https://arxiv.org/html/2604.25394v1'],
 'web_reader_date_utc':'2026-10-29',
 'access_limits':['World Scientific 403; no retry or bypass','Springer local cookie-error response; source statement read using web reader','No API retry after inherited access limits; no git/cache operations','Searches and selected actual registry bodies are bounded, not an exhaustive semantic or priority audit'],
 'strongest_objection':'Routine adaptation of source nine-class/involution machinery; recommend strict-campaign exclusion unless root independently adjudicates otherwise',
 'remaining_gap':'No author-identified ordinary gap in the numbered preprint conjecture. Independent proof/substantive review, journal-body equivalence and current registry semantic clearance absent. Separate prose residue-zero strengthening unproved.',
 'falsifier':'An exact required parity count nonzero modulo4 on the specified progressions, a failure of a stated bijection/fixed-point classification, a prior full proof or classical subsumer, or material source revision',
 'check':json.loads((P/'check-result.json').read_text())['counts'],
 'resource_guard':{'source':str(B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'sha256':sha(P/'helper_guard.py'),'copied_unchanged':sha(P/'helper_guard.py')==sha(B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_bytes':512*1024*1024,'group_RSS_bytes':512*1024*1024,'cpu_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1,'limitation':'Sampled group accounting cannot exclude between-sample transients'},
 'forbidden_actions_performed':False,'lean_or_paper':False,'independent_review':False,
}
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
assert all((P/n).is_file() for n in ['SUMMARY.md','discovery.md','progress.md','PROOF.md','provenance.json','run.sh'])
assert prov['resource_guard']['copied_unchanged']
print(json.dumps({'artifacts_present':True,'heads':heads,'credit':0,'source_files':len(sources)},indent=2))

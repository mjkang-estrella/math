from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((L/'bindings.json').read_text())
prior=json.loads((L/'frozen/sol-honest-tournament-preliminary-review-r1/bindings.json').read_text())
transitive=[]
for r in prior:
 if r.get('original') and Path(r['original']).name in ['1803.00823v1.pdf','1803.00823v1.txt','witness-table.csv','PROOF.md','failures.md']:
  assert digest(Path(r['original']))==r['sha256']
  if r.get('copy'):assert digest(Path(r['copy']))==r['sha256']
  transitive.append(r)
(L/'transitive-selected-bindings.json').write_text(json.dumps(transitive,indent=2)+'\n')
admin={}
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative/new-discoveries-batch2'/n).read_text());admin[n]={'accepted':[{'number':x.get('number'),'title':x.get('title'),'scope':x.get('scope'),'novelty_limit':x.get('novelty_limit')} for x in d.get('accepted',[])],'keys':list(d)}
 print(n,len(admin[n]['accepted']),[x['title'] for x in admin[n]['accepted']])
(L/'administrative/reading-summary.json').write_text(json.dumps(admin,indent=2)+'\n')
access=[json.loads(x) for x in (L/'access.jsonl').read_text().splitlines()]
for r in access:
 if 'path' in r:assert digest(L/r['path'])==r['sha256']
classification={
 'honesty-openalex':'secondary metadata; discovered Cologne repository URL, no body',
 'source-citers':'secondary citation-index query, zero records; no citing bodies',
 'repec-honesty':'secondary bibliographic abstract and subscriber-only link, no body',
 'kups':'404 at indexed institutional record, parked',
 'hegarty':'primary institutional author record, 38 displayed publications',
 'martinsson':'primary institutional author record, 14 displayed publications',
 'wedin':'primary institutional author record, 5 displayed publications',
 'search-honesty':'irrelevant dictionary results, unused',
 'search-conrads':'irrelevant retail results, unused',
 'ddg-honesty':'202 human image challenge; stopped',
 'crossref-correction':'metadata query, 10 results; no exact HMW successor',
 'rilke-author':'guessed .com hostname, DNS failure, unused',
 'irlenbusch-publications':'guessed institutional path, 404; unused',
 'econpapers-honesty':'metadata and restricted publisher link only',
 'irlenbusch-home':'department home, navigational, not exact author publication body',
 'econpapers-title':'search form without results; not a negative completed search',
 'econstor-search':'fulltext related hits, not exact target body, first page only',
 'irlenbusch-research':'department topic lists, not exact target body',
 'repec-rilke':'secondary author profile, supplies .de homepage',
 'repec-walkowitz':'secondary author profile, no target body obtained',
 'rilke-official':'author personal page, listed publications 2016 onward; links WHU, no target body',
 'whu-rilke':'primary institutional author page, displayed publications 2016 onward, no target body',
 'honesty-tdm':'primary publisher metadata only; explicit authorization restriction; no body or retry',
 'schwenk-discovery':'metadata only; exact 2000 source antecedent, no body retrieved'
}
coverage={'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':{'source':'PASS inherited, literal 2018 preprint','math':'PASS inherited, corrected final draw','substantive':'provisional retention of one complete refutation','novelty':'HOLD','acceptance':'root only; no decision/count change'},'body_coverage':[
 {'source':'arXiv1803.00823v1','reference':'bindings.json','read':'Section2 entirety; Section4 Rules1-3/4.7/C4.2/T4.3 opening; Section6 definitions,6.2/6.3 proofs,6.4-6.5,6.1,rounds example,6.3 including actual proofs6.6-6.8; references','not_read_as_new_audit':'remaining long constructions; no full26-page rereview'},
 {'source':'Chalmers501180 Fulltext','reference':'bindings.json','read':'abstract; Section5 definition/Theorem5.1/Cor5.2/Lemma5.3 and actual proofs; beginning Section6','version':'2018 preprint; no journal body asserted'},
 {'source':'Conrads et al2014 DOI10.1016/j.econlet.2014.01.026','read':'no proof/model/experimental body obtained; metadata and abstract only','gate':'material body gate remains'},
 {'source':'Schwenk2000 DOI10.1080/00029890.2000.12005171','read':'bibliography and metadata only; primary body not obtained','gate':'not body-cleared'},
 {'source':'HMW successors/citers','read':'no actual successor/citing body identified by bounded searches','gate':'zero hits do not clear absence'}],
 'request_coverage':[dict(name=r['name'],url=r['url'],outcome=classification[r['name']],path=r.get('path'),sha256=r.get('sha256')) for r in access],
 'route_derivations':{'kups':'OpenAlex DOI record location','hegarty/martinsson/wedin':'links in frozen Chalmers501180 page','econpapers-title':'related-works link on EconPapers title page; form only returned','irlenbusch-home':'department root after guessed publication path failed; ordinary navigation, not access bypass','irlenbusch-research':'link in department homepage','repec-rilke/repec-walkowitz':'registered-author links in RePEc article page','rilke-official':'RePEc author homepage link, https scheme','whu-rilke':'institution link in author personal page','honesty-tdm':'exact XML text-mining link from frozen Crossref record','schwenk-discovery':'title in actual HMW bibliography'},
 'registry':'No current registry head. Known relevant repository routes parked by user; no distinct available route discovered. No HEAD/history loops.',
 'comparison':'No complete applicable subsumer inspected. Generic finite LP/interpolation/empirical-match construction already known; exact separating assignment/violation is missing bridge.',
 'administrative_counts':{'additional':9,'total':39,'next':40,'authority':'root only'}}
(L/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
failures={'preserved_inherited':'frozen preliminary access/review and hash-bound frozen/failures.md; discovery abort/smallN failures not rerun','new_access_failures':[dict(name=r['name'],url=r['url'],error=r.get('error'),status=r.get('status'),classification=classification[r['name']],path=r.get('path'),sha256=r.get('sha256')) for r in access if r.get('error') or r['name'] in ['ddg-honesty','honesty-tdm','econpapers-title','search-honesty','search-conrads']],
 'helper_failures':[{'command':'guarded python -c HTML-link inspection','error':'SyntaxError: unmatched parenthesis in print expression','exit':1,'scientific_effect':'none; no writes/no retrieval; replaced with native bounded rg reads','preservation':'exact failing expression captured in helper-failure.txt'},{'command':'guarded finish.py first execution','error':'KeyError: original, at line9; prior bindings include records without original key','exit':1,'fix':'explicitly skip records lacking original; do not infer an original path','scientific_effect':'no output files had been written; selected verification only'}],
 'parked_prior_routes':['GitHub API/raw/codeload/diff/patch','ScienceDirect','Google challenge','SemanticScholar429'],
 'new_parked_routes':['DuckDuckGo image challenge','Cologne44214 404','guessed .com DNS failure','guessed Cologne publications404','Elsevier exact TDM response authorization limitation'],
 'no_cap_raises':True,'no_bypass':True}
(L/'failure-inventory.json').write_text(json.dumps(failures,indent=2)+'\n')
print('coverage and failures written; access bytes verified; selected transitive original/copy bindings verified')

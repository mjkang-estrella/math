from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
f=p/'REVIEW.md';s=f.read_text();a=s.index('Even D >= 1 combined');b=s.index('\n* **Vaidya',a);s=s[:a]+'For example, at n=10, completing the square with D >= 1 gives only sigma_t <= 625-10 = 615, whereas the best complete bipartite value is 576 (parts 1/9 or 2/8). Thus that argument does not settle even this order; additional structure would be needed.\n'+s[b:];f.write_text(s)
obj={
 'review_date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Focused bounded prior-art comparison only; not acceptance or a new Lean audit',
 'campaign':{'count':6,'target':20,'beyond':39,'credit':0,'acceptance_authority':'root alone'},
 'inherited_technical_status':{'Lean':'complete per supplied r1','fidelity':'PASS per supplied r1','replayed_here':False},
 'objections':{
  'N1':{'status':'still open','body_read':False,'evidence':['Zhou 2004 Remark 4 p.115 visually reread: attributes unrestricted high/low fixed-edge M1 bounds to Bell [12], using quasi-clique/quasi-star constructions. No Bell theorem number supplied.','Elphick-Wocjan 2014 p.52 attributes unrestricted variance/spectral extremizers and incomparability to Bell; no restricted-class theorem statement.','Current OpenAlex Bell locations only expose denied publisher PDF; first 50 indexed citing works screened.','Permitted distinct publisher HTML returned 403, no retry. Original publisher PDF and CORE not retried.'],'conclusion':'Known restatements concern unrestricted graphs; unread sections could still concern bipartite/triangle-free graphs. No body-level clearance.'},
  'N2':{'status':'narrowed','origin_bodies_status':'still open','evidence':['1904.05053v1 is Ali-Reti on IRA/IRB and N0, not solo Reti AMC 344-345 107-115.','2211.06744v1 has four authors and a different associated DOI; variance bounds/bidegreed and dominating hypotheses are not a fixed-order triangle-free maximum.','2501.01538v1 is an absolute total-irregularity survey, citing rather than reproducing D-S 2023.','OpenAlex exact origin locations, arXiv indexed-field phrase/author searches, an institutional author-page attempt (404), and public ORCID person lookup exposed no lawful preprint.'], 'origin_identifiers':{'Reti':'10.1016/j.amc.2018.10.010','Dimitrov_Stevanovic':'10.1016/j.amc.2022.127709'},'conclusion':'Three proposed replacements rejected; actual origin bodies remain unread. Later Dimitrov coauthorship is supporting context only.'},
  'N3':{'status':'narrowed','strict_gap_status':'still open','evidence':['Elphick-Wocjan Theorem 4.1(i) and proof pp.56-58 specialize to M1 <= nm, without the connected n-2 deficit in passages read.','At n=10 the D>=1/completing-square consequence is 615 > complete-bipartite optimum 576; equality-only exclusion does not close rounding by that argument.','Vaidya-Chang 2409.06081v1 Corollary 3.4(1), alpha=2, gives M1 <= 2m(Delta+delta)-n delta Delta. For K(2,6)-e it gives 106, versus actual/desired 82.','Its Section 4 requires triangle AND quadrangle exclusion and concerns 2-distance degrees.','Bounded arXiv/OpenAlex indexed searches and absolute-irregularity maximum literature screen found no exact gap or restricted variance maximum. Search noise and incomplete indexing prevent clearance.'],'conclusion':'No strict-gap theorem or full subsumer established; no absence claim.'}},
 'bodies_read':[
  {'source':'1904.05053v1','extent':'Introduction/Table 1; Sections 2-3 theorem/proof text; reference screen','complete_body_clearance':False},
  {'source':'2211.06744v1','extent':'Sections 1-4 and Proposition 14/proof; remaining theorem labels/references screened','complete_body_clearance':False},
  {'source':'2501.01538v1','extent':'Definition; Section 3.1 through Theorem 5; Section 4 opening sigma comparison and reference [28]','complete_body_clearance':False},
  {'source':'2409.06081v1','extent':'Theorem 3.2/Corollary 3.4 proofs; relevant Section 4 statements and proof portions; Corollary page visually checked','complete_body_clearance':False},
  {'source':'Elphick-Wocjan 2014, New measures of graph irregularity','extent':'p.52 Bell attribution; Section 4 theorem/proof/remarks pp.56-58; key theorem page visually checked','complete_body_clearance':False},
  {'source':'Zhou 2004 (cached sigma-source-review-r1)','extent':'pp.115-116 visually reread, including Remark 4 and Theorem 5 continuation','complete_body_clearance':False},
  {'source':'Irregularity of Graphs, MATCH 89 (2023) 371-388','extent':'pp.371-373 and relevant references only','complete_body_clearance':False}],
 'bodies_unread':['Bell 1992 original body','Reti AMC 344-345 (2019) 107-115 original body','Dimitrov-Stevanovic AMC 441 (2023) 127709 original body','Unspecified remainder of partially read downloaded papers; see bodies_read extents'],
 'subsumer':{'found':False,'candidate':None},
 'routine_bridge':{'established_from_prior_art':False,'conditional_risk':'A published D >= n-2 theorem under the exact connected triangle-free non-complete-bipartite hypotheses could make the remaining integer-bracketing deduction routine.'},
 'novelty_verdict':'HOLD',
 'reasons':['No original objection cleared.','Actual Bell and both origin bodies remain unread.','Strict-gap specialist literature remains unresolved despite two additional actual-body comparisons.','No subsumer found is not novelty clearance.'],
 'receipts':'receipts/*.json; downloads contain original response bytes; manifest binds local evidence and used cached inputs',
 'limitations':['No fresh public-registry audit; r1 registry evidence inherited only.','ArXiv all: queries are indexed-field searches, not PDF full-text searches.','Bing search responses irrelevant; Google interstitial not treated as evidence.','This is not an acceptance recommendation.'],
 'compliance':{'no_child_agents':True,'no_git':True,'no_shared_edits':True,'no_tabs':True,'no_external_messages_or_uploads':True,'no_background_jobs_at_handback':True}}
(p/'review.json').write_text(json.dumps({'365710':obj},ensure_ascii=False,indent=2)+'\n')
# Validate explicit bound comparison by direct arithmetic, not a graph-search novelty claim.
n=10;assert max(a*(n-a)*(n-2*a)**2 for a in range(1,n))==576
assert 8*11-(6**2+5**2+5*2**2+1)==6
assert 2*11*(6+1)-8*1*6==106
(p/'receipts'/'arithmetic.json').write_text(json.dumps({'n10_bipartite_max':576,'n10_deficit_one_continuous_bound':615,'K2_6_minus_edge':{'n':8,'m':11,'M1':82,'D':6,'corollary_upper_bound':106}},indent=2)+'\n')
inputs=[p.parent/'sigma-fidelity-novelty-review-r1'/'REVIEW.md',p.parent/'sigma-fidelity-novelty-review-r1'/'review.json',p.parent/'sigma-source-review-r1'/'REVIEW.md',p.parent/'sigma-source-review-r1'/'sources'/'zhou',p.parent/'sigma-source-review-r1'/'receipts'/'zhou.json',p.parent/'expanded-corpus-r60'/'SIGMA-ORDINARY-PROOF.md',p.parent/'expanded-corpus-r60'/'sources'/'2411.04881.html']
manifest={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'note':'Post-read inventory, not a before/after integrity assertion','inputs':{},'local_evidence':{}}
for x in inputs:manifest['inputs'][str(x)]=hashlib.sha256(x.read_bytes()).hexdigest()
for x in sorted(p.rglob('*')):
 if x.is_file() and x.name!='manifest.json':manifest['local_evidence'][str(x.relative_to(p))]=hashlib.sha256(x.read_bytes()).hexdigest()
(p/'receipts'/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Validated review.json; 3 objections; HOLD; arithmetic checks passed; manifest entries:',len(manifest['local_evidence']))

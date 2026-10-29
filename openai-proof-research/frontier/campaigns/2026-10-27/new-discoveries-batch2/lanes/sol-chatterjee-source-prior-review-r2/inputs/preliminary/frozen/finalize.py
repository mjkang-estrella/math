from pathlib import Path
import hashlib,json,datetime,re
P=Path(__file__).parent
def record(p):
    b=p.read_bytes()
    return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def save(n,d): (P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
save('source-hashes.json',{str(p.relative_to(P)):record(p) for p in sorted((P/'sources').iterdir()) if p.is_file()})
guard=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
heads={}
for name in ['omega','openai']:
    h=json.loads((P/'sources'/f'{name}-HEAD.json').read_text())
    heads[name]={'head':h['sha'],'committer_utc':h['commit']['committer']['date']}
delta=json.loads((P/'sources/omega-delta.json').read_text())
heads['omega']['incremental_comparison']={'from':'a5a8bcdf56019e58c398f6f6d27a3620b896d001','commits':delta['total_commits'],'returned_files':[x['filename'] for x in delta['files']]}
heads['coverage']='HOLD: inherited incomplete semantic delta coverage; lexical baseline plus current three changed bodies is not global clearance'
save('current-registry.json',heads)
http=[]
for n in ['http.json','closest-http.json','additional-http.json']:http+=json.loads((P/n).read_text())
save('provenance.json',{
 'finalized_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'lane':str(P.resolve()),'status':'full ordinary result, independently unreviewed; qualification HOLD',
 'credit':0,'accepted_counts_unchanged':{'additional':8,'total':38},
 'source_statement':'CGK author-accepted manuscript Section6; all three distances, uniform finite multiplicative triangle constant',
 'primary_url':'https://mirkogiacchini.github.io/papers/cgk25_chatterjee_metricity.pdf',
 'precise_theorem':'For each D in {d,d_avg,d_min} and every K>0 there are jointly absolutely continuous uniform(0,1) A,B,C with D(A,C)>K(D(A,B)+D(B,C)).',
 'all_n_formulas':{'r':'1/n','AB':'r','BA':'r','BC':'r^2','CB':'r^2','AC':'1-r^2+r^3','CA':'r'},
 'ordinary_proof':'PROOF.md','verification':'bash run.sh','exact_results':'exact-checks.json',
 'guard':{'path':str(guard.resolve()),**record(guard),'AS_bytes':512*1024**2,'group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'nominal_poll_seconds':.04,'BLAS_threads':1},
 'early_screen':'duplicate-screen.json','all_date_report_inventory':'report-inventory.json','context':'context.json',
 'source_bytes':'source-hashes.json','current_public':'current-registry.json','http':http,
 'strongest_objection':'Routine adaptation of shuffle-of-Min/modulo examples; substantive eligibility not established.',
 'remaining':['independent ordinary-math review','published final-edition body comparison after single403','classical/subsumption review','current semantic registry coverage','source informal approximate terminology versus exact multiplicative quantifiers'],
 'not_claimed':['worldwide priority','campaign acceptance','optimal average additive defect','Bezdek conjecture','formalization','paper'],
 'correction':'Independent exact integration falsified initial d=1/m^2 normalization; corrected to1/m before final proof and replay.'})
save('manifest.json',{str(p.relative_to(P)):record(p) for p in sorted(P.rglob('*')) if p.is_file() and p.name!='manifest.json' and '__pycache__' not in p.parts})
print('finalized',len(json.loads((P/'manifest.json').read_text())),'files')

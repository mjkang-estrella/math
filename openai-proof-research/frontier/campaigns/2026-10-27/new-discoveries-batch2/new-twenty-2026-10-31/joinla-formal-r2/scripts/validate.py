import json, pathlib, re
root = pathlib.Path.cwd()
rows = [line.split('\t') for line in (root/'outputs/audit.tsv').read_text().splitlines()]
allowed = {'propext','Classical.choice','Quot.sound'}
axioms = sorted({x[0] for x in rows if x[2] == 'axiom'})
assert set(axioms) <= allowed, axioms
localmods = {'Antimagic','AntimagicBasics','AntimagicIso','LauShiu','Counts','Endpoint'}
local = [x for x in rows if x[1] in localmods]
assert all(x[3:] == ['false']*4 for x in local), [x for x in local if x[3:] != ['false']*4]
hits=[]
for p in sorted((root/'src').glob('*.lean')):
    for i,line in enumerate(p.read_text().splitlines(),1):
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by)\b',line):
            hits.append([p.name,i,line])
assert all(x[0]=='Audit.lean' and '"axiom"' in x[2] for x in hits), hits
result={'status':'literal endpoint proved; not acceptance','mathdb_id':365453,'credit':0,'endpoint':'not_conjecture41 : ¬ Conjecture41','axioms':axioms,'closure_declarations':len(rows),'local_declarations':len(local),'source_scan_hits':hits,'optional_exact_value_four_formalized':False,'side_check':'publisher open reprint read; no target implication found','limits':{'rss_gib':6,'cpus':2,'cpu_seconds':120,'wall_seconds':140,'lean_M':3500},'strict_replay':'all source modules rebuilt and explicitly leanchecked from fresh zip extraction'}
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

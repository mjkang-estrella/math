import sys
sys.dont_write_bytecode=True
import pathlib,hashlib,json,difflib
h=pathlib.Path(__file__).resolve().parent;r=h.parents[2]
p=h/'gen_sym.py';s=p.read_text().replace('rich=(2,3,5,2,3,5,2,7)',"rich=getattr(self,'refinement_cycle',(2,3,2,3,2,2,3,7))");p.write_text(s)
p=h/'run7a.py';s=p.read_text().replace('name,rec,stage,target,seconds,slice_seconds,schedule=args','name,rec,stage,target,seconds,slice_seconds,schedule,rich_five=args');s=s.replace('    g.run(schedule)','    if rich_five:g.refinement_cycle=(2,3,5,2,3,5,2,7)\n    g.run(schedule)');s=s.replace("ap.add_argument('--key');a=ap.parse_args()","ap.add_argument('--key');ap.add_argument('--rich-five',action='store_true');a=ap.parse_args()");s=s.replace("tuple(map(int,a.schedule.split(',')))) for k,r", "tuple(map(int,a.schedule.split(','))),a.rich_five) for k,r");p.write_text(s)
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
source=[h.parent/'sym5'/n for n in ('gen_sym.py','gen_precomputed.py','check_sym5.py','audit_coverage.py','coverage_distinct.py','supply.json','summary.json','assignment.json','checks5.json')]+[r/'verification/indep5/check_sym_F5.py',r/'verification/indep5/NOTE_F5.md',r/'notes/highdim_sym5.md',r/'notes/highdim_sym4.md']
(h/'source_hashes.json').write_text(json.dumps({str(p):sha(p) for p in source},indent=1)+'\n')
assert sha(h/'gen_sym_baseline.py')==sha(h.parent/'sym5/gen_sym.py')
for n in ('gen_precomputed.py','check_sym5.py','audit_coverage.py','coverage_distinct.py'):assert sha(h/n)==sha(h.parent/'sym5'/n)
for n in ('gen_sym.py',):
 text=''.join(difflib.unified_diff((h.parent/'sym5'/n).read_text().splitlines(True),(h/n).read_text().splitlines(True),fromfile='sym5/'+n,tofile='sym7a/'+n))
 (h/(n+'.diff')).write_text(text)
print('Copied sources byte-identical; explicit refinement-cycle option is the sole generator diff.')

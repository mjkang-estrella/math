"""Merge hash-bound direct results, require all emitted certificates checked, seal evidence."""
import sys
sys.dont_write_bytecode=True
import collections,hashlib,json,pathlib,subprocess
H=pathlib.Path(__file__).resolve().parent;R=H.parents[2]
def load(p):return json.loads(pathlib.Path(p).read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,v):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(v,indent=1)+'\n');t.replace(p)
def main():
 checks=load(H/'checks.json')
 for extra in sorted(H.glob('checks_*.json')):
  for f,pair in load(extra).items():
   for who,record in pair.items():
    if record['result']=='PASS':checks.setdefault(f,{})[who]=record
 if (H/'withdrawn.json').exists():
  for record in load(H/'withdrawn.json'):checks[record['former_file']]=record['checks']
 save(H/'checks.json',checks)
 missing=[]
 for f in (H/'certs').glob('*.jsonl'):
  for who,checker in {'M':R/'verification/highdim/sym5/check_sym5.py','F5':R/'verification/indep5/check_sym_F5.py'}.items():
   rec=checks.get(str(f),{}).get(who,{})
   if not (rec.get('result')=='PASS' and rec.get('sha256')==sha(f) and rec.get('checker_sha256')==sha(checker)):missing.append([str(f),who,rec.get('result','MISSING')])
 assert not missing,missing
 tree=load(H/'tree.json')
 for state in tree['states'].values():
  if state['status']=='PENDING':state.update(status='OPEN',reason='bounded continuation ended before a complete checked proof of this leaf')
 save(H/'tree.json',tree)
 for p,h in load(H/'source_hashes.json').items():assert sha(p)==h,('changed original',p)
 assert sha(R/'verification/highdim/sym5/check_sym5.py')==sha(H/'check_sym5.py'),'M checker differs from frozen snapshot'
 assert sha(H/'gen_sym_before_lookup.py')==sha(H.parent/'sym6/gen_sym.py')
 assert (H/'gen_sym.py').read_text().replace('residues7.get(unit*pow(3,-a,mod)%mod, ())','residues7[unit*pow(3,-a,mod)%mod]')==(H/'gen_sym_before_lookup.py').read_text()
 assert load(H/'lookup_controls.json')['result']=='PASS'
 for n in ('gen_precomputed.py','check_sym5.py','supply.json','audit_coverage.py','coverage_distinct.py','audit_orderings.py'):
  assert sha(H/n)==sha(H.parent/'sym6'/n),('changed snapshot',n)
 subprocess.run(['bash','-c','ulimit -v 8000000; python3 -I "$@"','sym7b-audit',str(H/'audit_peel.py')],check=True)
 subprocess.run(['bash','-c','ulimit -v 8000000; python3 -I "$@"','sym7b-order',str(H/'audit_orderings.py')],check=True)
 retained={str(f) for f in (H/'certs').glob('*.jsonl')}
 counts={who:dict(collections.Counter(v[who]['result'] for f,v in checks.items() if f in retained and who in v)) for who in ('M','F5')}
 audit=load(H/'coverage_audit.json');summary=load(H/'summary.json');summary['checker_counts']=counts;summary['all_retained_certificates_dual_checked']=True;summary['source_integrity']='PASS';save(H/'summary.json',summary)
 save(H/'verification_status.json',{'checker_counts':counts,'all_retained_certificates_dual_checked':True,'source_integrity':'PASS','coverage_result':audit['coverage_result'],'split_result':audit['split_result'],'ordering_result':load(H/'ordering_audit.json')['result'],'counts_by_k':summary['counts_by_k'],'withdrawn_candidates':load(H/'withdrawn.json') if (H/'withdrawn.json').exists() else []})
 manifest={str(p.relative_to(R)):sha(p) for p in H.rglob('*') if p.is_file() and p.name!='manifest.json' and not p.name.endswith('.tmp') and '__pycache__' not in p.parts}
 manifest['notes/highdim_sym7b.md']=sha(R/'notes/highdim_sym7b.md');save(H/'manifest.json',{'files':manifest,'source_integrity':'PASS','no_git_commit':True})
 status=load(H/'verification_status.json');status['withdrawn_candidate_count']=len(status.pop('withdrawn_candidates'));print(json.dumps(status))
if __name__=='__main__':main()

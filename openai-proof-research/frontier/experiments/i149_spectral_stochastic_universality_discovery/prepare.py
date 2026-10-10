"""One-time evidence preparation. Never imported or executed by verify.py."""
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i149_spectral_stochastic_universality_discovery'
E='frontier/experiments/i149_spectral_stochastic_universality_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
def obj(p):return json.loads((ROOT/p).read_bytes())
def put(p,d):(ROOT/p).write_text(json.dumps(d,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def row(p):
 b=(ROOT/p).read_bytes();return {'path':p,'bytes':len(b),'sha256':sha(b)}
def main():
 assert not (ROOT/S/'seal.json').exists()
 contexts=obj(S+'/context-manifest.json')
 reads=[]
 def passage(p,a=1,b=None,provenance='completed tool display'):
  z=row(p);ls=(ROOT/p).read_text().splitlines();b=len(ls) if b is None else b
  assert 1<=a<=b<=len(ls)
  z.update(start=a,end=b,total_lines=len(ls),ending=ls[b-1],passage_sha256=sha('\n'.join(ls[a-1:b]).encode()),provenance=provenance)
  if '/corpus/preprints/' in p:z['pinned_url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/'+p.split('/corpus/preprints/')[1]
  reads.append(z)
 passage(contexts[0]['decoded'],provenance='bounded displays completed the truncated middle; all four decoded fields')
 passage(contexts[1]['decoded'],provenance='initial head/tail display plus stored-output middle reads at characters 18000:43000 and 43000:48500')
 for p in ['AGENTS.md','sources/upstream.json'] :passage(p)
 for r in obj(S+'/selected-inventory.json'):
  p=r['local'];f=r['path']
  full=(('Fixed-energy' in f and f.endswith('01-introduction.tex')) or
        ('All-temperature' in f and f.endswith(('invariant-sk.tex','60-general.tex'))) or
        ('From-critical' in f and f.endswith(('01-introduction.tex','05-expansion.tex','06-sewing.tex','07-identification.tex'))))
  if full:passage(p)
  if 'From-critical' in f and f.endswith('02-inputs.tex'):
   passage(p,1,243);passage(p,912,1006)
 passage(S+'/external/gps.txt',2655,2810)
 put(S+'/read-manifest.json',{'convention':'Python splitlines; LF joined, no appended LF; PDF form feeds split lines','passages':reads,'all_required_recursive_context_read':False})
 put(S+'/reading-limitations.json',{
  'task_status':'INCOMPLETE','all_decoded_fields_mandatory_I146':True,
  'all_recursive_decoded_fields':False,'complete_context_records':[r['path'] for r in contexts[:2]],
  'incomplete_or_unread_context_records':[r['path'] for r in contexts[2:]],
  'truncated_attempts':['broad ledger scan','selected source inventory listing','I140 decoded record display','initial I143 context display (middle recovered)','initial I146 disjoint-range display (middle recovered)'],
  'not_claimed':['full I146 primary-proof comparison','full three-family operation and companion screen','complete prior-overlap audit','whole-corpus semantic reading'],
  'original_report_source':'full I146 report and finalized parent response supplied in the user task; immutable disk originals separately bound'})
 expressions={'pivotal':r'pivotal','dynamic':r'dynam\w*','replica':r'replica\w*','signed':r'signed','variance':r'variance','resolvent':r'resolvent\w*','edge':r'edge\w*','incomplete':r'incomplete','failure':r'FAIL\w*'}
 scope={}
 for r in reads:scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
 found={k:[] for k in expressions}
 for p,ns in sorted(scope.items()):
  ls=(ROOT/p).read_text().splitlines()
  for n in sorted(ns):
   for k,rx in expressions.items():
    for m in re.finditer(rx,ls[n-1],re.I):found[k].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
 put(S+'/focused-lexical.json',{'expressions':expressions,'occurrences':found,'counts':{k:len(v) for k,v in found.items()}})
 originals=[]
 for p in ['frontier/iterations/i146-effective-boundary-exclusion.md','frontier/experiments/i146-parent-verification.json']:
  r=row(p);snap=S+'/context/'+Path(p).name;(ROOT/snap).write_bytes((ROOT/p).read_bytes());r['snapshot']=snap;originals.append(r)
 put(S+'/originals.json',originals)
 put(S+'/research-disposition.json',{'task_status':'INCOMPLETE','accepted_count':8,'remaining_count':2,'nomination':None,'effective_boundary':'PARK','spatial_marked_dynamics':'PARK','original_I146_full_audit':'UNRESOLVED: required review incomplete','new_original_FAIL_found':None,'inherited_I122_literal':'FAIL preserved','inherited_I125_literal':'FAIL canonical inventory preserved','I125_adapter':'distinct PASS receipt retained, not rerun'})
 ns={'__name__':'i149_prepare_new_diagnostics'};p=E+'/diagnostics.py';exec(compile((ROOT/p).read_bytes(),p,'exec'),ns);put(E+'/diagnostics.json',ns['run']())
 ext=obj(S+'/retrievals.json')
 for r in ext:
  if r.get('path','').endswith('gps.pdf'):
   p=S+'/external/gps.txt';r.update(text_path=p,text_sha256=row(p)['sha256'],text_bytes=row(p)['bytes'],extraction_command=['pdftotext','-layout',r['path'],p],extraction_exit=0,splitlines=len((ROOT/p).read_text().splitlines()))
 put(S+'/retrievals.json',ext)
 flat={r['path']:r for r in obj('frontier/sources/i146_effective_boundary_exclusion/immutable-flat.json')['files']}
 se='frontier/sources/i146_effective_boundary_exclusion/seal.json'
 for r in obj(se)['files']:flat[r['path']]=r
 flat[se]=row(se)
 extra=['sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','AGENTS.md',
 'frontier/sources/i113_online_optimization_discovery/search-domain.json',
 'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json',
 'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json',
 'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl']
 for r in contexts:extra.extend([r['path'],r['snapshot'],r['decoded']])
 extra.extend(r['path'] for r in originals)
 for p in extra:
  z=row(p)
  if p in flat:assert flat[p]['sha256']==z['sha256']
  flat[p]=z
 for p in flat:assert not re.search(r'/(?:i|iteration)(147|148)[-_]',p)
 put(S+'/immutable-flat.json',{'files':[flat[p] for p in sorted(flat)]})
 print(json.dumps({'prepared':True,'flat_refs':len(flat),'passages':len(reads),'task_status':'INCOMPLETE'}))
if __name__=='__main__':main()

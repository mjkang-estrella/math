"""I35 integrity verifier. Reproduction and exact arithmetic, not independent proof review."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,urllib.parse,re,runpy
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i35_splitting_invariant_entropic_bias'; E=R/'frontier/experiments/i35_splitting_invariant_entropic_bias'; REPORT=R/'frontier/iterations/i35-splitting-invariant-entropic-bias.md'; C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'; PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'; SEAL=S/'artifact-seal.json';EXCLUDE={SEAL,E/'verification.json',E/'live-drift.json'}
def read(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def git(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def ident(p):b=p.read_bytes();return dict(path=str(p.relative_to(R)),sha256=sha(b),bytes=len(b))
def artifacts():return sorted([p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in EXCLUDE]+[REPORT])
def main():
 if '--seal' in sys.argv:SEAL.write_text(json.dumps(dict(scope='I35 assigned artifacts; seal and generated verification/drift outputs excluded',files=[ident(p) for p in artifacts()]),indent=2)+'\n')
 errors=[];drift=[]
 def need(ok,msg):
  if not ok:errors.append(msg)
 def check(row):
  p=R/row['path'];need(p.is_file(),'missing '+row['path'])
  if p.is_file():b=p.read_bytes();need(sha(b)==row['sha256'],'SHA '+row['path']);need(len(b)==row.get('bytes',len(b)),'bytes '+row['path'])
 seal=read(SEAL)
 for row in seal['files']:check(row)
 need({r['path'] for r in seal['files']}=={str(p.relative_to(R)) for p in artifacts()},'sealed inventory')
 ins=read(S/'input-manifest.json')
 for row in ins:
  check(dict(path=row['frozen'],sha256=row['sha256'],bytes=row['bytes']));p=R/row['path'];now=sha(p.read_bytes()) if p.exists() else None
  if now!=row['sha256']:
   permitted=row['path']=='frontier/TEN-FINDINGS.md';classification='shared-ledger drift' if permitted else 'mathematical input drift'
   if row['path'].endswith('-task.json') and p.exists():
    permitted=read(p).get('brief')==read(R/row['frozen']).get('brief');classification='shared task-status drift; brief unchanged' if permitted else 'task brief drift'
   drift.append(dict(path=row['path'],frozen_sha256=row['sha256'],live_sha256=now,classification=classification));need(permitted,'non-shared input drift '+row['path'])
 deps=read(S/'dependency-manifest.json')
 for row in deps:check(row)
 tree=read(R/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};cm=read(R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
 need(not tree['truncated'],'truncated tree');need(cm['pin']==PIN,'pin');need(len(cm['files'])==9340,'corpus count');need(sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree['tree'])==749,'manuscript count')
 catalogue=(R/'sources/CONTENTS.md').read_text();need(len(re.findall(r'\]\(preprints/[^)]+\)',catalogue))==719,'catalogue entries')
 for row in cm['files']:
  b=(C/row['path']).read_bytes();need(sha(b)==row['sha256'],'corpus SHA '+row['path']);need(git(b)==row['git_blob']==lookup[row['path']]['sha'],'corpus Git '+row['path']);need(urllib.parse.unquote(row['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'],'corpus URL '+row['path'])
 selected=read(S/'source-manifest.json')
 for row in selected:
  b=(C/row['path']).read_bytes();need(sha(b)==row['sha256'] and git(b)==row['git_blob'],'selected '+row['path']);need(urllib.parse.unquote(row['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'],'selected pinned URL')
 need(len(selected)==9,'nine BT texts')
 passages=read(S/'read-passages.json')
 for row in passages:
  lines=(R/row['path']).read_text().splitlines(keepends=True);a,b=row['start_line'],row['end_line'];need(1<=a<=b<=len(lines),'passage range');need(sha(''.join(lines[a-1:b]).encode())==row['sha256'],'passage SHA '+row['path'])
 contracts=read(S/'contracts.json')
 for row in contracts:check(row)
 primary=read(S/'fresh-retrievals.json')+read(S/'reused-primary.json')
 for row in primary:
  check(row)
  if 'extraction' in row:check(row['extraction']);need((R/row['path']).read_bytes().startswith(b'%PDF'),'PDF extraction')
 freshversions=read(S/'versions.json');expected={'dnwp':{'1'},'delalande':{'1','2'},'altschuler':{'1'},'lm':{'1','2','3'},'ruan':{'1'},'wang':{'1'},'bk':{'1','2'},'ford':{'1'}}
 for row in freshversions:
  key=Path(row['path']).name.split('-')[0]
  if key in expected:need(set(row['versions'])==expected[key],'version '+key)
  else:need(row['hal_version']=='hal-05616391v1','HAL version')
 d=read(E/'diagnostics.json');expected_counts={'entropy_chain_cases':24,'unequal_split_kernel_entries':96,'symmetric_Gibbs_KL_cases':32,'split_center_fiber_cases':20,'scalar_W2_checks':120,'exact_polygon_prefix_cases':13,'prefix_decompositions':128,'true_bias_enclosures':9,'floating_quadrature':False};need(d['summary']==expected_counts,'diagnostic counts')
 for z in d['split_center_fibers']:
  a,b=F(z['a']),F(z['b']);need(F(z['F1'])==b/4 and F(z['F2'])==b**3/4,'fiber formulas');need(F(z['V'])==a*b*b and F(z['B'])==b/4+a*b*b,'bias/variance formulas')
 for z in d['true_gibbs_bias_enclosures']:need(F(1,4)<F(z['true_B_over_epsilon_lower'])<F(z['true_B_over_epsilon_upper'])<1,'bias enclosure')
 for z in d['exact_polygon_prefix_geometry']:need(F(z['disk_slack'])>=0,'prefix disk')
 # Reproduce exact diagnostics locally and compare bytes. This writes only I35's own output.
 before=(E/'diagnostics.json').read_bytes();runpy.run_path(str(E/'diagnostics.py'),run_name='__main__');need((E/'diagnostics.json').read_bytes()==before,'deterministic diagnostics reproduction')
 report=REPORT.read_text();need(report.count('$$')%2==0,'display delimiters');need(not any(ord(c)<32 and c not in '\n\t' for c in report),'control characters');need('UB and Q remain **unproved and not refuted**' in report,'honest status');need('Transverse Gibbs redistribution lemma (unproved)' in report,'unpaid lemma');need(not list(S.rglob('__pycache__')) and not list(E.rglob('__pycache__')),'bytecode files')
 (E/'live-drift.json').write_text(json.dumps(drift,indent=2)+'\n');res=dict(status='FAIL' if errors else 'PASS',scope='Integrity, deterministic exact diagnostics and stated source interfaces; not independent analytic proof/significance certification',sealed_artifacts=len(seal['files']),frozen_inputs=len(ins),dependencies=len(deps),BT_texts=len(selected),read_passages=len(passages),contracts=len(contracts),fresh_primary_responses=9,reused_primary_responses=len(primary)-9,reused_PDF_extractions=sum('extraction' in x for x in primary),corpus_files=len(cm['files']),manuscripts=749,catalogue_entries=719,diagnostics=d['summary'],live_drift=drift,errors=errors)
 (E/'verification.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
 if errors:raise SystemExit(1)
if __name__=='__main__':main()

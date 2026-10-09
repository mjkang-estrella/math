"""I34 preservation/reproduction verifier, not an analytic-proof certificate."""
import pathlib,json,hashlib,sys,urllib.parse
from fractions import Fraction as F
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i34_target_uniform_brenier';E=R/'frontier/experiments/i34_target_uniform_brenier';REPORT=R/'frontier/iterations/i34-target-uniform-brenier.md';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus';PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb';SEAL=S/'artifact-seal.json';EXCLUDE={SEAL,E/'verification.json',E/'live-drift.json'}
def read(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def git(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def ident(p):b=p.read_bytes();return dict(path=str(p.relative_to(R)),sha256=sha(b),bytes=len(b))
def artifacts():return sorted([p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in EXCLUDE]+[REPORT])
def main():
 if '--seal' in sys.argv:SEAL.write_text(json.dumps(dict(scope='I34 assigned artifacts; seal and verifier/drift outputs excluded',files=[ident(p) for p in artifacts()]),indent=2)+'\n')
 errors=[];drift=[]
 def need(ok,msg):
  if not ok:errors.append(msg)
 def check(row):
  p=R/row['path'];need(p.is_file(),'missing '+row['path'])
  if p.is_file():
   b=p.read_bytes();need(sha(b)==row['sha256'],'hash '+row['path']);need(len(b)==row.get('bytes',len(b)),'size '+row['path'])
 seal=read(SEAL)
 for row in seal['files']:check(row)
 need({r['path'] for r in seal['files']}=={str(p.relative_to(R)) for p in artifacts()},'sealed artifact inventory')
 ins=read(S/'input-manifest.json')
 for row in ins:
  check(dict(path=row['frozen'],sha256=row['sha256'],bytes=row['bytes']))
  p=R/row['path'];now=sha(p.read_bytes()) if p.exists() else None
  if now!=row['sha256']:
   drift.append(dict(path=row['path'],frozen_sha256=row['sha256'],live_sha256=now,classification='shared-ledger drift' if row['path']=='frontier/TEN-FINDINGS.md' else 'non-ledger input drift'))
   need(row['path']=='frontier/TEN-FINDINGS.md','non-ledger input drift '+row['path'])
 deps=read(S/'dependency-manifest.json')
 for row in deps:check(row)
 tree=read(S/'inputs/sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};cm=read(R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
 need(not tree['truncated'],'complete tree required');need(cm['pin']==PIN,'corpus pin');need(len(cm['files'])==9340,'corpus size')
 need(sum(r['type']=='tree' and r['path'].count('/')==1 for r in tree['tree'])==749,'749 manuscript inventory')
 for row in cm['files']:
  b=(C/row['path']).read_bytes();need(sha(b)==row['sha256'],'corpus SHA '+row['path']);need(git(b)==row['git_blob']==lookup[row['path']]['sha'],'corpus Git '+row['path']);need(urllib.parse.unquote(row['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'],'raw pinned URL '+row['path'])
 selected=read(S/'source-manifest.json')
 for row in selected:
  b=(C/row['path']).read_bytes();need(sha(b)==row['sha256'] and git(b)==row['git_blob'],'selected '+row['path'])
 passages=read(S/'read-passages.json')
 for row in passages:
  lines=(R/row['path']).read_text().splitlines(keepends=True);a,b=row['start_line'],row['end_line'];need(1<=a<=b<=len(lines),'passage range '+row['path']);need(sha(''.join(lines[a-1:b]).encode())==row['sha256'],'passage hash '+row['path'])
 contracts=read(S/'contracts.json')
 for row in contracts:check(row)
 primary=[]
 for mp in [S/'fresh-retrievals.json',S/'fresh-extra.json']+sorted((R/'frontier/sources/i33_density_robust_brenier/literature').glob('manifest*.json')):
  for row in read(mp):
   check(row)
   if 'extraction' in row:check(row['extraction']);need((R/row['path']).read_bytes().startswith(b'%PDF'),'non-PDF extraction '+row['path'])
   primary.append(row)
 d=read(E/'diagnostics.json');need(d['summary']['exact_audit_cases']==25,'audit count');need(d['summary']['exact_map_pairs']==11,'growing comparisons');need(d['summary']['exact_split_center_pairs']==12,'split comparisons');need(d['summary']['exact_facet_coefficients']==197,'facet count')
 for z in d['audit_cases']:
  a,k=F(z['a']),F(z['kappa']);need(F(z['moment_ratio'])==a+k*k/(9*a),'moment audit')
 for z in d['growing_diagrams']:
  n=z['n'];err,cost=F(z['D2']),F(z['W2_squared']);need(0<cost<=err,'target transport cost');need(F(z['D6_over_W2_squared'])==err**3/cost,'Q diagnostic');need(F(z['zigzag_path_cost'])==8*n+F(2,n),'zigzag formula');need(F(z['smallest_cross_flow'])>0,'realized directed path')
 for z in d['split_center_cases']:
  a,b=F(z['a']),F(z['b']);need(F(z['D2'])==b/4+a*b*b,'split-center map distance');need(F(z['W2_squared'])==F(z['variance'])==a*b*b,'split-center cost and variance')
 need(d['gluing']=={'source_motion_lower_squared':'233/1024','D2_at_lambda1':'31/20','W2_squared_at_lambda1':'4/5','repair_gap_at_lambda1':'7/40'},'gluing exact values')
 text=REPORT.read_text();need(text.count('$$')%2==0,'display delimiters');need(not any(ord(c)<32 and c not in '\n\t' for c in text),'control character');need('Q remains **unproved and not refuted**' in text,'honest Q status')
 need(len(selected)==9,'all nine BT texts');need(len(contracts)==15,'source contracts');need(not list(S.rglob('__pycache__')),'source bytecode cache')
 (E/'live-drift.json').write_text(json.dumps(drift,indent=2)+'\n')
 result=dict(status='PASS' if not errors else 'FAIL',scope='Frozen integrity and exact diagnostics, not analytic proof or significance certification',sealed_artifacts=len(seal['files']),frozen_inputs=len(ins),unchanged_dependencies=len(deps),selected_BT_sources=len(selected),contracts=len(contracts),read_passages=len(passages),corpus_files=len(cm['files']),manuscripts=749,primary_responses=len(primary),primary_extractions=sum('extraction' in r for r in primary),diagnostics=d['summary'],live_drift=drift,errors=errors)
 (E/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if errors:raise SystemExit(1)
if __name__=='__main__':main()

"""Acquisition of exact content search; replay implementation in verify.py."""
from pathlib import Path
import json, subprocess, hashlib,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i83_catalan_finite_measure'
rows=json.loads((R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json').read_text())
pattern=r"Catalan|irrationality.{0,24}(measure|exponent)|holonom|G.function|linear.{0,16}independence.{0,30}(period|zeta)|L\(2.{0,30}(chi|χ)"
def search(files,pat):
 out=[]
 for i in range(0,len(files),150):
  p=subprocess.run(['rg','--json','--text','--ignore-case',pat,*files[i:i+150]],cwd=R,capture_output=True);assert p.returncode in (0,1),p.stderr
  for line in p.stdout.split(b'\n'):
   if not line:continue
   o=json.loads(line)
   if o['type']=='match':
    d=o['data'];out.append({'path':d['path']['text'],'line':d['line_number'],'text':d['lines']['text']})
 return sorted(out,key=lambda x:(x['path'],x['line'],x['text']))
files=[x['local'] for x in rows]
history=[]
for base in ['proposals','reviews','frontier/iterations','frontier/reviews','frontier/findings']:
 history += [str(p.relative_to(R)) for p in (R/base).glob('*.md') if 'i83-' not in p.name]
history += [str(p.relative_to(R)) for p in (S/'ledgers').rglob('*.md')]
for name,fl,pat in [('corpus',files,pattern),('history',sorted(history),r'Catalan|irrationality|holonom|Diophantine|cofactor|adjugate')]:
 (S/(name+'-search-definition.json')).write_text(json.dumps({'files':fl,'pattern':pat,'flags':['--json','--text','--ignore-case'],'record_format':'sorted list of path,line,text; LF only JSON parsing preserves PDF formfeeds'},indent=2)+'\n')
 out=search(fl,pat);(S/(name+'-search-multiset.json')).write_text(json.dumps(out,indent=2)+'\n');print(name,len(fl),len(out))
 if name=='corpus':
  mp={x['local']:x['path'] for x in rows};families={}
  for x in out:
   f=mp[x['path']].split('/')[1];families[f]=families.get(f,0)+1
  (S/'matched-families.json').write_text(json.dumps(families,indent=2,sort_keys=True)+'\n');print(json.dumps(families,indent=2))

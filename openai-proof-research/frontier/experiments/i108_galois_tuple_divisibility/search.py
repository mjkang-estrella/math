"""Preparation only: exact full-domain lexical occurrence multisets."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i108_galois_tuple_divisibility'
DOMAIN='frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'
QUERIES={
 'companions':r'Alperin|Donovan|Galois.{0,50}weight|weight.{0,50}Galois|functorial.{0,30}equivalen',
 'bridge':r'marked.cover|small.orbit|Teichm.{0,10}ller|twisted.{0,40}(tuple|trace|commutator)|exceptional.{0,30}(ramif|branch)|minimal.field|permutation.{0,20}(summand|lattice)',
}
def occurrences():
 result={k:[] for k in QUERIES};pats={k:re.compile(v,re.I) for k,v in QUERIES.items()}
 for row in json.loads((ROOT/DOMAIN).read_text()):
  for ln,line in enumerate((ROOT/row['local']).read_bytes().decode('utf-8',errors='replace').splitlines(),1):
   for name,pat in pats.items():
    for m in pat.finditer(line):result[name].append({'path':row['path'],'line':ln,'span':list(m.span()),'match':m.group(),'text':line})
 for rows in result.values():rows.sort(key=lambda r:(r['path'],r['line'],r['span']))
 return result
def encoded(rows):return ''.join(json.dumps(r,sort_keys=True,ensure_ascii=False)+'\n' for r in rows).encode()
if __name__=='__main__':
 (S/'queries.json').write_text(json.dumps({'domain':DOMAIN,'queries':QUERIES,'flags':['IGNORECASE'],'line_convention':'UTF-8 errors=replace; str.splitlines 1-based; character spans 0-based half-open'},indent=2)+'\n')
 result=occurrences()
 for name,rows in result.items():(S/('search-'+name+'.jsonl')).write_bytes(encoded(rows))
 summary={name:{'occurrences':len(rows),'families':sorted({r['path'].split('/')[1] for r in rows})} for name,rows in result.items()}
 (S/'search-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 print(json.dumps({k:{'occurrences':v['occurrences'],'families':len(v['families'])} for k,v in summary.items()}))

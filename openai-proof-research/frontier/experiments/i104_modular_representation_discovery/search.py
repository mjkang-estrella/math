"""Offline lexical-search preparation. No claim of full semantic reading."""
import hashlib, json, re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'frontier/sources/i104_modular_representation_discovery'
DOMAIN='frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'
QUERIES={
 'companions': r'Donovan|Alperin|Brou[eé]|Verlinde|restricted.tilting|tensor.saturation|Galois.{0,50}weight|weight.{0,50}Galois',
 'mechanisms': r'twisted.{0,40}(cocenter|commutator|tuple)|cocenter.{0,50}(Galois|Frobenius)|minimal.field|based.{0,25}(Morita|Frobenius)|equivariant.{0,30}(weight|bijection)',
 'screens': r'Fulton|multiplicity.one|moderate.growth|ramification|stopping.certificate|effective.{0,30}(Donovan|Morita)',
}
domain=json.loads((ROOT/DOMAIN).read_text())
refs=[]
for f in ['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md',DOMAIN]:
 refs.append({'path':f,'sha256':hashlib.sha256((ROOT/f).read_bytes()).hexdigest()})
(BASE/'immutable-references.json').write_text(json.dumps(refs,indent=2)+'\n')
(BASE/'queries.json').write_text(json.dumps({'domain':DOMAIN,'flags':['IGNORECASE'],'line_convention':'UTF-8 errors=replace, str.splitlines(), 1-based; spans are 0-based character half-open offsets','queries':QUERIES},indent=2)+'\n')
outs={name:[] for name in QUERIES}
patterns={n:re.compile(p,re.I) for n,p in QUERIES.items()}
for row in domain:
 text=(ROOT/row['local']).read_bytes().decode('utf-8',errors='replace')
 for ln,line in enumerate(text.splitlines(),1):
  for name,pat in patterns.items():
   for m in pat.finditer(line):outs[name].append({'path':row['path'],'line':ln,'span':list(m.span()),'match':m.group(),'text':line})
for name,rows in outs.items():
 rows.sort(key=lambda x:(x['path'],x['line'],x['span']))
 (BASE/('search-'+name+'.jsonl')).write_text(''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in rows))
 print(name,len(rows),len({x['path'].split('/')[1] for x in rows}))
titles=sorted({x['path'].split('/')[1] for x in domain})
pat=re.compile(r'block|brauer|brou|alperin|donovan|tensor|verlinde|saturat|tilting|picard|frobenius|modular',re.I)
(BASE/'title-screen.json').write_text(json.dumps({'total_titles':len(titles),'pattern':pat.pattern,'matches':[x for x in titles if pat.search(x)]},indent=2)+'\n')

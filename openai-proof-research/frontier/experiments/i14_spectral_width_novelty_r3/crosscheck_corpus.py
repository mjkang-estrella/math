"""Second whole-corpus search: alternate spelling and manuscript-level co-occurrence."""
import json,pathlib,re,collections
base=pathlib.Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
grouped=collections.defaultdict(list)
for p in base.rglob('*'):
    if p.is_file(): grouped[p.relative_to(base).parts[1]].append(p)
hits={}
for title,files in grouped.items():
    text=re.sub(r'\s+',' ',' '.join(p.read_text(errors='replace') for p in files))
    reasons=[]
    if re.search(r'uryso(?:h)?n|codimension[ -]two width|graph[ -]width',text,re.I): reasons.append('width')
    if re.search(r'scalar[\s~-]+curvature',text,re.I) and re.search(r'spectral|Schr[oö]|\\Delta|laplacia',text,re.I): reasons.append('scalar+operator')
    if reasons: hits[title]=reasons
pathlib.Path(__file__).with_name('corpus-crosscheck.json').write_text(json.dumps(hits,indent=2)+'\n')
print('Scanned',len(grouped),'manuscripts;',len(hits),'broad matches.')

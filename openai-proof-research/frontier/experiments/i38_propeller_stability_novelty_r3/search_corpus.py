from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i38_propeller_stability_novelty_r3'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def run():
 m=json.loads((C.parent/'corpus-manifest.json').read_text());t=json.loads((R/'sources/preprints-tree.json').read_text())['tree']
 patterns={'propeller':r'propeller','centroid_stability':r'(centroid|first.moment|barycent).{0,100}(stabil|deficit|remainder)|(stabil|deficit|remainder).{0,100}(centroid|first.moment|barycent)','gaussian_max':r'Gaussian.{0,90}(maxim|width|support.function)|(maxim|width|support.function).{0,90}Gaussian','support_escape':r'(countab|trace|support).{0,70}(compact|escape|stability)|(compact|escape).{0,70}(countab|trace|support)'}
 out={'pin':m['pin'],'tree_entries':len(t),'manuscripts':len({e['path'].split('/')[1] for e in t if e['path'].startswith('preprints/') and len(e['path'].split('/'))>1}),'files':len(m['files']),'bytes':0,'patterns':patterns,'hits':{k:[] for k in patterns},'inventory_titles':[]}
 for row in m['files']:
  b=(C/row['path']).read_bytes();assert len(b)==row['bytes'];assert hashlib.sha256(b).hexdigest()==row['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'];out['bytes']+=len(b)
  lines=b.decode('utf8',errors='replace').splitlines()
  for key,pat in patterns.items():
   rex=re.compile(pat,re.I)
   hits=[{'line':i,'text':l} for i,l in enumerate(lines,1) if rex.search(l)]
   if hits:out['hits'][key].append({'path':row['path'],'sha256':row['sha256'],'matches':hits})
 out['inventory_titles']=sorted({e['path'].split('/')[1] for e in t if re.search(r'(Gaussian|Propeller|Noise-Stability|Mean-Width|Simplex|Partition)',e['path'].split('/')[1],re.I)})
 selected=[x for x in m['files'] if '/The-Gaussian-Propeller-Bound-in-Every-Dimension-' in x['path']]
 return out,selected
if __name__=='__main__':
 out,selected=run();(S/'corpus-search.json').write_text(json.dumps(out,indent=2)+'\n');(S/'selected-pinned.json').write_text(json.dumps(selected,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k not in ['hits','patterns']},indent=2));print({k:len(v) for k,v in out['hits'].items()})

from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i17_six_point_ramsey_novelty_r3'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b): return hashlib.sha256(b).hexdigest()
def run():
    tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text())
    assert not tree['truncated']
    entries=tree['tree']; assert len({e['path'] for e in entries})==len(entries)
    index={('preprints/'+e['path'] if not e['path'].startswith('preprints/') else e['path']):e for e in entries}
    manifest=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
    patterns={
      'six_circle':r'(six|6|hexagon).{0,140}(Ramsey|concyclic|spherical|circle)|(Ramsey|concyclic|spherical|circle).{0,140}(six|hexagon)',
      'euclidean_ramsey':r'Euclidean.{0,30}Ramsey|Ramsey.{0,30}(configuration|spherical|circle|cyclic)',
      'certificate':r'(bilinear|bidegree|M.bi[u]?s|fractional.linear|adjugate).{0,180}(interpol|Ramsey|tensor)|(Ramsey|tensor).{0,180}(bilinear|bidegree|M.bi[u]?s|fractional.linear|adjugate)',
      'negative_boundary':r'(seven|heptagon).{0,120}(Ramsey|circle)|(Ramsey|circle).{0,120}(seven|heptagon)',
    }
    hits={k:[] for k in patterns}; verified=[]
    for item in manifest['files']:
        p=C/item['path']; b=p.read_bytes(); h=sha(b); git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert h==item['sha256'] and len(b)==item['bytes'] and git==item['git_blob']==index[item['path']]['sha'],item['path']
        verified.append({'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':h,'git_blob':git})
        t=re.sub(r'\s+',' ',b.decode(errors='replace'))
        for key,pat in patterns.items():
            matches=[{'start':m.start(),'passage':t[max(0,m.start()-160):min(len(t),m.end()+260)]} for m in re.finditer(pat,t,re.I)]
            if matches: hits[key].append({'path':item['path'],'matches':matches})
    manuscripts=sorted({p.split('/')[1] for p in index if '/' in p})
    result={'entries':len(entries),'blobs':sum(e['type']=='blob' for e in entries),'manuscripts':manuscripts,'text_files':len(verified),'bytes':sum(x['bytes'] for x in verified),'patterns':patterns,'hits':hits,'verified_dependencies':verified,'limitation':'Full text screen, not full mathematical reading. Absence is not novelty evidence.'}
    (S/'corpus-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'entries':len(entries),'manuscripts':len(manuscripts),'verified':len(verified),'hit_files':{k:len(v) for k,v in hits.items()},'euclidean_manuscripts':sorted({x['path'].split('/')[1] for x in hits['euclidean_ramsey']})},indent=2))
if __name__=='__main__':run()

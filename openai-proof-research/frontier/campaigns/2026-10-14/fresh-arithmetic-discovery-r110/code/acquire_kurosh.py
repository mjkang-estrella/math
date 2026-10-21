import hashlib,json,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def main():
    raw=(PROJECT/'sources/preprints-tree.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(raw)['tree']; assert len(tree)==13223
    rows=[]
    for v in tree:
        path=v['path']
        if 'Kurosh' not in path or not path.endswith(('.tex','.bib')):continue
        url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{path}'
        b=urllib.request.urlopen(url,timeout=40).read()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert len(b)==v['size'] and blob==v['sha'],path
        dest=ROOT/'private/source'/path
        dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
        rows.append({'canonical_path':path,'url':url,'bytes':len(b),'git_blob_sha1':blob,'sha256':hashlib.sha256(b).hexdigest(),'local':str(dest.relative_to(ROOT))})
    (ROOT/'private/source/kurosh-metadata.json').write_text(json.dumps(rows,indent=2))
    print('Authenticated',len(rows),'pinned bodies; acquisition is not a reading claim.')
if __name__=='__main__':main()

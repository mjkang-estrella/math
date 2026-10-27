#!/usr/bin/env python3
"""Deterministic manifest-only release archives; no prebuilt proof objects."""
from pathlib import Path
import hashlib
import io
import json
import zipfile

ROOT = Path(__file__).resolve().parents[2]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def archive_bytes(slug, payload):
    out = io.BytesIO()
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name,data in sorted(payload.items()):
            info=zipfile.ZipInfo(slug+'/'+name,(2026,10,27,0,0,0))
            info.external_attr=0o100644 << 16
            z.writestr(info,data,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    return out.getvalue()

def main():
    for slug,count,decls,mods in [('cstar-smale-unbounded',27,49,5),
                                 ('cstar-bieberbach',25,28,4)]:
        candidate=ROOT/'candidates'/slug
        packet=ROOT/'candidate-packets'/(slug+'-proof.zip')
        extract=ROOT/'build'/(slug+'-packet-audit-v1')
        assert not packet.exists() and not extract.exists()
        frozen=json.loads((candidate/'reviewed-parent-hashes.json').read_text())
        locations=json.loads((candidate/'reviewed-file-locations.json').read_text())
        assert len(frozen)==count and set(frozen)==set(locations)
        for name,digest in frozen.items():
            assert sha((candidate/locations[name]).read_bytes())==digest,name
        audit_bytes=(candidate/'verification/parent-audit.json').read_bytes()
        assert audit_bytes==(candidate/'verification/independent-audit.json').read_bytes()
        audit=json.loads(audit_bytes)
        assert audit['status']=='PASS' and audit['declarations']==decls
        assert len(audit['modules'])==mods
        for module in audit['modules']:
            assert sha((candidate/module['path']).read_bytes())==module['sha256']
        qa=json.loads((candidate/'paper-qa.json').read_text())
        assert qa['pages']==2 and qa['build_issues']==[]
        assert qa['parent_release_all_pages_read'] is True
        assert qa['tex_sha256']==sha((candidate/'main.tex').read_bytes())
        assert qa['pdf_sha256']==sha((candidate/'paper.pdf').read_bytes())
        payload={}
        for path in sorted(candidate.rglob('*')):
            if not path.is_file():continue
            name=path.relative_to(candidate)
            if name.parts[0]=='build' or '__pycache__' in name.parts:continue
            if str(name) in ['acceptance.json','MANIFEST.json']:continue
            assert path.suffix not in ['.olean','.ilean','.pyc'],name
            payload[str(name)]=path.read_bytes()
        manifest={name:sha(data) for name,data in payload.items()}
        payload['MANIFEST.json']=(json.dumps(manifest,indent=2)+'\n').encode()
        data=archive_bytes(slug,payload)
        assert data==archive_bytes(slug,payload),'Non-deterministic archive'
        packet.write_bytes(data)
        with zipfile.ZipFile(packet) as z:
            assert z.testzip() is None
            assert set(z.namelist())==set(slug+'/'+n for n in payload)
            for name,blob in payload.items():assert z.read(slug+'/'+name)==blob
            z.extractall(extract)
        dest=extract/slug
        for name,digest in manifest.items():assert sha((dest/name).read_bytes())==digest,name
        result={'status':'PASS archive/determinism/readback; extracted Lean replay pending',
                'packet':str(packet.relative_to(ROOT)),'sha256':sha(data),
                'members':len(payload),'payload_files':len(manifest),
                'extracted':str(dest.relative_to(ROOT))}
        (extract/'readback.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result))

if __name__=='__main__':main()

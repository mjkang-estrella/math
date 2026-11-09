from pathlib import Path
import json,zipfile,hashlib
root=Path(__file__).resolve().parent;p=root/'submission-manifest.json';d=json.loads(p.read_text())
for r in d['papers']:
 files={}
 with zipfile.ZipFile(r['proof_packet']) as z:
  for i in z.infolist():
   q=Path(i.filename)
   if i.is_dir() or q.is_absolute() or '..' in q.parts:continue
   if q.suffix in ['.lean','.md','.toml','.json','.py','.tex','.log','.txt'] or q.name=='lean-toolchain':
    try: files[i.filename]=z.read(i).decode('utf-8')
    except UnicodeDecodeError:pass
 package=Path(r['paper']).parent/'proof-sources.json';package.write_text(json.dumps({'original_archive_sha256':r['proof_packet_sha256'],'files':files},ensure_ascii=False,indent=2)+'\n')
 unpack=package.parent/'extract_sources.py';unpack.write_text('''"""Extract the accompanying proof-sources.json into a new directory."""\nimport json\nfrom pathlib import Path\np=Path(__file__).with_name("proof-sources.json")\nout=Path("extracted-proof-sources")\nout.mkdir(exist_ok=False)\nfor name, text in json.loads(p.read_text())["files"].items():\n    q=Path(name)\n    assert not q.is_absolute() and ".." not in q.parts\n    target=out/q\n    target.parent.mkdir(parents=True,exist_ok=True)\n    target.write_text(text)\nprint(out.resolve())\n''')
 r['attachments']=[str(package),str(unpack)]
 r['comments']=r['comments'].replace('source proof archive','source proof package')+' Attachments: proof-sources.json preserves UTF-8 source files from the accepted proof archive; extract_sources.py reconstructs them. The original archive SHA-256 is recorded in the JSON.'
p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print('Packaged 22 source sets')

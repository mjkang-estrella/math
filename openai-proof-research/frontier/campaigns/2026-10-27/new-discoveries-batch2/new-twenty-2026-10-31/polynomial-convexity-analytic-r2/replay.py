#!/usr/bin/env python3
"""Rebuild partial source-only certificate, writing only to a fresh --output directory."""
import argparse,hashlib,importlib.util,json,os,pathlib,stat,sys,zipfile
sys.dont_write_bytecode=True
ap=argparse.ArgumentParser(); ap.add_argument('--archive',required=True); ap.add_argument('--output',required=True)
a=ap.parse_args(); archive=pathlib.Path(a.archive).resolve(); out=pathlib.Path(a.output).absolute()
if out.exists() or out.is_symlink(): raise SystemExit('output must not exist')
if not out.parent.is_dir() or out.parent.resolve()!=out.parent: raise SystemExit('output parent must be a real resolved directory')
with zipfile.ZipFile(archive) as z:
    infos=z.infolist(); names=[i.filename for i in infos]
    if len(names)!=len(set(names)) or sum(i.file_size for i in infos)>2_000_000: raise SystemExit('unsafe archive')
    for i in infos:
        q=pathlib.PurePosixPath(i.filename)
        if q.is_absolute() or '..' in q.parts or i.is_dir() or stat.S_ISLNK(i.external_attr>>16): raise SystemExit('unsafe entry')
    manifest=json.loads(z.read('manifest.json'))
    if set(names)!=set(manifest)|{'manifest.json'}: raise SystemExit('manifest file set mismatch')
    for name,h in manifest.items():
        if hashlib.sha256(z.read(name)).hexdigest()!=h: raise SystemExit('hash mismatch '+name)
    out.mkdir(); extracted=out/'extracted'; extracted.mkdir()
    for i in infos:
        dest=extracted/i.filename;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(i))
spec=importlib.util.spec_from_file_location('bounded_build',extracted/'run_build.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
ok=m.build(extracted/'src',out/'build')
(out/'replay-result.json').write_text(json.dumps({'success':ok,'scope':'partial helpers only; conjecture not proved','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'manifest_files':len(manifest),'environment':'fresh output plus pinned dependency package caches only'},indent=2))
raise SystemExit(0 if ok else 1)

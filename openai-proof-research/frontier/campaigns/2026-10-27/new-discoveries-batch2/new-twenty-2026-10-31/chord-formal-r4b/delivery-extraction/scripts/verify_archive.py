from pathlib import Path
import zipfile,hashlib,json,stat
R=Path(__file__).resolve().parent.parent
out=R/'delivery-extraction'
out.mkdir(exist_ok=False)
with zipfile.ZipFile(R/'chord-comb4-source.zip') as z:
    for x in z.infolist():
        p=Path(x.filename)
        assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(x.external_attr>>16)
        assert not x.filename.startswith(('build/','logs/','cache/','tmp/'))
    z.extractall(out)
mods=(R/'modules.txt').read_text().splitlines()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (out/'modules.txt').read_bytes()==(R/'fresh-extraction/modules.txt').read_bytes()
for m in mods:
    assert h(out/'src'/f'{m}.lean')==h(R/'fresh-extraction/src'/f'{m}.lean')
res=dict(archive_sha256=h(R/'chord-comb4-source.zip'),safe_paths=True,source_only=True,
         modules=len(mods),final_archive_sources_equal_fresh_replay=True)
(R/'certificate.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res))

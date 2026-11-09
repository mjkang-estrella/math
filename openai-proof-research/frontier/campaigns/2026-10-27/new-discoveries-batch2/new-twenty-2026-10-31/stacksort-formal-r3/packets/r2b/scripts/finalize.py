from pathlib import Path
import json,hashlib,zipfile
root=Path(__file__).resolve().parent.parent
r=json.loads((root/'results.json').read_text())
f=json.loads((root/'fresh-extraction/results.json').read_text())
assert r['modules']==f['modules']
archive=root/'stacksort-seeds2-source.zip'
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        assert not name.startswith('/') and '..' not in Path(name).parts
        assert z.read(name)==(root/'fresh-extraction'/name).read_bytes(),name
assert f['validation']['strict_build_and_explicit_module_checkers']
assert f['audit']['closure_equals_audited_set']
r['validation']['fresh_replay']={'directory':'fresh-extraction','source_archive_byte_identical':True,
 'safe_paths':True,'empty_extraction':True,'strict_serial_build':True,'all_module_checkers':True,
 'module_count':len(f['modules']),'audit':f['audit'],'results':'fresh-extraction/results.json',
 'logs':'fresh-extraction/logs'}
r['archive_sha256']=hashlib.sha256(archive.read_bytes()).hexdigest()
r['peak_recorded_single_command_rss_KiB']=max(r['peak_recorded_single_command_rss_KiB'],f['peak_recorded_single_command_rss_KiB'])
(root/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('Fresh exact archive replay verified:',len(f['modules']),'modules;',r['archive_sha256'])

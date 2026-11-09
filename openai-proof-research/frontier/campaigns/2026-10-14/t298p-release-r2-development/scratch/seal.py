from pathlib import Path
import hashlib,json
p=Path(__file__).absolute().parent.parent
ns={'__file__':str(p/'release.py'),'__name__':'seal_import'}
exec(compile((p/'release.py').read_bytes(),str(p/'release.py'),'exec'),ns)
files,dirs=ns['inventory'](p,exclude=('scratch',))
files.pop('IMPLEMENTATION-MANIFEST.json',None)
raw=ns['encoded']({'schema':'t298p-release-implementation-v1','kind':'PREPARATION_ONLY','accepted':False,'published':False,'count_change':0,'excluded_top_level_directories':['scratch'],'directories':dirs,'files':{n:ns['record'](b) for n,b in sorted(files.items())}})
(p/'IMPLEMENTATION-MANIFEST.json').write_bytes(raw)
print(hashlib.sha256(raw).hexdigest())

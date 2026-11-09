import pathlib,zipfile,hashlib,json
root=pathlib.Path.cwd()
files=sorted(list(root.glob('src/*.lean'))+list(root.glob('scripts/*'))+list(root.glob('*.md'))+[root/'modules.txt',root/'frozen-before.sha256'])
with zipfile.ZipFile(root/'chord-source.zip','w',zipfile.ZIP_DEFLATED) as z:
    for p in files:
        if not p.is_file(): continue
        name=p.relative_to(root).as_posix()
        assert not name.startswith('/') and '..' not in pathlib.PurePosixPath(name).parts
        z.write(p,name)
extract=root/'fresh-extraction'
extract.mkdir(exist_ok=False)
with zipfile.ZipFile(root/'chord-source.zip') as z:
    for name in z.namelist():
        assert not name.startswith('/') and '..' not in pathlib.PurePosixPath(name).parts
    z.extractall(extract)
for p in (extract/'scripts').glob('*.sh'): p.chmod(0o755)
print(json.dumps({'sha256':hashlib.sha256((root/'chord-source.zip').read_bytes()).hexdigest(),'members':len(files)}))

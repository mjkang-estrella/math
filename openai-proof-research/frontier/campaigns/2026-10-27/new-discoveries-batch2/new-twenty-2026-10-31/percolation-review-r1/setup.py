import pathlib,hashlib,json,zipfile,shutil
L=pathlib.Path.cwd(); B=L.parent; D=B/'expanded-corpus-r164'; F=B/'percolation-formal-r1'
files=[D/'CANDIDATE.md',D/'SUMMARY.md',D/'results.json',F/'source-only.zip',F/'module-order.txt',F/'PROOF.md',F/'STATEMENT-CORRESPONDENCE.md']+list((D/'outputs').glob('percolation*'))+[D/'outputs/lrat-check.json',D/'sources/333709.pdf']+list((F/'src').glob('*.lean'))
h={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files if p.is_file()}
(L/'inputs-before.json').write_text(json.dumps(h,indent=2))
z=zipfile.ZipFile(F/'source-only.zip'); out=L/'extracted';out.mkdir()
for i in z.infolist():
 p=pathlib.PurePosixPath(i.filename)
 assert not p.is_absolute() and '..' not in p.parts and not (i.external_attr>>16)&0o170000==0o120000
 assert i.file_size<10000000
 if not i.is_dir():
  dest=out.joinpath(*p.parts);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(i))
print('archive',h[str(F/'source-only.zip')]); print('\n'.join(z.namelist()))
shutil.copyfile(D/'sources/333709.pdf',L/'source.pdf')

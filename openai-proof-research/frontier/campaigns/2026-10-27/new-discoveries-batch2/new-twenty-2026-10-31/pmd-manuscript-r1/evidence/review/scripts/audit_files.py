import pathlib,tarfile,hashlib,json,re
L=pathlib.Path(__file__).resolve().parents[1];S=L.parent/'expanded-corpus-r143'
with tarfile.open(S/'lean-packet.tar.gz') as t:
 for x in t:
  p=pathlib.PurePosixPath(x.name)
  assert not p.is_absolute() and '..' not in p.parts and (x.isfile() or x.isdir()),repr(x)
  print('SAFE_ARCHIVE_MEMBER',x.name)
for p in ['TorusPMD.lean','AuditAll.lean','Audit.lean']:
 a=hashlib.sha256((S/'packet'/p).read_bytes()).hexdigest();b=hashlib.sha256((L/'extracted'/p).read_bytes()).hexdigest();assert a==b
 assert (S/p).read_bytes()==(L/'extracted'/p).read_bytes()
 print('MATCHED_SOURCE',p,a)
text=(L/'extracted/TorusPMD.lean').read_text()
assert not re.search(r'\b(unsafe|partial|axiom|sorry|admit|native_decide|implemented_by|extern)\b|_unsafe_rec',text)
print('SOURCE_TOKEN_AUDIT PASS')
raw=json.loads((S/'raw/366974.jsonl').read_text());d=next(d for d in json.loads((S/'results.json').read_text()).values() if d['mathdb_id']==366974)
assert raw['statement']==d['statement'];print('RAW_RESULTS_STATEMENT_MATCH PASS')
for p in (L/'downloads').rglob('*'):
 if p.is_file():print('DOWNLOAD_SHA256',hashlib.sha256(p.read_bytes()).hexdigest(),p.relative_to(L))

import tarfile,pathlib,hashlib
base=pathlib.Path(__file__).resolve().parents[1]
p=base.parent/'expanded-corpus-r158/lean-packet.tar.gz'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200'
with tarfile.open(p,'r:gz') as t:
    ms=t.getmembers()
    assert {m.name for m in ms}=={'Definitions.lean','Witness.lean','Audit.lean'}
    for m in ms:
        assert m.isfile() and m.size<100000 and '/' not in m.name
        q=base/'packet'/m.name
        with q.open('xb') as f: f.write(t.extractfile(m).read())
        print(m.name,hashlib.sha256(q.read_bytes()).hexdigest())

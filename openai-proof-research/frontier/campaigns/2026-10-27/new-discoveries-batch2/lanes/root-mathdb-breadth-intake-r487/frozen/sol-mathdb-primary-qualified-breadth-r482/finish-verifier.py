import pathlib
O=pathlib.Path(__file__).resolve().parent;p=O/'verify.py';s=p.read_text();s=s.replace("ds=load(O/'dispositions.json');assert", "ds=load(O/'dispositions.json');assert")
s=s.replace("found={}\n", "baseline=load(I/'coverage-delta.json');assert len(baseline)==3333 and not set(map(str,ids))&set(baseline)\n assert load(I/'adjudications.json')['372627']['credit']==0\n assert load(L/'root-mathdb-cayley-review-intake-r363'/'disposition.json')['mathdb_id']==364119\n if '--corrupt-statement' in sys.argv:ds[0]['statement_utf8_sha256']='0'*64\n found={}\n")
p.write_text(s)

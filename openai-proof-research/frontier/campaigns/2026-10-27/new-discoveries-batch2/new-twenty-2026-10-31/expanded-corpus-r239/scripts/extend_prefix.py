import pathlib
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'scripts/cyclic_prefix.py').read_text();s=s.replace('rows=[]; totalnodes=0','rows=[]; totalnodes=0\nbegin=int(sys.argv[1]);tag=sys.argv[2]')
s=s.replace('enumerate(itertools.combinations(range(n-k,N),k))','enumerate(itertools.islice(itertools.combinations(range(n-k,N),k),begin,None),begin)')
s=s.replace("D/'cyclic-exhaustive-prefix.json'","D/('cyclic-prefix-'+tag+'.json')")
s=s.replace("'samples_attempted':sample+1","'begin_index':begin,'last_loop_index':sample,'actually_assessed':tested+skipped+timeouts,'next_index':begin+tested+skipped+timeouts")
(D/'scripts/cyclic_more.py').write_text(s)

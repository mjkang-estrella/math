import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/cycles.py').read_text().replace('range(9,19)','range(19,27)').replace("D/'cycles-coverage.json'","D/'cycles-deep-coverage.json'")
exec(compile(s,str(D/'scripts/cycles.py'),'exec'))

import pathlib
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'scripts/covariance.py').read_text().replace('range(1,6)','range(6,9)').replace('covariance-search.json','covariance-extended-search.json');(D/'scripts/covariance_extended.py').write_text(s)

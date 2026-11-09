from pathlib import Path
p=Path('scripts/schur.py').read_text().replace('range(int(sys.argv[1])+1)','range(int(sys.argv[2]),int(sys.argv[1])+1)').replace("'outputs/schur.json'","'outputs/schur-26-30.json'")
Path('scripts/schur_extension.py').write_text(p)

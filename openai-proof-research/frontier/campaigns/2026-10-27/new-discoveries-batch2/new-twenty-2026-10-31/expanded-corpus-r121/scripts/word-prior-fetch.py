import pathlib,runpy
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
for x in [('word-journal.pdf','https://cs.uwaterloo.ca/journals/JIS/VOL24/Grytczuk/grytczuk7.pdf'),('extremal-classic.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v27i1p48/pdf/')]:print(get(x),flush=True)

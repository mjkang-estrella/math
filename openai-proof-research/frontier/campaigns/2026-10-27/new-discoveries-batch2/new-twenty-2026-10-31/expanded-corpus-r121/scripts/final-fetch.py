import pathlib,runpy
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
for x in [('2101.06743v1.html','https://arxiv.org/html/2101.06743v1'),('chord-thesis.pdf','https://www.math.uwaterloo.ca/~kayeats/students/enumerative_perspectives_on_chord_diagrams_thesis.pdf')]:print(get(x),flush=True)

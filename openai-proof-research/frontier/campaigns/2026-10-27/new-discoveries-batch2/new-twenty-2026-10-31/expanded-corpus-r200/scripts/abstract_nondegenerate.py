import pathlib,sys
p=pathlib.Path(__file__).resolve().parent/'abstract_star.py'
s=p.read_text().replace("if any(w[M[i][j]]", "if kind=='ternary' and w[idx[tuple([1]*m)]]<max(w):continue\n if any(w[M[i][j]]").replace("abstract-star-{kind}-{m}-{q}.json","abstract-star-maxdeg-{kind}-{m}-{q}.json")
exec(compile(s,str(p),'exec'))

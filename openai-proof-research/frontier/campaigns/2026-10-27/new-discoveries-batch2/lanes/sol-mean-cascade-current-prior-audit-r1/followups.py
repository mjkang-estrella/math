exec((__import__('pathlib').Path(__file__).parent/'audit.py').read_text().split("if sys.argv[1] in")[0])
tasks=[('mean-current-abs.html','https://arxiv.org/abs/2405.13618'),('cascade-current-abs.html','https://arxiv.org/abs/2004.07893'),('mean-publisher.pdf','https://pefmath.etf.bg.ac.rs/vol20num1/AADM-Vol20-No1-1-23.pdf'),('cascade-author-publications.html','https://pouyanne.perso.math.cnrs.fr/')] 
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:r=list(ex.map(lambda x:get(*x),tasks))
(b/'http-primary.json').write_text(json.dumps(r,indent=2));print(r)

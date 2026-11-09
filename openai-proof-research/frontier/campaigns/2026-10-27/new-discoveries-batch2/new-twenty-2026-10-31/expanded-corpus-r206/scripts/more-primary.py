import pathlib,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
for k,u in [('codes-vor.html','https://doi.org/10.1007/s00574-016-0010-z'),('meander-vor.html','https://doi.org/10.1093/imrn/rny044'),('ghost-vor.html','https://doi.org/10.1007/s10468-014-9476-9'),('hetero-vor.html','https://doi.org/10.1016/j.disc.2018.04.031')]:get(k,u)

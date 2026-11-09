import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
get('zerafa-2026.html','https://arxiv.org/html/2609.28118')
get('zhou-wang-2026.html','https://arxiv.org/html/2610.01137')
get('song-xu.pdf','https://kam.mff.cuni.cz/~spring/media/papers/4/Divisibility_Coloring_P5_free_JS.pdf')
get('chudnovsky-sivaraman.pdf','https://web.math.princeton.edu/~mchudnov/Perfect2div.pdf')

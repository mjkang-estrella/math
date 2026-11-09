from fetch import get
base='https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/'
for name,path in [('boone-introduction.tex','Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/build/introduction.tex'),('hotspots-introduction.tex','Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/introduction.tex')]:print(get((name,base+path)))

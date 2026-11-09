from fetch import get
base='https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/'
print(get(('standard-introduction.tex',base+'build/sections/introduction.tex')))
print(get(('standard-setup.tex',base+'build/sections/setup.tex')))

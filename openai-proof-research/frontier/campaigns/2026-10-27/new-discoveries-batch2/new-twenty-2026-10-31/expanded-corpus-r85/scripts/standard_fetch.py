from fetch import get
base='https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/'
print(get(('standard-README.md',base+'README.md')))
print(get(('standard-main.tex',base+'build/main.tex')))

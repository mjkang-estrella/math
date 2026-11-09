import sys
sys.argv=['x','60']
import pathlib; exec(open(pathlib.Path(__file__).with_name('opt364642.py')).read().split('base=series_base(N)')[0])
base=series_base(60)
for k in (2,6,4,12,8):
    s=power(base,k,60)
    vals=[(n,s[n],(s[n]&-s[n]).bit_length()-1) for n in range(4,61,8)]
    print('k=',k,'8n+4 values (n, OPT, v2):',vals[:5])

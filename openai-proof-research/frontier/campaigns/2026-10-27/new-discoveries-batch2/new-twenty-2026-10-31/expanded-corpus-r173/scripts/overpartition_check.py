import pathlib,json,itertools,math
D=pathlib.Path(__file__).resolve().parents[1]
def count(n,lo=1):
 if n==0:return 1
 return sum((2**len(set(p))) for p in parts(n,lo))
def parts(n,lo):
 if n==0:yield ();return
 for s in range(lo,n+1,2):
  for p in parts(n-s,s):yield (s,)+p
b=[count(n) for n in range(9)];q4=sum(b[j]*b[4-j] for j in range(5));assert b[:5]==[1,2,2,4,6] and q4==32
x=json.loads((D/'outputs/overpartition.json').read_text());print('independent single-color coefficients',b,'two-color q4',q4)
print('corrected sweep',[(r['i'],r['r'],len(r['failures'])) for r in x['rows']]);(D/'outputs/overpartition-independent.json').write_text(json.dumps({'single_color_0_to_8':b,'two_color_q4':q4,'method':'enumeration of all odd partitions weighted by2^number_of_distinct_part_sizes; ordered pair convolution'},indent=2))

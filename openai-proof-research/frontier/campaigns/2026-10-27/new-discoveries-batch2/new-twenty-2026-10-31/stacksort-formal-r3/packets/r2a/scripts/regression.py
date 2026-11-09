import json,pathlib,math,re
lane=pathlib.Path(__file__).resolve().parent.parent
seed=list(map(int,re.search(r'def seed20 : List ℕ := \[(.*?)\]',(lane/'StackSortFinal.lean').read_text()).group(1).split(',')))
a=json.loads((lane/'lower-table.json').read_text())
assert a[:21]==seed
for n in range(21,131):
 assert a[n]==4*a[n-1]+sum(math.comb(n-1,i)*a[i]*a[n-1-i] for i in range(1,n-1))
 for i in range(1,n-1):
  assert math.comb(n-1,i)==math.factorial(n-1)//(math.factorial(i)*math.factorial(n-1-i))
assert a[130]==int(re.search(r'def lower130 : ℕ := (\d+)',(lane/'StackSortCertificate.lean').read_text()).group(1))
assert 4*131*math.factorial(130)*173**131<a[130]*100**131
assert not 4*131*math.factorial(130)*195**131<a[130]*100**131
assert not 4*130*math.factorial(129)*173**130<a[129]*100**130
assert a[130]+1!=4*a[129]+sum(math.comb(129,i)*a[i]*a[129-i] for i in range(1,129))
assert seed[3]!=27
print('PASS: 110 rows, all factorial/binomial coefficients, literal lower130, certificate, four negative controls')

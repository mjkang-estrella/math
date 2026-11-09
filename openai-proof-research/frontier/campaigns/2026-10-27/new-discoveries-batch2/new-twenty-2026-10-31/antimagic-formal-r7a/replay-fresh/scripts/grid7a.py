import runpy
v=runpy.run_path('scripts/review-verify.py')
for n in (3,4,5,6):
 t=2; Z=2**(n-1)-1; q=2**(n-1); N=2*Z
 lab=v['build'](2,n)
 p=lambda i: 4-i if n-1==2 and i in (1,3) else i
 shell=lambda r: Z-1-r//2 if r%2==0 else Z+1+r//2
 a=lambda x: x-Z if x>Z else q+1+x-Z
 assert all(lab[n-1][i]==shell(p(i)) for i in range(q))
 assert sorted(a(x) for x in lab[n-1])==list(range(1,q+1))
 sig=lambda x: 2*x if x<=q//2 else 2*(x-q//2)-1
 assert all(x+a(x)==Z+sig(a(x)) for x in lab[n-1])
 assert all(lab[n][2*i]==N+a(lab[n-1][i]) and lab[n][2*i+1]==N+2*q+1-sig(a(lab[n-1][i])) for i in range(q))
 assert v['check'](2,n,lab)['ok']
 print({'n':n,'patched_parent_permutation':True,'cancellation':True,'literal_formula':True,'proper_and_colours':True})

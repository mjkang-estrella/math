import runpy
v = runpy.run_path('scripts/review-verify.py')
for t in (2,4,6):
    for n in (3,4,5):
        a=v['build'](t,n)
        b=[None]+[[v['closed_label'](t,n,h,i) for i in range(t**h)] for h in range(1,n+1)]
        assert a==b
        r=v['check'](t,n,b)
        assert r['ok'],r
        print(t,n,r)
a=v['build'](2,3,t2_swap=False)
assert not v['check'](2,3,a)['ok']
a=v['build'](4,3);a[1][0]=a[1][1]
assert not v['check'](4,3,a)['ok']
print('nine requested cases and two negative controls passed')

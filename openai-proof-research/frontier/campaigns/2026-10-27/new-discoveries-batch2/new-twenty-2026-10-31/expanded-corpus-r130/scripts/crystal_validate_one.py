import sys, json
sys.path.insert(0, __import__('os').path.dirname(__file__))
sys.argv=[sys.argv[0],sys.argv[1],'0']+sys.argv[2:]
import crystal_validate as cv
lam=json.loads(sys.argv[3]); mu=json.loads(sys.argv[4])
a=cv.KF(lam,mu); b=cv.FP(lam,mu)
print(json.dumps(dict(lam=lam,mu=mu,KF=a,fixed_points=b,equal=a==b)))

import re,sys
f,pat=sys.argv[1],sys.argv[2]; w=int(sys.argv[3]) if len(sys.argv)>3 else 1200
t=open(f).read(); t=re.sub(r'\n\s*\n+','\n',t)
k=t.find('License:'); t=t[k:] if k>0 else t
for m in re.finditer(pat,t): print('=====',m.start()); print(t[max(0,m.start()-w):m.start()+w])

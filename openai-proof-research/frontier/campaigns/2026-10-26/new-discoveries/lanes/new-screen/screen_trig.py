import numpy as np,json
N=4000;M=65536
c=np.zeros(N+1);c[0]=1
for i in range(1,N+1):c[i]=c[i-1]*(2*i-1)/(2*i)
a=np.zeros(N+1);a[0]=1
for i in range(1,N+1):a[i]=a[i-1]*(i-1.5)/i
records=[];bestn=N+1
for D in range(3,401):
 b=np.zeros(N+1)
 for j in range(N//D+1):b[j*D:]+=a[j]*c[:N+1-j*D]
 for n in range(D, min(N,bestn)+1):
  if (n+1)%D not in [0,1,2] and n>2*D:continue
  if n>=bestn:continue
  f=np.fft.rfft(b[:n+1],n=M).real
  v=float(f.min());ix=int(f.argmin());t=ix*2*np.pi/M
  if v< -1e-9:
   bestn=n;rec={'D':D,'d':D-1,'n':n,'t':t,'value':v,'fft_index':ix,'fft_size':M};records.append(rec);print(rec,flush=True)
   break
json.dump({'records':records,'best_n':bestn},open('trig-screen.json','w'),indent=2)

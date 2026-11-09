// PD_2(n) mod 2^64 via sum PD_2(n) q^n = f4 f6^2 / (f1 f3 f12); f_a = prod (1-q^{am}).
// Uses Euler pentagonal sparse series. Tests PD_2(2^{k+2} n) == PD_2(2^k n) mod 2^{k+1}.
#include "libc.h"
typedef uint64_t u;
static long N;
// multiply a by f_s in place (sparse, descending index)
static void mulf(u*a,long s){ for(long n=N;n>=0;n--){ u acc=a[n]; for(long j=1;;j++){ long g1=s*(j*(3*j-1)/2), g2=s*(j*(3*j+1)/2); if(g1>n)break; u sg=(j&1)?(u)-1:1; acc+=sg*a[n-g1]; if(g2<=n) acc+=sg*a[n-g2]; } a[n]=acc; } }
// divide a by f_s in place: a = b/f  <=> a[n] = b[n] - sum_{g>0} e_g a[n-g]
static void divf(u*a,long s){ for(long n=0;n<=N;n++){ u acc=a[n]; for(long j=1;;j++){ long g1=s*(j*(3*j-1)/2), g2=s*(j*(3*j+1)/2); if(g1>n)break; u sg=(j&1)?(u)-1:1; acc-=sg*a[n-g1]; if(g2<=n) acc-=sg*a[n-g2]; } a[n]=acc; } }
int main(int c,char**v){ N=atol(v[1]); u*a=calloc(N+1,8); a[0]=1;
 mulf(a,4); mulf(a,6); mulf(a,6); divf(a,1); divf(a,3); divf(a,12);
 printf("PD2[0..12]:"); for(int i=0;i<=12;i++) printf(" %llu",(unsigned long long)a[i]); printf("\n");
 for(int k=0;k<=40;k++){ long m=1L<<(k+2); if(m>N)break; u mask=(k+1>=64)?~(u)0:(((u)1<<(k+1))-1); long fails=0,first=-1,tested=0;
  for(long n=0;n*m<=N;n++){ tested++; if(((a[n*m]-a[n*(m/4)])&mask)!=0){ if(first<0)first=n; fails++; } }
  // also record exact 2-adic valuation min of difference
  int minv=64; for(long n=1;n*m<=N;n++){ u d=a[n*m]-a[n*(m/4)]; int vv=0; if(d==0)vv=64; else while(!((d>>vv)&1))vv++; if(vv<minv)minv=vv; }
  printf("k=%d tested n<=%ld count=%ld fails=%ld first_fail_n=%ld min_v2_diff(n>=1)=%d\n",k,N/m,tested,fails,first,minv); }
 // write coefficients file for reuse
 FILE*f=fopen(v[2],"wb"); fwrite(a,8,N+1,f); fclose(f); return 0; }

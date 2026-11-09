// Enumerate 6-subsets {0<x1<...<x5} of Z_n generating Z_n (gcd(n,x1..x5)=1), canonical under
// affine maps x->u*x+t (u unit), keep those where every nonzero difference occurs at least twice
// in the ordered difference multiset (necessary for extremality: unimodular masses, mu*mu~=6 delta_0).
int printf(const char*,...); int atoi(const char*); int fflush(void*);
static int n, units[512], nu;
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
static int cmpset(int*a,int*b){for(int i=0;i<6;i++){if(a[i]!=b[i])return a[i]<b[i]?-1:1;}return 0;}
static void sort6(int*a){for(int i=1;i<6;i++){int v=a[i],j=i-1;while(j>=0&&a[j]>v){a[j+1]=a[j];j--;}a[j+1]=v;}}
// canonical: minimal sorted image over units u and translations by -u*e for e in E (so 0 in image)
static int is_canonical(int*E){
  int img[6];
  for(int k=0;k<nu;k++){int u=units[k];
    for(int t=0;t<6;t++){for(int i=0;i<6;i++)img[i]=((u*(E[i]-E[t]))%n+n)%n; sort6(img); if(cmpset(img,E)<0)return 0;}}
  return 1;
}
int main(int argc,char**argv){
  int lo=atoi(argv[1]),hi=atoi(argv[2]);
  for(n=lo;n<=hi;n++){
    nu=0;for(int u=1;u<n;u++)if(gcd(u,n)==1)units[nu++]=u;
    long tot=0,pass=0; int E[6]; E[0]=0; int cnt[512];
    for(E[1]=1;E[1]<n;E[1]++)for(E[2]=E[1]+1;E[2]<n;E[2]++)for(E[3]=E[2]+1;E[3]<n;E[3]++)
    for(E[4]=E[3]+1;E[4]<n;E[4]++)for(E[5]=E[4]+1;E[5]<n;E[5]++){
      int g=n; for(int i=1;i<6;i++)g=gcd(g,E[i]); if(g!=1)continue;
      for(int d=0;d<n;d++)cnt[d]=0;
      for(int i=0;i<6;i++)for(int j=0;j<6;j++)if(i!=j)cnt[(E[i]-E[j]+n)%n]++;
      int ok=1; for(int d=1;d<n;d++)if(cnt[d]==1){ok=0;break;}
      if(!ok)continue;
      tot++;
      if(!is_canonical(E))continue;
      pass++; printf("SET %d %d %d %d %d %d %d\n",n,E[0],E[1],E[2],E[3],E[4],E[5]);
    }
    printf("N %d filtered %ld canonical %ld\n",n,tot,pass); fflush(0);
  }
}

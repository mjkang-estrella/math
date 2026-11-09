// Faster complete enumeration of generating 6-subsets E of Z_n with every nonzero ordered difference
// occurring at least twice (necessary for extremality). Any such E contains 0 after translation; pick the
// 5-subset E5 = E minus y where y is any element; y must repair each singleton difference d of E5:
// y in E5+d or E5-d. We enumerate E5={0<x1<x2<x3<x4} and y over that candidate set (all y if E5 has no
// singleton). Every qualifying E (translated so that it contains 0 at a non-y element) is reached.
int printf(const char*,...); int atoi(const char*); int fflush(void*); void*calloc(unsigned long,unsigned long);
static int n,units[4096],nu;
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
static void sort6(int*a){for(int i=1;i<6;i++){int v=a[i],j=i-1;while(j>=0&&a[j]>v){a[j+1]=a[j];j--;}a[j+1]=v;}}
static int cmp6(int*a,int*b){for(int i=0;i<6;i++)if(a[i]!=b[i])return a[i]<b[i]?-1:1;return 0;}
static void canon(int*E,int*best){int img[6];int first=1;
  for(int k=0;k<nu;k++){int u=units[k];for(int t=0;t<6;t++){for(int i=0;i<6;i++)img[i]=(int)(((long)u*((E[i]-E[t]+n)%n))%n);sort6(img);
    if(first||cmp6(img,best)<0){for(int i=0;i<6;i++)best[i]=img[i];first=0;}}}}
int main(int argc,char**argv){
  int lo=atoi(argv[1]),hi=atoi(argv[2]);
  int *cnt=calloc(8192,sizeof(int)); int (*seen)[6]=calloc(200000,sizeof(int[6])); 
  for(n=lo;n<=hi;n++){
    nu=0;for(int u=1;u<n;u++)if(gcd(u,n)==1)units[nu++]=u;
    int ns=0; long tested=0;
    int E[6]; E[0]=0;
    for(E[1]=1;E[1]<n;E[1]++)for(E[2]=E[1]+1;E[2]<n;E[2]++)for(E[3]=E[2]+1;E[3]<n;E[3]++)for(E[4]=E[3]+1;E[4]<n;E[4]++){
      for(int i=0;i<5;i++)for(int j=0;j<5;j++)if(i!=j)cnt[(E[i]-E[j]+n)%n]++;
      int single=-1; for(int i=0;i<5&&single<0;i++)for(int j=0;j<5;j++)if(i!=j&&cnt[(E[i]-E[j]+n)%n]==1){single=(E[i]-E[j]+n)%n;break;}
      int cand[16],nc=0;
      if(single>=0){for(int i=0;i<5;i++){cand[nc++]=(E[i]+single)%n;cand[nc++]=(E[i]-single+n)%n;}}
      int ylo=0,yhi=(single>=0)?nc:n;
      for(int c=ylo;c<yhi;c++){int y=(single>=0)?cand[c]:c; int in=0;for(int i=0;i<5;i++)if(E[i]==y)in=1; if(in)continue;
        tested++;
        for(int i=0;i<5;i++){cnt[(y-E[i]+n)%n]++;cnt[(E[i]-y+n)%n]++;}
        int ok=1; for(int i=0;i<5&&ok;i++){if(cnt[(y-E[i]+n)%n]<2||cnt[(E[i]-y+n)%n]<2)ok=0; for(int j=0;j<5&&ok;j++)if(i!=j&&cnt[(E[i]-E[j]+n)%n]<2)ok=0;}
        if(ok){int F[6]={E[0],E[1],E[2],E[3],E[4],y};int g=n;for(int i=0;i<6;i++)g=gcd(g,F[i]);
          if(g==1){int b[6];canon(F,b);int dup=0;for(int s=0;s<ns;s++)if(!cmp6(seen[s],b)){dup=1;break;}
            if(!dup&&ns<200000){for(int i=0;i<6;i++)seen[ns][i]=b[i];ns++;}}}
        for(int i=0;i<5;i++){cnt[(y-E[i]+n)%n]--;cnt[(E[i]-y+n)%n]--;}
      }
      for(int i=0;i<5;i++)for(int j=0;j<5;j++)if(i!=j)cnt[(E[i]-E[j]+n)%n]--;
    }
    for(int s=0;s<ns;s++)printf("SET %d %d %d %d %d %d %d\n",n,seen[s][0],seen[s][1],seen[s][2],seen[s][3],seen[s][4],seen[s][5]);
    printf("N %d canonical %d tested %ld\n",n,ns,tested);fflush(0);
  }
}

typedef void FILE;
extern FILE *fopen(const char*,const char*);
extern int fscanf(FILE*,const char*,...);
extern int printf(const char*,...);
extern int puts(const char*);
extern int atoi(const char*);
extern int fflush(FILE*);
extern void *memset(void*,int,unsigned long);
#define stdout ((FILE*)0)
int main(int argc,char**argv){
 FILE*f=fopen(argv[1],"r");int n,m,a[30],b[30],ng=0;long long total=0;int maxn=atoi(argv[2]),maxm=atoi(argv[3]);
 while(fscanf(f,"%d%d",&n,&m)==2){
  for(int j=0;j<m;j++)fscanf(f,"%d%d",a+j,b+j);
  if(n>maxn||m>maxm)continue;
  int size=1<<n,uc[4096]={0},ug[12][12],lam[12][12],cuts[4096];
  for(int s=1;s<size-1;s++)for(int e=0;e<m;e++)uc[s]+=((s>>a[e])^(s>>b[e]))&1;
  for(int u=0;u<n;u++)for(int v=0;v<n;v++){ug[u][v]=99;for(int s=1;s<size-1;s++)if((s>>u&1)&&!(s>>v&1)&&uc[s]<ug[u][v])ug[u][v]=uc[s];}
  int best=-1,wb=-1,bmask=0,wmask=0;
  // reverse symmetry fixes edge0
  int end=m?1<<(m-1):1;
  for(int o=0;o<end;o++){
   int dir=o<<1;
   memset(cuts,0,sizeof(cuts));
   for(int e=0;e<m;e++){
    int u=(dir>>e&1)?b[e]:a[e],v=(dir>>e&1)?a[e]:b[e];
    for(int s=1;s<size-1;s++)cuts[s]+=((s>>u&1)&&!(s>>v&1));
   }
   for(int u=0;u<n;u++)for(int v=0;v<n;v++)lam[u][v]=99;
   for(int s=1;s<size-1;s++)for(int u=0;u<n;u++)if(s>>u&1)for(int v=0;v<n;v++)if(!(s>>v&1)&&cuts[s]<lam[u][v])lam[u][v]=cuts[s];
   int tac=0,balanced=1;
   for(int u=0;u<n;u++)for(int v=0;v<n;v++)if(u!=v){tac+=lam[u][v];if(lam[u][v]<ug[u][v]/2)balanced=0;}
   if(tac>best){best=tac;bmask=dir;}if(balanced&&tac>wb){wb=tac;wmask=dir;}
   total++;
  }
  ng++;printf("n %d m %d best %d balanced_best %d mask %d balanced_mask %d edges",n,m,best,wb,bmask,wmask);for(int e=0;e<m;e++)printf(" %d-%d",a[e],b[e]);puts("");fflush(stdout);
  if(best!=wb){puts("COUNTEREXAMPLE");return 2;}
 }
 printf("COMPLETE graphs %d orientations_mod_reversal %lld\n",ng,total);
}
void __libc_csu_init(void){}
void __libc_csu_fini(void){}

extern int printf(const char *, ...);
extern void abort(void);
#define assert(x) ((x)?(void)0:abort())
static unsigned in[7],spectrum[1<<21];
static unsigned long valid;
int n,m,aa[21],bb[21];
void visit(int e,int graph){
 if(e<m){int a=aa[e],b=bb[e];visit(e+1,graph);in[b]|=1u<<a;visit(e+1,graph|(1<<e));in[b]^=1u<<a;in[a]|=1u<<b;visit(e+1,graph|(1<<e));in[a]^=1u<<b;return;}
 for(int v=0;v<n;v++)if(!in[v])return;
 valid++;int best=n;
 for(unsigned s=0;s<(1u<<n);s++){int k=__builtin_popcount(s);if(k>=best)continue;int v=0;for(;v<n;v++)if(!(in[v]&s))break;if(v==n)best=k;}
 spectrum[graph]|=1u<<best;
}
int main(){for(n=0;n<=6;n++){m=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){aa[m]=a;bb[m++]=b;}for(int i=0;i<(1<<m);i++)spectrum[i]=0;valid=0;visit(0,0);int graphs=0;for(int g=0;g<(1<<m);g++)if(spectrum[g]){graphs++;unsigned x=spectrum[g];while(!(x&1))x>>=1;assert((x&(x+1))==0);}printf("n=%d all_admissible_labeled_graphs=%d valid_orientations=%lu gaps=0\n",n,graphs,valid);}return 0;}

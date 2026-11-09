typedef unsigned long long uint64_t;
extern int printf(const char*,...); extern int atoi(const char*); extern void abort(void); extern void *calloc(unsigned long,unsigned long); extern void free(void*);extern void qsort(void*,unsigned long,unsigned long,int(*)(const void*,const void*));extern void *bsearch(const void*,const void*,unsigned long,unsigned long,int(*)(const void*,const void*));
#define assert(x) ((x)?(void)0:abort())
typedef uint64_t U;
int m,n,N;U lo[63],hi[63],states[20000000],opts[600];int count=0,no=1;
int valid(U s){for(int x=0;x<N;x++)if(!(s>>x&1)&&(s&lo[x])&&(s&hi[x]))return 0;return 1;}
void gen(int i,U s){if(i==m){if(valid(s)){assert(count<20000000);states[count++]=s;}return;}for(int j=0;j<no;j++)gen(i+1,s|(opts[j]<<(i*n)));}
U row(U s){for(int x=N-1;x>=0;x--){U b=1ULL<<x;int ok=1;if(s&b)ok=!((s&(lo[x]^b))&&(s&(hi[x]^b)));else{int i=x/n,j=x%n,p[4]={i?x-n:-1,j?x-1:-1,i+1<m?x+n:-1,j+1<n?x+1:-1};for(int k=0;k<4;k++)if(p[k]>=0&&!(s>>p[k]&1)&&(s&(k<2?lo[p[k]]:hi[p[k]])))ok=0;}if(ok)s^=b;}return s;}
int cmp(const void*a,const void*b){U x=*(U*)a,y=*(U*)b;return (x>y)-(x<y);}
int main(int argc,char**argv){m=atoi(argv[1]);n=atoi(argv[2]);N=m*n;assert(N<=63&&n<=32);U even=0;for(int i=0;i<m;i++)for(int j=0;j<n;j++){int x=i*n+j;if((i+j)%2==0)even|=1ULL<<x;for(int a=0;a<m;a++)for(int b=0;b<n;b++){if(a<=i&&b<=j)lo[x]|=1ULL<<(a*n+b);if(a>=i&&b>=j)hi[x]|=1ULL<<(a*n+b);}}
for(int a=0;a<n;a++)for(int b=a;b<n;b++)opts[no++]=((1ULL<<(b-a+1))-1)<<a;gen(0,0);qsort(states,count,sizeof(U),cmp);char*seen=calloc(count,1);int orbits=0,maxlen=0;for(int i=0;i<count;i++)if(!seen[i]){U s=states[i],start=s;long long sum=0;int len=0;do{U*p=bsearch(&s,states,count,sizeof(U),cmp);assert(p);int k=p-states;assert(!seen[k]);seen[k]=1;len++;sum+=2*__builtin_popcountll(s&even)-__builtin_popcountll(s);s=row(s);}while(s!=start);orbits++;if(len>maxlen)maxlen=len;if(sum){printf("FAIL m %d n %d start %llu length %d sum %lld\n",m,n,(unsigned long long)start,len,sum);return 1;}}
printf("m %d n %d states %d orbits %d max_length %d all_orbit_sums_zero true\n",m,n,count,orbits,maxlen);free(seen);return 0;}

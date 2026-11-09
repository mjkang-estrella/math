extern int printf(const char*,...); extern int atoi(const char*); extern void *calloc(unsigned long,unsigned long); extern void free(void*); extern int memcmp(const void*,const void*,unsigned long); int abs(int x){return x<0?-x:x;}
int gcd(int a,int b){return b?gcd(b,a%b):a;}
int max(int a,int b){return a>b?a:b;}
int main(int argc,char**argv){int lo=atoi(argv[1]),hi=atoi(argv[2]);long tests=0;for(int b=lo;b<=hi;b++)for(int a=1;a<=40;a++)for(int c=1;c<=40;c++)if(gcd(a,c)==1)for(int y=1;y<2*b;y++)if(gcd(b,y)==1){
// Exclusions from Cor 6.2, Prop 5.1(i,iii), 7.4, 8.1,8.2.
if(c%a==0 && c/a%2==0 && y==b)continue;
if(a%c==0){int k=a/c;if((k%2 && k*y%(2*b)==0)||(!(k%2)&&k*y%(2*b)==b))continue;}
if(a==c && (y==b || (b%2 && (y==b-1||y==b+1))))continue;
if(b==1 && a%2 && abs(a-c)==1)continue;
if((b==2&&a==2&&c==3&&(y==1||y==3))||(b==3&&a==3&&c==2&&(y==1||y==5)))continue;
int p=2*b*(a+c)/gcd(2*b,y),N=max(6*p,3000),w=2*b;unsigned char *v=calloc((N+1)*w,1);
for(int x=0;x<=N;x++)for(int h=0;h<w;h++){int mask=0;if(h>=b)mask|=1<<v[x*w+h-b];if(x>=a)mask|=1<<v[(x-a)*w+h];if(x>=c)mask|=1<<v[(x-c)*w+(h+y)%w];int z=0;while(mask>>z&1)z++;v[x*w+h]=z;}
// Full rows use exact 2b vertical periodicity: check stabilization for all 2b rows.
int found=0,pre=0;for(int d=1;d<=p;d++)if(p%d==0){int last=-1;for(int x=0;x+d<=N;x++)if(memcmp(&v[x*w],&v[(x+d)*w],w))last=x;if(last< N-max(a,c)-2*p-d){found=d;pre=last+1;break;}}
tests++;if(found!=p){printf("candidate %d %d %d %d predicted %d found %d pre %d\n",b,a,c,y,p,found,pre);}
free(v); }printf("tests %ld b %d..%d a,c 1..40\n",tests,lo,hi);}

typedef unsigned long long uint64_t;
extern int printf(const char *, ...);
extern int puts(const char *);
extern double exp(double);
static uint64_t st=246;unsigned rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return (unsigned)st;}
int n,m,a[120],b[120],lab[120],col[60],sz[3],s[60],best,found;long long iters;
int energy(){int sum[3]={0},sq[3]={0};for(int v=0;v<n;v++){sum[col[v]]+=s[v];sq[col[v]]+=s[v]*s[v];}int en=0;for(int c=0;c<3;c++)en+=sz[c]*sq[c]-sum[c]*sum[c];if(en==0){for(int i=0;i<3;i++)for(int j=0;j<i;j++)if(sum[i]*sz[j]==sum[j]*sz[i])en+=1000;}return en;}
void run(){for(int i=0;i<m;i++)lab[i]=i+1;for(int i=0;i<n;i++)s[i]=0;for(int i=0;i<m;i++){s[a[i]]+=lab[i];s[b[i]]+=lab[i];}int en=energy();for(int step=0;step<120000;step++){int i=rnd()%m,j=rnd()%m;if(i==j)continue;int d=lab[j]-lab[i];s[a[i]]+=d;s[b[i]]+=d;s[a[j]]-=d;s[b[j]]-=d;int ne=energy();double t=0.3+20.0*(1-(step%10000)/10000.0);if(ne<=en || (double)rnd()/4294967296.0 < exp((en-ne)/t)){int x=lab[i];lab[i]=lab[j];lab[j]=x;en=ne;}else{s[a[i]]-=d;s[b[i]]-=d;s[a[j]]+=d;s[b[j]]+=d;}iters++;if(en<best)best=en;if(en==0){found=1;printf("FOUND order %d colors",n);for(int v=0;v<n;v++)printf(" %d",col[v]);printf(" labels");for(int i=0;i<m;i++)printf(" %d",lab[i]);printf(" sums");for(int v=0;v<n;v++)printf(" %d",s[v]);puts("");return;}}}
void colors(int v,int top){if(found)return;if(v==n){if(top<2)return;for(int c=0;c<3;c++)sz[c]=0;for(int i=0;i<n;i++)sz[col[i]]++;run();return;}for(int c=0;c<=top+1 && c<3;c++){int ok=1;for(int i=0;i<m;i++)if(b[i]==v&&a[i]<v&&col[a[i]]==c)ok=0;else if(a[i]==v&&b[i]<v&&col[b[i]]==c)ok=0;if(ok){col[v]=c;colors(v+1,c>top?c:top);}}}
int main(){for(n=12;n<=16;n+=4){m=0;for(int i=0;i<n;i++){a[m]=i;b[m++]=(i+1)%n;}for(int i=0;i<n/2;i++){a[m]=i;b[m++]=i+n/2;}best=100000;found=0;iters=0;col[0]=0;colors(1,0);printf("order %d iterations %lld best %d found %d\n",n,iters,best,found);if(found)break;}return 0;}

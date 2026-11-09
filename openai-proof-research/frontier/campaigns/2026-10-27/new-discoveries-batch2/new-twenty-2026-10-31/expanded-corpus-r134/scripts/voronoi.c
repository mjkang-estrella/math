extern int printf(const char*,...);extern int atoi(const char*);
int n,k,V,L,p[16],d[128][128];long long tested,eqs;
int gcd(int a,int b){return b?gcd(b,a%b):a;}
int payoff(int idx,int loc){int sum=0;for(int x=0;x<V;x++){int ds=d[x][loc],tie=1,lose=0;for(int j=0;j<k;j++)if(j!=idx){int q=d[x][p[j]];if(q<ds){lose=1;break;}if(q==ds)tie++;}if(!lose)sum+=L/tie;}return sum;}
int equilibrium(){for(int i=0;i<k;i++){if(i&&p[i]==p[i-1])continue;int old=payoff(i,p[i]);for(int y=0;y<V;y++)if(payoff(i,y)>old)return 0;}return 1;}
void rec(int t,int start){if(t==k){tested++;if(equilibrium()){eqs++;if(eqs<=10){for(int i=0;i<k;i++)printf("%d ",p[i]);printf("\n");}}return;}for(int x=start;x<V;x++){p[t]=x;rec(t+1,x);}}
int main(int argc,char**argv){n=atoi(argv[1]);k=atoi(argv[2]);V=1<<n;L=1;for(int i=1;i<=k;i++)L=L/gcd(L,i)*i;for(int i=0;i<V;i++)for(int j=0;j<V;j++)d[i][j]=__builtin_popcount((unsigned)(i^j));p[0]=0;rec(1,0);printf("n %d k %d normalized multisets %lld equilibria %lld denominator %d\n",n,k,tested,eqs,L);}

#include <bits/stdc++.h>
#include <sys/resource.h>
#include <sched.h>
using namespace std; using G=vector<vector<int>>;
string root(const G&g,int v,int p){vector<string>s;for(int w:g[v])if(w!=p)s.push_back(root(g,w,v));sort(s.begin(),s.end());string a="(";for(auto &t:s)a+=t;return a+")";}
string canon(const G&g){string s;for(int i=0;i<(int)g.size();i++){auto a=root(g,i,-1);if(i==0||a<s)s=a;}return s;}
void edge(G&g,int a,int b){g[a].push_back(b);g[b].push_back(a);}
double energy(const G&g){int n=g.size();double a[20][20]={};for(int i=0;i<n;i++)for(int j:g[i])a[i][j]=1/sqrt(double(g[i].size()*g[j].size()));
for(int it=0;it<60;it++){double mx=0;for(int p=0;p<n;p++)for(int q=p+1;q<n;q++){double v=a[p][q];mx=max(mx,abs(v));if(abs(v)<1e-14)continue;double tau=(a[q][q]-a[p][p])/(2*v), t=copysign(1.0,tau)/(abs(tau)+sqrt(1+tau*tau)),c=1/sqrt(1+t*t),s=t*c;a[p][p]-=t*v;a[q][q]+=t*v;a[p][q]=a[q][p]=0;for(int k=0;k<n;k++)if(k!=p&&k!=q){double x=a[k][p],y=a[k][q];a[k][p]=a[p][k]=c*x-s*y;a[k][q]=a[q][k]=s*x+c*y;}}if(mx<1e-12)break;}
double v=0;for(int i=0;i<n;i++)v+=abs(a[i][i]);return v;}
int main(){rlimit r{120,120};setrlimit(RLIMIT_CPU,&r);r={6ull<<30,6ull<<30};setrlimit(RLIMIT_AS,&r);cpu_set_t old,c;CPU_ZERO(&c);sched_getaffinity(0,sizeof(old),&old);int k=0;for(int i=0;i<CPU_SETSIZE&&k<2;i++)if(CPU_ISSET(i,&old)){CPU_SET(i,&c);k++;}sched_setaffinity(0,sizeof(c),&c);auto st=chrono::steady_clock::now();vector<G> prev(1,G(2));edge(prev[0],0,1);
for(int n=3;n<=18;n++){map<string,G> current;for(auto &g:prev)for(int v=0;v<n-1;v++){G h=g;h.emplace_back();edge(h,v,n-1);current.emplace(canon(h),move(h));}prev.clear();G sun(n);if(n%2){for(int i=0;i<(n-1)/2;i++){edge(sun,0,1+2*i);edge(sun,1+2*i,2+2*i);}}else{edge(sun,0,1);int z=(n-2)/2;for(int i=0;i<z;i++){edge(sun,i<(z+1)/2?0:1,2+2*i);edge(sun,2+2*i,3+2*i);}}
double bound=energy(sun),best=-1;string key;for(auto &[s,g]:current){double e=energy(g);if(e>best){best=e;key=s;}prev.push_back(move(g));}cout<<setprecision(17)<<"n="<<n<<" count="<<current.size()<<" best="<<best<<" sun="<<bound<<" excess="<<best-bound<<" canonical="<<key<<endl;if(best>bound+1e-8){cout<<"POSSIBLE_COUNTEREXAMPLE_NUMERIC_ONLY"<<endl;break;}if(chrono::duration<double>(chrono::steady_clock::now()-st).count()>90){cout<<"SOFT_TIME_STOP"<<endl;break;}}
}

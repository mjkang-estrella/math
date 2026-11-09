#include <bits/stdc++.h>
using namespace std;
int n,k,V,L; long long tested,eqs; vector<vector<int>> dista;vector<int> p; vector<vector<int>> witnesses;
int payoff(const vector<int>& a,int idx,int loc){int sum=0;for(int x=0;x<V;x++){int d=dista[x][loc],tie=1;bool lose=false;for(int j=0;j<k;j++)if(j!=idx){int q=dista[x][a[j]];if(q<d){lose=true;break;}if(q==d)tie++;}if(!lose)sum+=L/tie;}return sum;}
bool equilibrium(){for(int i=0;i<k;i++){if(i&&p[i]==p[i-1])continue;int old=payoff(p,i,p[i]);for(int y=0;y<V;y++)if(payoff(p,i,y)>old)return false;}return true;}
void rec(int start){if((int)p.size()==k){tested++;if(equilibrium()){eqs++;if(witnesses.size()<10)witnesses.push_back(p);}return;}for(int x=start;x<V;x++){p.push_back(x);rec(x);p.pop_back();}}
int main(int argc,char**argv){n=atoi(argv[1]);k=atoi(argv[2]);V=1<<n;L=1;for(int i=1;i<=k;i++)L=lcm(L,i);dista.assign(V,vector<int>(V));for(int i=0;i<V;i++)for(int j=0;j<V;j++)dista[i][j]=__builtin_popcount((unsigned)(i^j));p={0};rec(0);cout<<"n "<<n<<" k "<<k<<" normalized multisets "<<tested<<" equilibria "<<eqs<<" denominator "<<L<<"\n";for(auto a:witnesses){for(int x:a)cout<<x<<' ';cout<<"\n";}}

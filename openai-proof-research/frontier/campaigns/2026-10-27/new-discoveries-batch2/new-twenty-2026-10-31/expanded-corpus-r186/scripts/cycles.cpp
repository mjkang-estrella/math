#include <algorithm>
#include <iostream>
#include <vector>
using namespace std;
long long counts[18],totals[18];int N,pat;
bool cyclic(const vector<int>&p){int j=0;for(int k=0;k<(int)p.size();k++){j=p[j];if(j==0)return k==(int)p.size()-1;}return false;}
bool allowed(const vector<int>&p,int at){int n=p.size();
 if(pat==123){int low=100;for(int i=0;i<at;i++){if(p[i]>low)return false;low=min(low,p[i]);}}
 if(pat==321){int high=-1;for(int i=at;i<n;i++){if(p[i]<high)return false;high=max(high,p[i]);}}
 if(pat==132 || pat==231){int lo=100,hi=-1;for(int i=0;i<at;i++){lo=min(lo,p[i]);hi=max(hi,p[i]);}for(int i=at;i<n;i++){if(pat==132 && lo<p[i])return false;if(pat==231 && hi>p[i])return false;}}
 return true;}
void dfs(const vector<int>&p){int n=p.size();totals[n]++;if(n && cyclic(p))counts[n]++;if(n==N)return;for(int at=0;at<=n;at++)if(allowed(p,at)){auto q=p;q.insert(q.begin()+at,n);dfs(q);}}
int main(int argc,char**argv){N=stoi(argv[1]);for(int q:{123,132,231,321}){pat=q;fill(counts,counts+18,0);fill(totals,totals+18,0);dfs({});for(int n=1;n<=N;n++)cout<<q<<" "<<n<<" "<<totals[n]<<" "<<counts[n]<<"\n";cout.flush();}}

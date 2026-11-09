#include <bits/stdc++.h>
using namespace std;
int posi[10][10];
int main(){for(int n=5;n<=7;n++){
 int b=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)posi[i][j]=b++;
 vector<unordered_set<unsigned>> orbit(n+1);vector<unsigned> canonical(n+1);
 for(int k=5;k<=n;k++){
  int z=0;int idx[10][10];for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)idx[i][j]=z++;
  vector<int> p(k);iota(p.begin(),p.end(),0);int odd=k%2?k:k+1;
  do{unsigned m=0;for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)if((p[j]-p[i]+odd)%odd<=odd/2)m|=1u<<idx[i][j];orbit[k].insert(m);}while(next_permutation(p.begin(),p.end()));
  unsigned m=0;for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)if(j-i<=odd/2)m|=1u<<idx[i][j];canonical[k]=m;
 }
 vector<vector<vector<int>>> maps(n+1);
 for(int k=5;k<=n;k++)for(int s=0;s<(1<<n);s++)if(__builtin_popcount((unsigned)s)==k){vector<int>v,mp;for(int i=0;i<n;i++)if(s>>i&1)v.push_back(i);for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)mp.push_back(posi[v[i]][v[j]]);maps[k].push_back(mp);}
 vector<int> mx(n+1,-1),count(n+1),bad(n+1);vector<unsigned>witness(n+1);
 for(unsigned m=0;m<(1u<<b);m++)for(int k=5;k<=n;k++){
  int score=0;for(auto &mp:maps[k]){unsigned sub=0;for(int i=0;i<(int)mp.size();i++)sub|=((m>>mp[i])&1u)<<i;score+=orbit[k].count(sub);}
  if(score>mx[k])mx[k]=score,count[k]=bad[k]=0;
  if(score==mx[k]){count[k]++;if(!orbit[n].count(m))bad[k]++,witness[k]=m;}
 }
 for(int k=5;k<=n;k++)cout<<"n="<<n<<" k="<<k<<" labelled="<<(1u<<b)<<" max="<<mx[k]<<" maximizers="<<count[k]<<" noncanonical="<<bad[k]<<" witness="<<witness[k]<<endl;
}}

#include <bits/stdc++.h>
using namespace std;
void check(vector<pair<int,int>> e,int n,string name){
 int m=e.size();vector<int>p(m);iota(p.begin(),p.end(),1);long long count=0,valid=0;int best=n;vector<int>w;
 do{vector<int>s(n);for(int i=0;i<m;i++){s[e[i].first]+=p[i];s[e[i].second]+=p[i];}bool ok=1;for(auto [a,b]:e)if(s[a]==s[b]){ok=0;break;}count++;if(!ok)continue;valid++;set<int>cs(s.begin(),s.end());if((int)cs.size()<best){best=cs.size();w=p;}}
 while(next_permutation(p.begin(),p.end()));
 cout<<name<<" edges "<<m<<" permutations "<<count<<" valid "<<valid<<" minimum "<<best<<" witness";for(int x:w)cout<<" "<<x;cout<<endl;
}
int main(){for(int r=2;r<=4;r++){vector<int>a(r,3);function<void(int)> rec=[&](int t){if(t==r){int m=1;for(int x:a)m+=x-1;if(m>10||a.back()<4)return;vector<pair<int,int>>e={{0,1}};int n=2;string name="GB";for(int x:a){name+="_"+to_string(x);int last=0;for(int j=0;j<x-2;j++){e.push_back({last,n});last=n++;}e.push_back({last,1});}check(e,n,name);return;}for(int x=(t?a[t-1]:3);x<=7;x++){a[t]=x;rec(t+1);}};rec(0);} }

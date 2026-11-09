#include <bits/stdc++.h>
using namespace std;
using P=vector<int>;
bool avoid(const P&p,int cls,int pos){
 vector<P> pats=cls==0?vector<P>{{2,1,3,4},{4,2,1,5,3},{2,4,1,5,3}}:vector<P>{{2,1,4,3},{4,2,1,3,5},{2,4,1,3,5}};
 int n=p.size();for(auto pat:pats){int k=pat.size();vector<int> ind(k);bool found=false;
 function<void(int,int)> go=[&](int z,int start){if(found)return;if(z==k){if(find(ind.begin(),ind.end(),pos)==ind.end())return;for(int a=0;a<k;a++)for(int b=0;b<a;b++)if((p[ind[a]]<p[ind[b]])!=(pat[a]<pat[b]))return;found=true;return;}for(int j=start;j<=n-k+z;j++){ind[z]=j;go(z+1,j+1);}};go(0,0);if(found)return false;}return true;
}
int main(){vector<P> cs[2];cs[0]={{}};cs[1]={{}};for(int n=1;n<=11;n++){map<pair<int,int>,long long> counts[2];for(int c=0;c<2;c++){vector<P> ns;for(auto p:cs[c])for(int j=0;j<n;j++){P q=p;q.insert(q.begin()+j,n);if(!avoid(q,c,j))continue;int d=0,id=0;P inv(n);for(int a=0;a<n;a++){inv[q[a]-1]=a;if(a&&q[a-1]>q[a])d++;}for(int a=1;a<n;a++)if(inv[a-1]>inv[a])id++;if(c){d=n-1-d;id=n-1-id;}counts[c][{d,id}]++;ns.push_back(q);}cs[c]=move(ns);}cout<<"n "<<n<<" count0 "<<cs[0].size()<<" count1 "<<cs[1].size()<<" distributions_equal "<<(counts[0]==counts[1])<<endl;for(auto [pair,num]:counts[0])cout<<pair.first<<","<<pair.second<<":"<<num<<" ";cout<<endl;}}

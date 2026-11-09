#include <vector>
#include <algorithm>
#include <iostream>
#include <cstdint>
using namespace std;
const int N=17; uint64_t cnt[18][1<<16];
void dfs(vector<int>&p,int mask){int n=p.size(); cnt[n][mask]++; if(n==N)return; int pos[18];for(int j=0;j<n;j++)pos[p[j]]=j;
 for(int at=0;at<=n;at++){int a=pos[n-1]+(pos[n-1]>=at),b=at;if(a>b)swap(a,b);bool ok=true;
 for(int i=(n-1)%2;i+1<n;i+=2){int c=pos[i]+(pos[i]>=at),d=pos[i+1]+(pos[i+1]>=at);if(c>d)swap(c,d);if((a<c&&c<b&&b<d)||(c<a&&a<d&&d<b)){ok=false;break;}}
 if(ok){bool desc=pos[n-1]>=at;bool m=(desc==((n-1)%2==0));p.insert(p.begin()+at,n);dfs(p,mask|(int(m)<<(n-1)));p.erase(p.begin()+at);}}
}
int main(){vector<int>p={0};dfs(p,0);for(int n=2;n<=N;n++){uint64_t mx=0,total=0;for(int i=0;i<(1<<(n-1));i++){total+=cnt[n][i];mx=max(mx,cnt[n][i]);} cout<<"n "<<n<<" total "<<total<<" max "<<mx<<" maximizers";
 int bad=0,num=0;for(int i=0;i<(1<<(n-1));i++)if(cnt[n][i]==mx){num++;vector<int>b;int run=1;for(int j=1;j<n-1;j++){if(((i>>j)&1)==((i>>(j-1))&1))run++;else{b.push_back(run);run=1;}}b.push_back(run);bool fail=false;for(int j=0;j<(int)b.size();j++)if(b[j]>3||(j&&b[j]==3&&b[j-1]==3))fail=true;if(fail)bad++;if(n>=8&&fail)cout<<" BAD "<<i;}
 cout<<" "<<num<<" violations "<<(n>=8?bad:0)<<endl;}}

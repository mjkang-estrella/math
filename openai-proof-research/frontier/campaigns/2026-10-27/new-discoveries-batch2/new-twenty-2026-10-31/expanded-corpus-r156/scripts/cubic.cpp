#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
int n,A[16][16],d[16];long long graphs=0, cyclesum=0;bool found=false;
vector<vector<int>> C;int edgeid[16][16];
bool solve(vector<vector<int>> cs){
 if(cs.empty())return true;
 auto it=min_element(cs.begin(),cs.end(),[](auto&a,auto&b){return a.size()<b.size();});
 if(it->empty())return false;
 for(int e:*it){
  bool off[32]={};for(auto&c:cs)if(find(c.begin(),c.end(),e)!=c.end())for(int f:c)if(f!=e)off[f]=true;
  vector<vector<int>> rem;bool ok=true;
  for(auto&c:cs){if(find(c.begin(),c.end(),e)!=c.end())continue;vector<int>x;for(int f:c)if(!off[f])x.push_back(f);if(x.empty()){ok=false;break;}rem.push_back(x);}
  if(ok&&solve(rem))return true;
 }return false;
}
void test(){
 graphs++;int id=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)if(A[a][b])edgeid[a][b]=edgeid[b][a]=id++;
 C.clear();for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)if(A[a][b])for(int c=a+1;c<n;c++)if(c!=b&&A[b][c])for(int e=a+1;e<n;e++)if(e!=b&&e!=c&&A[c][e])for(int f=b+1;f<n;f++)if(f!=c&&f!=e&&A[e][f]&&A[f][a])C.push_back({edgeid[a][b],edgeid[b][c],edgeid[c][e],edgeid[e][f],edgeid[f][a]});
 cyclesum+=C.size();if(!solve(C)){found=true;cout<<"WITNESS "<<n<<"\n";for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)if(A[a][b])cout<<a<<" "<<b<<"\n";}
}
void fill(int v,int start){
 if(found)return;
 if(d[v]==3){int w=v+1;while(w<n&&d[w]==3)w++;if(w==n)test();else fill(w,w+1);return;}
 for(int b=start;b<n;b++)if(d[b]<3&&!A[v][b]){
  bool tri=false;for(int c=0;c<n;c++)if(A[v][c]&&A[b][c])tri=true;if(tri)continue;
  A[v][b]=A[b][v]=1;d[v]++;d[b]++;fill(v,b+1);d[v]--;d[b]--;A[v][b]=A[b][v]=0;
 }
}
int main(int argc,char**argv){n=stoi(argv[1]);for(int b=1;b<=3;b++){A[0][b]=A[b][0]=1;d[b]++;}d[0]=3;auto t=chrono::steady_clock::now();fill(1,2);cout<<"n "<<n<<" canonical_first_neighbours_fixed graphs "<<graphs<<" total_5cycles "<<cyclesum<<" counterexample "<<found<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t).count()<<"\n";}

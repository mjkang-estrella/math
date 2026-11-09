#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using U=uint64_t;
void concepts(){
 std::vector<U>E;for(int i=0;i<5;i++)for(int j=5;j<10;j++)for(int k=j+1;k<10;k++)E.push_back((1ULL<<i)|(1ULL<<j)|(1ULL<<k));
 int m=E.size();U all=(1ULL<<m)-1;std::vector<U>N(m);for(int i=0;i<m;i++)for(int j=0;j<m;j++)if(E[i]&E[j])N[i]|=1ULL<<j;
 auto nbr=[&](U a){U b=all;while(a){int i=std::countr_zero(a);a&=a-1;b&=N[i];}return b;};auto cls=[&](U a){return nbr(nbr(a));};
 std::vector<U>hit;for(U c=0;c<1024;c++)if(std::popcount(c)==4){U h=0;for(int i=0;i<m;i++)if(E[i]&c)h|=1ULL<<i;hit.push_back(h);}
 U a=cls(0);long count=0,valid=0;do{count++;U b=nbr(a);U sa=0,sb=0;for(int i=0;i<m;i++){if(a>>i&1)sa|=E[i];if(b>>i&1)sb|=E[i];}if(sa==1023&&sb==1023){valid++;bool ok=false;for(U h:hit)if(((a|b)&~h)==0){ok=true;break;}if(!ok){std::cout<<"COUNTEREXAMPLE "<<a<<" "<<b<<std::endl;return;}}
 if(count%100000==0)std::cout<<"concepts checkpoint "<<count<<" valid "<<valid<<std::endl;
 bool found=false;for(int i=m-1;i>=0;i--)if(!(a>>i&1)){U low=(1ULL<<i)-1;U c=cls((a&low)|(1ULL<<i));if((c&low)==(a&low)){a=c;found=true;break;}}if(!found)break;
 }while(true);std::cout<<"concepts COMPLETE n=10 pin=5 r=s=3 closed_pairs="<<count<<" valid="<<valid<<" no failure"<<std::endl;
}
bool order(U remaining,int s,U seen,int p){if(std::popcount(remaining)==1)return true;U options=remaining;while(options){int i=std::countr_zero(options);options&=options-1;int t=(s+i)%p;if(!(seen>>t&1)&&order(remaining&~(1ULL<<i),t,seen|(1ULL<<t),p))return true;}return false;}
void cyclic(int p){long leaves=0,valid=0;auto gen=[&](auto&&self,int i,int sum,U x)->void{if(i>(p-1)/2){leaves++;if(sum%p||std::popcount(x)<3)return;valid++;int first=std::countr_zero(x);if(!order(x&~(1ULL<<first),first,1|(1ULL<<first),p)){std::cout<<"FAIL "<<x<<std::endl;exit(1);}return;}self(self,i+1,sum,x);self(self,i+1,(sum+i)%p,x|(1ULL<<i));self(self,i+1,(sum+p-i)%p,x|(1ULL<<(p-i)));};gen(gen,1,0,0);std::cout<<"cyclic COMPLETE p="<<p<<" inverse-free subsets="<<leaves<<" nonempty zero-sum size>=3="<<valid<<" no failure"<<std::endl;}
void cube(int n,bool anti,int trials){std::vector<std::pair<int,int>>E;int full=(1<<n)-1;for(int v=0;v<=full;v++)for(int i=0;i<n;i++)if(!(v>>i&1))E.push_back({v,v^(1<<i)});int idx[32][32]={};for(int j=0;j<(int)E.size();j++){auto [v,w]=E[j];idx[v][w]=idx[w][v]=j;}
 std::vector<int>rep(E.size(),-1);int k=0;for(int j=0;j<(int)E.size();j++)if(rep[j]<0){rep[j]=k;if(anti){auto[v,w]=E[j];rep[idx[v^full][w^full]]=k;}k++;}
 std::mt19937_64 rng(231);U total=trials?trials:(1ULL<<k);for(U z=0;z<total;z++){U mask=trials?rng():z;std::vector<int>col(E.size());for(int j=0;j<(int)E.size();j++){col[j]=(mask>>rep[j])&1;if(anti){auto[v,w]=E[j];int t=idx[v^full][w^full];if(j>t)col[j]^=1;}}
 bool ok=false;for(int start=0;start<=full&&!ok;start++){std::array<int,5>a;std::iota(a.begin(),a.begin()+n,0);do{int v=start,prev=-1,changes=0;for(int i=0;i<n;i++){int w=v^(1<<a[i]);int c=col[idx[v][w]];if(prev>=0&&c!=prev)changes++;prev=c;v=w;}if(changes<=(anti?0:1)){ok=true;break;}}while(std::next_permutation(a.begin(),a.begin()+n));}if(!ok){std::cout<<"CUBE FAILURE "<<n<<" "<<mask<<std::endl;return;}}
 std::cout<<"cube COMPLETE n="<<n<<" anti="<<anti<<" assignments="<<total<<" sampled="<<(trials!=0)<<" no failure"<<std::endl;
}
int main(int argc,char**argv){std::string mode=argv[1];if(mode=="concepts")concepts();else if(mode=="cyclic")cyclic(std::stoi(argv[2]));else {cube(3,false,0);cube(4,true,0);cube(4,false,100000);cube(5,true,20000);}}

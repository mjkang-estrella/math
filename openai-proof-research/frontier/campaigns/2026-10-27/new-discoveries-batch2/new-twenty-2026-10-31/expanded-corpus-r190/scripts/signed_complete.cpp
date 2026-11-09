#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <random>
#include <vector>
#include <cstdint>
using namespace std;
int main(){int ix[8][8],k=0;for(int a=0;a<8;a++)for(int b=a+1;b<8;b++)ix[a][b]=ix[b][a]=k++;
vector<array<uint32_t,3>> templates;array<int,8> p={0,1,2,3,4,5,6,7};do{array<uint32_t,3> t={};for(int j=1;j<7;j++){vector<pair<int,int>> es={{7,j}};for(int z=1;z<4;z++)es.push_back({(j+z)%7,(j-z+7)%7});for(auto [a,b]:es)t[(j-1)/2]|=1u<<ix[p[a]][p[b]];}sort(t.begin(),t.end());templates.push_back(t);}while(next_permutation(p.begin()+1,p.end()));sort(templates.begin(),templates.end());templates.erase(unique(templates.begin(),templates.end()),templates.end());
uint64_t hist[3]={};int failed=0;for(uint32_t m=0;m<(1u<<21);m++){uint32_t s=0;int z=0;for(int a=1;a<8;a++)for(int b=a+1;b<8;b++,z++)if(m>>z&1)s|=1u<<ix[a][b];bool ok=false;for(auto t:templates){if(!(popcount(s&t[0])%2)&&!(popcount(s&t[1])%2)&&!(popcount(s&t[2])%2)){ok=true;break;}}if(!ok){if(failed<100)cout<<"uncovered "<<m<<'\n';failed++;}}cout<<"normalized signatures "<<(1<<21)<<" templates "<<templates.size()<<" uncovered "<<failed<<endl;
}

#include <algorithm>
#include <iostream>
#include <numeric>
#include <cstdlib>
int main(int argc,char**argv){int n=std::atoi(argv[1]),p[16],inv[16];long long h[16][16]={},count=0;std::iota(p,p+n,0); do{int a=0,b=0;for(int j=0;j<n;j++)inv[p[j]]=j;for(int j=0;j<n-1;j++){a+=((p[j]>p[j+1])==(j%2==0));b+=((inv[j]>inv[j+1])==(j%2==0));}h[a][b]++;count++;}while(std::next_permutation(p,p+n));std::cout<<"{\"n\":"<<n<<",\"count\":"<<count<<",\"hist\":[";for(int i=0;i<n;i++){if(i)std::cout<<",";std::cout<<"[";for(int j=0;j<n;j++){if(j)std::cout<<",";std::cout<<h[i][j];}std::cout<<"]";}std::cout<<"]}\n";}

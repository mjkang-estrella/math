#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

// Independent literal RREF enumeration over F_3, rank 3. Every maximal minor
// is tested. No run-skeleton classification is used in this program.
using Col = std::array<int,3>;
bool allowed[27][27][27];
Col vectors[27];
int columns[20];
std::vector<int> options[20];
int dimension;

std::uint64_t search(int position) {
  if (position==dimension) return 1;
  std::uint64_t count=0;
  for (int v:options[position]) {
    bool good=true;
    for (int a=0;a<position && good;++a)
      for (int b=a+1;b<position;++b)
        if (!allowed[columns[a]][columns[b]][v]) {good=false;break;}
    if (good) {columns[position]=v;count+=search(position+1);}
  }
  return count;
}

int main() {
  for(int i=0;i<27;++i) vectors[i]={i%3,(i/3)%3,(i/9)%3};
  for(int i=0;i<27;++i)for(int j=0;j<27;++j)for(int k=0;k<27;++k) {
    auto a=vectors[i],b=vectors[j],c=vectors[k];
    int d=a[0]*(b[1]*c[2]-b[2]*c[1])-b[0]*(a[1]*c[2]-a[2]*c[1])+c[0]*(a[1]*b[2]-a[2]*b[1]);
    allowed[i][j][k]=((d%3+3)%3)!=2;
  }
  for(dimension=3;dimension<=12;++dimension) {
    std::uint64_t total=0;
    for(int a=0;a<dimension;++a)for(int b=a+1;b<dimension;++b)for(int c=b+1;c<dimension;++c) {
      int pivots[3]={a,b,c};
      for(int j=0;j<dimension;++j) {
        options[j].clear();int pivot=-1,seen=0;
        for(int r=0;r<3;++r) {if(pivots[r]==j)pivot=r;if(pivots[r]<j)++seen;}
        if(pivot>=0) {options[j].push_back(pivot==0?1:(pivot==1?3:9));continue;}
        for(int mask=0;mask<(1<<seen);++mask) {
          Col v={0,0,0};
          for(int r=0;r<seen;++r)if(mask>>r&1) v[r]=((r+seen-1)%2==0)?1:2;
          options[j].push_back(v[0]+3*v[1]+9*v[2]);
        }
      }
      total+=search(0);
    }
    std::cout<<dimension<<" "<<total<<std::endl;
  }
}

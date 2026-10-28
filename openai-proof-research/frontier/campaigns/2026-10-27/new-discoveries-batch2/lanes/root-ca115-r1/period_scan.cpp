#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <chrono>

// Literal second-order rule115 from arXiv2606.13159v1 Eq.(1), Table1.
// Outside the represented interval, both rows follow the uniform 3-cycle.
int main(int argc, char **argv) {
  unsigned max_k = argc > 1 ? std::strtoul(argv[1], nullptr, 10) : 11;
  std::uint64_t cap = argc > 2 ? std::strtoull(argv[2], nullptr, 10) : 120000000;
  for (unsigned k = 0; k <= max_k; ++k) {
    unsigned width = 2*k+7, center = k+3;
    if (width >= 63 || k+2 >= 31) return 2;
    const std::uint64_t mask = (std::uint64_t(1)<<width)-1;
    std::uint64_t b0 = std::uint64_t(1)<<center, c0 = 0;
    // Current word1(01)^k centered on0; memory has exactly its origin set.
    for (unsigned j=0;j<=k;++j) c0 |= std::uint64_t(1)<<(3+2*j);
    std::uint64_t b=b0,c=c0,found=0;
    unsigned i=k/2;
    std::uint64_t predicted = (k&1) ? (std::uint64_t(1)<<(2*k+4))-1
      : (2*(std::uint64_t(1)<<(4*i+4))-7*(std::uint64_t(1)<<(2*i+2))+5)/3;
    std::uint64_t limit = predicted < cap ? predicted : cap;
    auto start=std::chrono::steady_clock::now();
    for (std::uint64_t step=1;step<=limit;++step) {
      // Current background is1 exactly at times congruent to1 modulo3.
      bool bg = ((step-1)%3)==1;
      std::uint64_t left=((c<<1)&mask)|(bg?1:0);
      std::uint64_t right=(c>>1)|(bg?(std::uint64_t(1)<<(width-1)):0);
      std::uint64_t delta=((~c)|(left&(~right)))&mask;
      std::uint64_t next=b^delta;
      b=c;c=next;
      if (step%3==0 && b==b0 && c==c0) {found=step;break;}
    }
    double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout << "{\"k\":"<<k<<",\"width\":"<<width
      <<",\"predicted\":"<<predicted<<",\"first_return\":"<<found
      <<",\"steps_checked\":"<<(found?found:limit)
      <<",\"seconds\":"<<seconds
      <<",\"status\":\""<<(found==predicted?"MATCH":found?"EARLIER_RETURN":limit==predicted?"NO_RETURN_AT_PREDICTED":"CAP_ONLY")
      <<"\"}\n"<<std::flush;
  }
}

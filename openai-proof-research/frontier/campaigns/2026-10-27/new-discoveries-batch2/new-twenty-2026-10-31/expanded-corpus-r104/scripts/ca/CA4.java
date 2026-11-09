import java.util.*;
import java.util.concurrent.atomic.*;
// r=4 exhaustive over balanced rules (32-bit truth tables with 16 ones) via Gosper's hack, split by lowest-word bit pattern.
public class CA4 {
  static final int r=4, W=32;
  static int[] mask=new int[r+2]; static long[] idN=new long[r+2];
  static boolean surj(long tt){
    int S=1<<r; int V=S*S; boolean[] fw=new boolean[V]; int[] q=new int[V]; int h=0,t=0;
    for(int u=0;u<S;u++){ int wu=u, wv=u|(1<<r); if(((tt>>wu)&1)!=((tt>>wv)&1)) continue;
      int id=(wu>>1)*S+(wv>>1); if(!fw[id]){fw[id]=true;q[t++]=id;}
      id=(wv>>1)*S+(wu>>1); if(!fw[id]){fw[id]=true;q[t++]=id;} }
    while(h<t){int id=q[h++]; int u=id/S,v=id%S; if(u==v) return false;
      for(int a=0;a<2;a++)for(int b=0;b<2;b++){int wu=u|(a<<r), wv=v|(b<<r); if(((tt>>wu)&1)!=((tt>>wv)&1)) continue;
        int nid=(wu>>1)*S+(wv>>1); if(!fw[nid]){fw[nid]=true;q[t++]=nid;} }}
    return true;
  }
  public static void main(String[] a) throws Exception {
    for(int w=0;w<W;w++){ int k=Integer.bitCount(w); mask[k]|=(1<<w); if((w&1)==1) idN[k]++; }
    int part=Integer.parseInt(a[0]), parts=Integer.parseInt(a[1]);
    AtomicLong cnt=new AtomicLong(), bad=new AtomicLong(), surjBad=new AtomicLong(), surjAll=new AtomicLong();
    // enumerate by top 8 bits value hi (0..255) assigned round-robin to parts; low 24 bits with (16-popcount(hi)) ones
    Thread[] th=new Thread[2];
    for(int tix=0;tix<2;tix++){ final int T=tix; th[tix]=new Thread(()->{
      for(int hi=0;hi<256;hi++){ if((hi%(2*parts))!=(2*part+T)) continue;
        int need=16-Integer.bitCount(hi); if(need<0||need>24) continue;
        long lo=(need==0)?0:((1L<<need)-1); long limit=1L<<24;
        while(lo<limit){
          int tt=(int)(((long)hi<<24)|lo); cnt.incrementAndGet();
          // prefix check
          int s1=0; int s2=0; boolean isBad=false;
          for(int n=0;n<=r+1;n++){ s1+=Integer.bitCount(tt&mask[n]); s2+=idN[n]; if(s1<s2){isBad=true;break;} }
          if(isBad){ bad.incrementAndGet(); long ttl=tt&0xffffffffL; if(surj(ttl)){ long c=surjBad.incrementAndGet(); if(c<20) System.out.println("VIOLATION rule="+Long.toBinaryString(ttl)); } }
          if(need==0) break;
          long c=lo&-lo, rr=lo+c; lo=(((rr^lo)>>>2)/c)|rr;
        }
      }}); th[tix].start(); }
    for(Thread x:th) x.join();
    System.out.println("part="+part+"/"+parts+" balanced="+cnt+" prefixViolatingBalanced="+bad+" surjectiveViolating="+surjBad);
  }
}

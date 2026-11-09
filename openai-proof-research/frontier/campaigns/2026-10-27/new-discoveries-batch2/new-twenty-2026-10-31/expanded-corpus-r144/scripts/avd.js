let seed=144;
function rand(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)/4294967296;}
function check(a){
 let n=a.length,N=1<<n,all=N-1,cv=new Int32Array(N),sz=new Int8Array(N),vc=Array(n).fill(0),vs=Array(n).fill(0),ec=Array(n*n).fill(0),es=Array(n*n).fill(0),c=0,s=0;
 for(let t=1;t<N;t++){let z=t&-t,b=31-Math.clz32(z),r=t^z;cv[t]=cv[r]|a[b]|z;sz[t]=sz[r]+1;}
 for(let t=0;t<N;t++){
  let miss=all^cv[t],k=sz[t];
  if(!miss){c++;s+=k;let out=all^t;
   while(out){let z=out&-out,v=31-Math.clz32(z);out^=z;vc[v]++;vs[v]+=k;
    let q=a[v]&t;if(q&&!(q&(q-1))){let u=31-Math.clz32(q);ec[u*n+v]++;es[u*n+v]+=k;}
   }
  }else if(!(miss&(miss-1))){let v=31-Math.clz32(miss);vc[v]++;vs[v]+=k;}
 }
 let vertex=vc.some((x,v)=>vs[v]*c<s*x),edge=false,minDelta=Infinity,maxDelta=-Infinity;
 for(let u=0;u<n;u++)for(let v=u+1;v<n;v++)if(a[u]>>v&1){
 let delta=s*(ec[u*n+v]+ec[v*n+u])-c*(es[u*n+v]+es[v*n+u]);
 if(delta>0)edge=true;minDelta=Math.min(delta,minDelta);maxDelta=Math.max(delta,maxDelta);
 }
 return {vertex,edge,c,s,minDelta,maxDelta};
}
let n=+process.argv[2],count=+process.argv[3],p=+process.argv[4],mode=process.argv[5]||'random',bad=0;
for(let it=0;it<count;it++){
 let a=Array(n).fill(0),j=0;
 for(let u=0;u<n;u++)for(let v=u+1;v<n;v++,j++)if(mode==='all'?(it/2**j|0)&1:rand()<p){a[u]|=1<<v;a[v]|=1<<u;}
 if(a.every(x=>x===0))continue;
 let r=check(a);
 if(!r.vertex||!r.edge){console.log(JSON.stringify({it,a,...r}));bad++;}
}
console.log(JSON.stringify({n,count,p,mode,bad,seed:144}));

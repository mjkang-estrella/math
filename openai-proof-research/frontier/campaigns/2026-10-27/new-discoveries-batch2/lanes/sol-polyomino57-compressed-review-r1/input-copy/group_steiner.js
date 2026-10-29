const fs=require('fs'),zlib=require('zlib'),path=require('path');const L=__dirname;
const rows=JSON.parse(fs.readFileSync(path.join(L,'group-domains.json')));let receipt=[];
for(const r of rows){const {a,b,e,V,G,adj}=r,n=V.length,k=G.length;
 if(G[0].length===0){receipt.push({a,b,e,status:'empty-constraint',lower:12});continue;}
 const N=1<<k,D=new Uint8Array(N*n);D.fill(12);const cover=new Uint32Array(n);
 for(let g=0;g<k;g++)for(const v of G[g])cover[v]|=1<<g;
 for(let v=0;v<n;v++)for(let m=cover[v];m;m=(m-1)&cover[v])D[m*n+v]=1;
 for(let m=1;m<N;m++){
  const off=m*n;
  for(let s=(m-1)&m;s;s=(s-1)&m){const t=m^s;if(s>t)continue;let so=s*n,to=t*n;for(let v=0;v<n;v++){let x=D[so+v]+D[to+v]-1;if(x<D[off+v])D[off+v]=x;}}
  for(let cost=1;cost<11;cost++)for(let v=0;v<n;v++)if(D[off+v]===cost)for(const w of adj[v])if(D[off+w]>cost+1)D[off+w]=cost+1;
 }
 let lower=12;for(let v=0;v<n;v++)lower=Math.min(lower,D[(N-1)*n+v]);
 const cert=zlib.gzipSync(D,{level:9,mtime:0});const file=`steiner-${a}-${b}-${e}.bin.gz`;fs.writeFileSync(path.join(L,file),cert);
 receipt.push({a,b,e,status:'dp',n,k,entries:D.length,compressed_bytes:cert.length,lower,file});
 console.log(a,b,e,n,k,D.length,cert.length,lower);if(lower<12)throw Error('counterexample state');
}
fs.writeFileSync(path.join(L,'steiner-receipt.json'),JSON.stringify(receipt,null,2)+'\n');

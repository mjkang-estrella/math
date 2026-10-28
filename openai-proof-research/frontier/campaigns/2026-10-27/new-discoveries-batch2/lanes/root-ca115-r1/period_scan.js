// Independent executable version of the literal rule115 table.
// Bit positions increase with spatial coordinate; boundaries follow the background.
'use strict';
const maxK=Number(process.argv[2] || 11), cap=Number(process.argv[3] || 120000000);
for(let k=0;k<=maxK;k++) {
  const width=2*k+7, center=k+3;
  if(width>30) throw Error('32-bit implementation width exceeded');
  const mask=2**width-1;
  const b0=2**center;
  let c0=0;
  for(let j=0;j<=k;j++) c0|=2**(3+2*j);
  let b=b0,c=c0,found=0;
  const i=Math.floor(k/2);
  const predicted=k%2 ? 2**(2*k+4)-1 : (2*4**(2*i+2)-7*4**(i+1)+5)/3;
  const limit=Math.min(cap,predicted), start=Date.now();
  for(let step=1;step<=limit;step++) {
    const bg=(step-1)%3===1;
    const left=((c<<1)&mask)|(bg?1:0);
    const right=(c>>>1)|(bg?2**(width-1):0);
    const delta=((~c)|(left&(~right)))&mask;
    const next=b^delta;
    b=c;c=next;
    if(step%3===0&&b===b0&&c===c0) {found=step;break;}
  }
  console.log(JSON.stringify({k,width,predicted,first_return:found,steps_checked:found||limit,
    seconds:(Date.now()-start)/1000,
    status:found===predicted?'MATCH':found?'EARLIER_RETURN':limit===predicted?'NO_RETURN_AT_PREDICTED':'CAP_ONLY'}));
}

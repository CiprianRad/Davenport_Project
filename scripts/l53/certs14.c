// SPDX-License-Identifier: Apache-2.0
// For each 14-term rep (one per line), find a +-1 I_1 certificate with 5 zero sets: A+B+C = D+E.
// Output: codes... | A B C ; D E   (masks over positions). Fallback marker "NONE".
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#define N 14
static int ADD[64][64];
int main(int argc,char**argv){
  for(int a=0;a<64;a++) for(int b=0;b<64;b++){ int r=0; for(int i=0;i<3;i++){ int s=(((a>>(2*i))&3)+((b>>(2*i))&3))&3; r|=s<<(2*i);} ADD[a][b]=r; }
  FILE *f=fopen(argv[1],"r"); int (*seqs)[N]=malloc(sizeof(int)*N*100000); int n=0;
  while(fscanf(f,"%d",&seqs[n][0])==1){ for(int i=1;i<N;i++) if(fscanf(f,"%d",&seqs[n][i])!=1) return 1; n++; }
  char **out=calloc(n,sizeof(char*)); int none=0;
  #pragma omp parallel for schedule(dynamic,8) reduction(+:none)
  for(int s=0;s<n;s++){
    int *c=seqs[s]; static __thread int sum[1<<N]; static __thread unsigned char isz[1<<N]; static __thread int Z[1<<N];
    int nz=0; sum[0]=0; isz[0]=0;
    for(int m=1;m<(1<<N);m++){ int b=__builtin_ctz(m); sum[m]=ADD[sum[m&(m-1)]][c[b]]; isz[m]=sum[m]==0; if(isz[m]) Z[nz++]=m; }
    int found=0; char buf[256];
    for(int i=0;i<nz&&!found;i++) for(int j=i+1;j<nz&&!found;j++){
      int D=Z[i],E=Z[j]; int U=D^E, I=D&E, W=D|E;
      for(int a=0;a<nz&&!found;a++){ int A=Z[a]; if(A&~W) continue; if((I&~A)==I && 0) {}
        for(int b=a+1;b<nz&&!found;b++){ int B=Z[b]; if(B&~W) continue; if(A&B&U) continue; if(I&~(A|B)) continue;
          int C=(U&~A&~B)|(I&(A^B)); if(C==0||!isz[C]) continue;
          if(C==D||C==E||A==D||A==E||B==D||B==E) {} // repeated masks are fine (coefficients add up) but avoid degenerate
          sprintf(buf,"%d %d %d ; %d %d",A,B,C,D,E); found=1; }
      }
    }
    if(!found){ none++; sprintf(buf,"NONE"); }
    out[s]=strdup(buf);
  }
  FILE *o=fopen(argv[2],"w");
  for(int s=0;s<n;s++){ for(int i=0;i<N;i++) fprintf(o,"%d ",seqs[s][i]); fprintf(o,"| %s\n",out[s]); }
  fclose(o); printf("reps=%d none=%d\n",n,none);
}

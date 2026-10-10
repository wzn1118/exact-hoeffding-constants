#!/usr/bin/env python3
"""80-digit evaluation of the variance and Laplace envelopes."""
from math import comb
import mpmath as mp
mp.mp.dps=80
cases=[(7,3,3),(15,7,3),(31,3,3),(101,50,17),(101,50,50),(1001,500,30),(1001,500,500),(10001,5000,100)]
count=0
for N,k,m in cases:
 p=mp.mpf(k)/N;q=1-p;d=q-p;M=mp.mpf(m*(N-m))/(N-1);a=mp.mpf(N-2*m)/(N-2)
 mass=[mp.mpf(comb(k,i)*comb(N-k,m-i))/comb(N,m) for i in range(m+1)]
 minvar=mp.inf;minlap=mp.inf
 for t in [mp.mpf(-3),mp.mpf('-0.1'),4/mp.mpf(N),mp.mpf('0.1'),mp.mpf(3)]:
  weights=[mass[i]*mp.exp(t*(i-m*p)) for i in range(m+1)]
  total=mp.fsum(weights);y=mp.fsum((i-m*p)*weights[i] for i in range(m+1))/total
  v=mp.fsum((i-m*p-y)**2*weights[i] for i in range(m+1))/total
  P=M*p*q+a*d*y-a*a*y*y/M
  psi=mp.log(total);U=M/(a*a)*(mp.log(q+p*mp.exp(a*t))-p*a*t)
  assert P>v and U>psi,(N,k,m,t,P-v,U-psi)
  minvar=min(minvar,P-v);minlap=min(minlap,U-psi);count+=1
 print(f'N={N},k={k},m={m}: min tested (P-v)={mp.nstr(minvar,14)}, min tested (U-psi)={mp.nstr(minlap,14)}')
print(f'PASS: {count} direct-mass, 80-digit comparisons; each uses nonzero tilt.')

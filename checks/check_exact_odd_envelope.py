#!/usr/bin/env python3
"""Exact rational evaluation of the mean-dependent variance envelope."""
from fractions import Fraction as Q
from math import comb
count=0
for N in range(7,62,2):
 for m in range(3,(N-1)//2+1):
  M=Q(m*(N-m),N-1); a=Q(N-2*m,N-2)
  for k in range(m,(N-1)//2+1):
   p=Q(k,N); d=1-2*p
   for z in [Q(1,20),Q(1,2),Q(9,10),Q(1),Q(11,10),Q(2),Q(20)]:
    w=[comb(k,i)*comb(N-k,m-i)*z**i for i in range(m+1)]
    total=sum(w);u=sum(i*x for i,x in enumerate(w))/total
    v=sum((i-u)**2*x for i,x in enumerate(w))/total
    y=u-m*p;P=M*p*(1-p)+a*d*y-a*a*y*y/M
    assert P>=v,(N,k,m,z,P-v)
    assert (P==v)==(z==1),(N,k,m,z,P-v)
    count+=1
print(f'PASS: {count} exact rational parameter/tilt checks; equality iff tilt is zero.')

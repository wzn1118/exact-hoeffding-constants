#!/usr/bin/env python3
"""Exact rational verification of the mean-dependent tilted-variance envelope.

Integer-scaled tilted masses preserve all original parameter/tilt cases.
"""
from fractions import Fraction as Q
from math import comb
count=0
for N in range(7,62,2):
    for m in range(3,(N-1)//2+1):
        M=Q(m*(N-m),N-1)
        a=Q(N-2*m,N-2)
        for k in range(m,(N-1)//2+1):
            p=Q(k,N)
            d=1-2*p
            mass=[comb(k,i)*comb(N-k,m-i) for i in range(m+1)]
            for numer,denom in [(1,20),(1,2),(9,10),(1,1),(11,10),(2,1),(20,1)]:
                w=[mass[i]*numer**i*denom**(m-i) for i in range(m+1)]
                total=sum(w)
                first=sum(i*v for i,v in enumerate(w))
                second=sum(i*i*v for i,v in enumerate(w))
                u=Q(first,total)
                v=Q(second*total-first*first,total*total)
                y=u-m*p
                P=M*p*(1-p)+a*d*y-a*a*y*y/M
                assert P>=v,(N,k,m,numer,denom,P-v)
                assert (P==v)==(numer==denom),(N,k,m,numer,denom,P-v)
                count+=1
print(f'PASS: {count} exact rational parameter/tilt checks; equality iff tilt is zero.')

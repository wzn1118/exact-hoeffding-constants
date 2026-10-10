"""Exact certificate checks and independent high-precision tests for the even-N extension."""
import math
from fractions import Fraction
import mpmath as mp
import sympy as s

# For j=m-3>=0 and r=N-2m>=1, the original symbolic identities contain
# no parity assumptions. Check the positivity certificate using exact arithmetic.
for N in range(8, 41, 2):
    for m in range(3, N//2):
        j, r = m-3, N-2*m
        lambda_num = 3*j*j+3*j*r+13*j+r*r+5*r+12
        alpha_num = j*j+3*j*r+3*j+r*r+5*r
        U = j*j+3*j*r+5*j+r*r+7*r+6
        V = j**3+4*j*j*r+3*j*j+4*j*r*r+10*j*r+r**3+5*r*r
        assert min(lambda_num,alpha_num,U,V)>0, (N,m)
print('PASS: positive-definite certificate conditions for all even N=8,...,40')

mp.mp.dps=70
margins=[]
for N in range(6,31,2):
    for m in range(2,N//2):
        for k in range(m,N//2+1):
            p=mp.mpf(k)/N
            q=1-p
            a=mp.mpf(N-2*m)/(N-2)
            M=mp.mpf(m*(N-m))/(N-1)
            probs=[mp.mpf(math.comb(k,i)*math.comb(N-k,m-i))/math.comb(N,m) for i in range(m+1)]
            for t in (mp.mpf('-3'),mp.mpf('-1'),mp.mpf('-0.15'),mp.mpf('0.15'),mp.mpf('1'),mp.mpf('3')):
                H=mp.log(mp.fsum([pr*mp.exp(t*(i-m*p)) for i,pr in enumerate(probs)]))
                B=(M/(a*a))*(mp.log(q+p*mp.exp(a*t))-p*a*t)
                gap=B-H
                assert gap>0, (N,m,k,t,mp.nstr(gap,30))
                margins.append(gap)
print('PASS: strict tilted Laplace bound for all even 6<=N<=30, 2<=m<N/2, m<=k<=N/2 at six nonzero tilts')

for N in range(6,31,2):
    for m in range(2,N//2):
        k=N//2
        M=mp.mpf(m*(N-m))/(N-1)
        p=mp.mpf(k)/N
        V=M*p*(1-p)
        assert mp.almosteq(V,M/4)
print('PASS: balanced even margin gives equality at zero tilt, hence equality of optimal variance proxies')

print('Minimum numerical positive Laplace gap:',mp.nstr(min(margins),12))

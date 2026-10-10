"""Exact rational probability-mass evaluation of the curvature bound."""
from fractions import Fraction
from math import comb
NCASES=0
for N in range(2,29):
  for k in range(1,N):
    for m in range(1,N):
      lo=max(0,m+k-N); hi=min(k,m)
      nums=[comb(k,i)*comb(N-k,m-i) for i in range(lo,hi+1)]
      indices=range(lo,hi+1)
      bound=Fraction(min(k*(N-k),m*(N-m)),4*(N-1))
      for z in [Fraction(1,16),Fraction(1,4),Fraction(1,1),Fraction(4,1),Fraction(16,1)]:
        vals=[Fraction(a)*z**i for i,a in zip(indices,nums)]
        Z=sum(vals)
        mean=sum(Fraction(i)*a for i,a in zip(indices,vals))/Z
        var=sum((Fraction(i)-mean)**2*a for i,a in zip(indices,vals))/Z
        assert var<=bound,(N,k,m,z,var,bound)
        NCASES+=1
print('PASS: exact rational PMF evaluations:',NCASES,'integer parameter/tilt cases for N=2..28')

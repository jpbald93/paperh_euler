from sympy import *
a,b,c,u=symbols('a b c u')
p=a+b+c
gram=(2*a**2*b**2+2*b**2*c**2+2*c**2*a**2-a**4-b**4-c**4)/4
w=[a*u,b*u,c*u]; g=[Rational(1,3)]*3
d=[wi-gi for wi,gi in zip(w,g)]
d2={(0,1):c**2,(1,2):a**2,(2,0):b**2}
L=-(2*d[0]*d[1]*c**2+2*d[1]*d[2]*a**2+2*d[2]*d[0]*b**2)/2
D=expand(L-p**2/36-Rational(5,9)*u**2*gram+Rational(8,9)*a*b*c*u)
P=Poly(D,u); D0=P.coeff_monomial(1); D1=P.coeff_monomial(u); D2=P.coeff_monomial(u**2)
print(expand(D0*p**2+D1*p+D2))
cu=-(D0*(1+p*u)+D1*u)
print(expand(D - cu*(p*u-1)))
print(factor(D0), '|', factor(D1))

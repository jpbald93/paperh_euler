from sympy import *
x,y,z,X,Y,Z,D,E,R,r,s=symbols('x y z X Y Z D E R r s')
G=lambda x,y,z:2*(x*y+y*z+z*x)-x**2-y**2-z**2
L=X*(y+z-x)+Y*(z+x-y)+Z*(x+y-z)
S=x+y+z;T=X+Y+Z
lhs=2*S*T*(L-D*E); rhs=(T*D-S*E)**2+2*((T*x-S*X)**2+(T*y-S*Y)**2+(T*z-S*Z)**2)
diff=expand(lhs-rhs)
# reduce with D^2=G(x,y,z), E^2=G(X,Y,Z)
q=expand(diff.subs(D**2,G(x,y,z)).subs(E**2,G(X,Y,Z)))
print("pedoe residual", simplify(q))
print("coeffs:", factor(diff.coeff(D,2)), factor(diff.coeff(E,2)))
# Kooi
K=R*(4*R+r)**2/(2*(2*R-r))
B=2*R**2+10*R*r-r**2; C=r*(4*R+r)**3
f=lambda u:u**2-2*B*u+C
print("K-B", factor(together(K-B)))
print("f(K)", factor(together(f(K))))

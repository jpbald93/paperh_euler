from mpmath import mp, mpf, sqrt, rand, matrix
import random
mp.dps=30
def tri():
    k=random.random()
    if k<0.3: # near-degenerate
        A=(mpf(0),mpf(0)); B=(mpf(1),mpf(0)); C=(rand()*3-1, mpf(10)**(-random.randint(3,8)))
    else:
        A,B,C=[(rand()*4-2,rand()*4-2) for _ in range(3)]
    return A,B,C
def d(P,Q): return sqrt((P[0]-Q[0])**2+(P[1]-Q[1])**2)
def comb(w,Ps): return (sum(wi*P[0] for wi,P in zip(w,Ps)), sum(wi*P[1] for wi,P in zip(w,Ps)))
mx=0; mxi=mpf(0)
for it in range(2000):
    A,B,C=tri(); Ps=[A,B,C]
    a,b,c=d(B,C),d(C,A),d(A,B); s=(a+b+c)/2
    D=abs((B[0]-A[0])*(C[1]-A[1])-(C[0]-A[0])*(B[1]-A[1]))/2
    # circumcenter
    ax,ay=A;bx,by=B;cx,cy=C
    dd=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    ux=((ax**2+ay**2)*(by-cy)+(bx**2+by**2)*(cy-ay)+(cx**2+cy**2)*(ay-by))/dd
    uy=((ax**2+ay**2)*(cx-bx)+(bx**2+by**2)*(ax-cx)+(cx**2+cy**2)*(bx-ax))/dd
    O=(ux,uy); R=d(O,A); r=D/s
    I=comb([a/(2*s),b/(2*s),c/(2*s)],Ps)
    G=comb([mpf(1)/3]*3,Ps); H=(A[0]+B[0]+C[0]-2*ux, A[1]+B[1]+C[1]-2*uy)
    sides=[a,b,c]; res=[]
    res.append(d(I,O)**2-(R**2-2*R*r))
    for i in range(3):
        eps=[1,1,1]; eps[i]=-1
        S=sum(e*x for e,x in zip(eps,sides))
        X=comb([e*x/S for e,x in zip(eps,sides)],Ps)
        ri=D/(s-sides[i])
        res.append(d(X,O)**2-(R**2+2*R*ri))
        # exradius = dist to line? check dist to side opposite i
    res.append(d(O,G)**2-(R**2-(a*a+b*b+c*c)/9))
    res.append(d(O,H)**2-(9*R**2-(a*a+b*b+c*c)))
    res.append(d(I,G)**2-(s**2+5*r**2-16*R*r)/9)
    res.append(4*R*D-a*b*c); res.append(D**2-s*(s-a)*(s-b)*(s-c))
    scale=1+R**2
    mx=max(mx,max(abs(x) for x in res)/scale)
    # inequalities
    assert 2*r<=R*(1+mpf(10)**-25)
    W=a*a+b*b+c*c-4*sqrt(3)*D; HF=W-((a-b)**2+(b-c)**2+(c-a)**2)
    assert HF>=-mpf(10)**-20 and W>=HF-mpf(10)**-20
    assert 16*R*r-5*r*r<=s*s*(1+mpf(10)**-25) and s*s<=(4*R*R+4*R*r+3*r*r)*(1+mpf(10)**-25)
print("max rel residual", mx)
# equilateral
A,B,C=(mpf(0),mpf(0)),(mpf(1),mpf(0)),(mpf(1)/2,sqrt(3)/2)
D=sqrt(3)/4; s=mpf(3)/2; r=D/s; R=1/sqrt(3); print("equi R-2r",R-2*r,"HF",3-4*sqrt(3)*D)

import mpmath as mp, random
mp.mp.dps=30
random.seed(1)
def tri(kind):
    if kind=='nd':  # near-degenerate
        A=mp.matrix([0,0]);B=mp.matrix([1,0]);C=mp.matrix([mp.mpf(random.random()),mp.mpf(1e-6)*random.random()])
    elif kind=='obt':
        A=mp.matrix([0,0]);B=mp.matrix([1,0]);C=mp.matrix([mp.mpf(random.random())*0.8+0.1,mp.mpf(random.random())*0.2+0.01])
    else:
        A,B,C=[mp.matrix([mp.mpf(random.gauss(0,1)),mp.mpf(random.gauss(0,1))]) for _ in range(3)]
    return A,B,C
d=lambda P,Q:mp.norm(P-Q)
def data(A,B,C):
    a,b,c=d(B,C),d(C,A),d(A,B); s=(a+b+c)/2
    D=mp.sqrt(max(s*(s-a)*(s-b)*(s-c),0)); R=a*b*c/(4*D); r=D/s
    return a,b,c,s,D,R,r
worst={}
def upd(k,v):
    worst[k]=min(worst.get(k,mp.inf),v)
for it in range(3000):
    k=random.choice(['g','nd','obt'])
    A,B,C=tri(k); a,b,c,s,D,R,r=data(A,B,C)
    A2,B2,C2=tri(random.choice(['g','nd','obt'])); a2,b2,c2,s2,D2,_,_=data(A2,B2,C2)
    upd('pedoe',a2**2*(b**2+c**2-a**2)+b2**2*(c**2+a**2-b**2)+c2**2*(a**2+b**2-c**2)-16*D*D2)
    # pedoe equality for similar triangle (scaled, rotated)
    kk=mp.mpf(random.random()*3+0.1)
    upd('pedoe_sim_abs',-abs(kk**2*(a**2*(b**2+c**2-a**2)+b**2*(c**2+a**2-b**2)+c**2*(a**2+b**2-c**2))-16*D*D*kk**2))
    X=mp.matrix([mp.mpf(random.gauss(0,1)),mp.mpf(random.gauss(0,1))])
    upd('ptolemy',d(A,B)*d(C,X)+d(B,C)*d(A,X)-d(A,C)*d(B,X))
    upd('kooi',R*(4*R+r)**2/(2*(2*R-r))-s**2)
    upd('kooi_vs_gerretsen',(4*R**2+4*R*r+3*r**2)-R*(4*R+r)**2/(2*(2*R-r)))
    G=(A+B+C)/3
    upd('leibniz',d(X,A)**2+d(X,B)**2+d(X,C)**2-(a*a+b*b+c*c)/3 - 3*d(X,G)**2 if False else d(X,A)**2+d(X,B)**2+d(X,C)**2-(a*a+b*b+c*c)/3)
    upd('leibniz_identity_abs',-abs(d(X,A)**2+d(X,B)**2+d(X,C)**2-(a*a+b*b+c*c)/3-3*d(X,G)**2))
    upd('isoper',(a+b+c)**2-12*mp.sqrt(3)*D)
for k,v in worst.items(): print(k, mp.nstr(v,8))
# Kooi equality: scan isosceles triangles apex angle
print("Kooi gap along isosceles family (apex angle t):")
for t in [0.3,0.8,1.0,mp.pi/3,1.1,1.5,2.0,2.8]:
    A=mp.matrix([0,0]);B=mp.matrix([1,0]);C=mp.matrix([mp.cos(t),mp.sin(t)])
    a,b,c,s,D,R,r=data(A,B,C)
    print(mp.nstr(t,6), mp.nstr(R*(4*R+r)**2/(2*(2*R-r))-s**2,8))
# minimize gap overall
f=lambda u,v: (lambda dd: dd[5]*(4*dd[5]+dd[6])**2/(2*(2*dd[5]-dd[6]))-dd[3]**2)(data(mp.matrix([0,0]),mp.matrix([1,0]),mp.matrix([u,v])))
best=min(((f(mp.mpf(u)/50,mp.mpf(v)/50),u,v) for u in range(-30,80) for v in range(1,100)))
print("grid min of Kooi gap", mp.nstr(best[0],6), "at C=",best[1]/50,best[2]/50, "(equilateral C=(0.5,0.866))")

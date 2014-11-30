ell=5
eta=150
rho=10
rhop=10

nh=10

def QuotientNear(a,b):
  "Gives the nearest integer to a/b"
  return (2*a+b)//(2*b)

def modNear(a,b):
  "Computes a mod b with a \in ]-b/2,b/2]"
  if b==2: return mod(a,2).lift()
  return a-b*QuotientNear(a,b)

def getCrtCoeffs(p):
  P=prod([pj for pj in p])
  return [ZZ(P/p[i])*(mod(ZZ(P/p[i]),p[i])^(-1)).lift() for i in range(ell)]

def crt(v,crt_coeffs):
  return sum([v[i]*crt_coeffs[i] for i in range(ell)])

def encrypt(m,g,z,p,x0,crt_coeffs,i=1):
  return mod(crt([(g[j]*ZZ.random_element(-2^rho,2^rho)+m[j])*z.inverse_mod(p[j])^i for j in range(ell)],crt_coeffs),x0).lift()

def genKey():
  p=[random_prime(2^eta,None,2^(eta-1)) for i in range(ell)]
  x0=prod([pj for pj in p])
  crt_coeffs=getCrtCoeffs(p)

  g=[ZZ.random_element(2^(rhop-1),2^rhop) for j in range(ell)]
  z=ZZ.random_element(x0)

  h=[ZZ.random_element(2^nh) for j in range(ell)]

  pzt=mod(sum([mod(h[j]*z^2*g[j].inverse_mod(p[j]),p[j]).lift()*ZZ(x0/p[j]) for j in range(ell)]),x0).lift()

  return p,x0,crt_coeffs,g,z,pzt

def decrypt(c,g,p,z,k=1):
  return [modNear(modNear(z^k*c,p[j]),g[j]) for j in range(ell)]

"Cheon attack against the native CLT scheme"
def clt_test():
  p,x0,crt_coeffs,g,z,pzt=genKey()
  print "ell=",ell
  print "eta=",eta

  zero=[0 for i in range(ell)]
  
  x=[encrypt(zero,g,z,p,x0,crt_coeffs) for i in range(ell)]
  r=[encrypt(zero,g,z,p,x0,crt_coeffs) for i in range(ell)]

  c0=encrypt(zero,g,z,p,x0,crt_coeffs,0)
  
  print [modNear(c0,p[j]) for j in range(ell)]

  W1=Matrix(ZZ,[[modNear(pzt*x[j]*c0*x[k],x0) for k in range(ell)] for j in range(ell)])
  W2=Matrix(ZZ,[[modNear(pzt*x[j]*x[k],x0) for k in range(ell)] for j in range(ell)])

  M=W1*W2.inverse()

  print M.eigenvalues()
  
  pp=random_prime(2^(2*nh+10))

  W1p=Matrix(GF(pp),W1)
  W2p=Matrix(GF(pp),W2)

  Mp=W1p*W2p.inverse()
  print [modNear(v.lift(),pp) for v in Mp.eigenvalues()]

  return

def boneh_keygen():
  p,x0,crt_coeffs,g,z,pzt = genKey()
  tL = encrypt([1]*(ell-1) + [0], g, z, p, x0, crt_coeffs, 1)
  tR = encrypt([0]*(ell-2)+[1,0], g, z, p, x0, crt_coeffs, 1)
  return p,x0,crt_coeffs,g,z,pzt,tL,tR,ell-2

def boneh_encrypt(m,g,z,p,x0,crt_coeffs,i=1):
  """
  Encrypt a message according to Boneh et al.'s scheme
  m should be of length ell-2
  """
  zeta = ZZ.random_element(g[-2])
  nuL  = ZZ.random_element(g[-1])
  nuR  = ZZ.random_element(g[-1])
  mL   = m + [zeta, nuL]
  mR   = [ZZ.random_element(gi) for gi in g[:-2]] + [zeta, nuR]
  xL   = encrypt(mL,g,z,p,x0,crt_coeffs,i)
  xR   = encrypt(mR,g,z,p,x0,crt_coeffs,i)
  return (xL, xR)

def boneh_test():
  p,x0,crt_coeffs,g,z,pzt,tL,tR,ellp=boneh_keygen()
  print "ell'=",ellp
  print "eta =",eta

  zero=[0 for i in range(ellp)]
  
  x=[boneh_encrypt(zero,g,z,p,x0,crt_coeffs,1) for i in range(2*ell)]
  r=[boneh_encrypt(zero,g,z,p,x0,crt_coeffs,0) for i in range(2*ell)]
  c0=boneh_encrypt([ZZ.random_element(gi) for gi in g[:-2]],g,z,p,x0,crt_coeffs,0)

  def coeffj(x,j):
    return modNear(x,p[j])

  ratios = [coeffj(c0[0],j) for j in range(ell)] + [coeffj(c0[1],j) for j in range(ell)]
  print ratios
  
  def wjk(c,j,k):
    aL = x[j][0]*c[0]*r[k][0]*tL
    aR = x[j][1]*c[1]*r[k][1]*tR
    return modNear(pzt*(aL - aR),x0)

  W1=Matrix(ZZ,[[wjk(c0,j,k) for k in range(2*ell)] for j in range(2*ell)])
  W2=Matrix(ZZ,[[wjk([1,1],j,k) for k in range(2*ell)] for j in range(2*ell)])

  M=W1*W2.inverse()

  eigens = M.eigenvalues()
  print eigens
  print "Found expected ratios?", sorted(ratios) == sorted(eigens)

  def trygcd(e,a,b):
    return gcd(x0, e.denominator()*a - e.numerator()*b)

  factors = [max(gcd(c0[0]-e,x0),gcd(c0[1]-e,x0)) for e in eigens]

  print factors
  return lcm(factors)==x0

def random_message(g):
  return [ZZ.random_element(gi) for gi in g]

def garg_keygen():
  p,x0,crt_coeffs,g,z,pzt = genKey()
  nk=5  # matrix size. In principle nk=2kappa+1

  T=Matrix(Integers(x0),[[ZZ.random_element(x0) for j in range(nk)] for i in range(nk)])
  #T=identity_matrix(Integers(x0),nk)

  zero=[0 for gi in g]

  s=vector(ZZ,[encrypt(random_message(g),g,z,p,x0,crt_coeffs,0) for i in range(nk//2)]+\
              [encrypt(zero,g,z,p,x0,crt_coeffs,0) for i in range(nk//2)]+\
              [encrypt(random_message(g),g,z,p,x0,crt_coeffs,0)])*T.inverse()

  t=T*vector(ZZ,[encrypt(zero,g,z,p,x0,crt_coeffs,0) for i in range(nk//2)]+\
              [encrypt(random_message(g),g,z,p,x0,crt_coeffs,0) for i in range(nk//2)]+\
              [encrypt(random_message(g),g,z,p,x0,crt_coeffs,0)])*pzt

  return p,x0,crt_coeffs,g,z,pzt,nk,T,s,t

def garg_encrypt(m,g,z,p,x0,crt_coeffs,nk,T,level=1):
  C=[[0 for j in range(nk)] for i in range(nk)]
  zero=[0 for gi in g]

  for i in range(nk):
    for j in range(nk):
      if i==j:
        if i==nk-1:
          u=m
        else:
          u=random_message(g)
      else:
        u=zero
      C[i][j]=encrypt(u,g,z,p,x0,crt_coeffs,level)

      #if i!=j:
      #  C[i][j]=0


  C=Matrix(Integers(x0),C)
  return T*C*T.inverse()

def wgarg(U,s,t,x0):
  return modNear((s*U*t).lift(),x0)

def garg_test():
  p,x0,crt_coeffs,g,z,pzt,nk,T,s,t=garg_keygen()

  print "primes=",sorted(p)

  zero=[0 for gi in g]

  x=[garg_encrypt(zero,g,z,p,x0,crt_coeffs,nk,T) for i in range(nk*ell)]
  r=[garg_encrypt(zero,g,z,p,x0,crt_coeffs,nk,T) for i in range(nk*ell)]

  c0=garg_encrypt(random_message(g),g,z,p,x0,crt_coeffs,nk,T,0)

  def coeffj(x,j):
    return modNear(x,p[j])

  plainc0=T.inverse()*c0*T
  ratios = [coeffj(plainc0[0][0].lift(),j) for j in range(ell)]
  print ratios

  W1=Matrix(ZZ,[[wgarg(x[j]*c0*r[k],s,t,x0) for k in range(nk*ell)] for j in range(nk*ell)])
  W2=Matrix(ZZ,[[wgarg(x[j]*r[k],s,t,x0) for k in range(nk*ell)] for j in range(nk*ell)])

  M=W1*W2.inverse()
  poly=M.charpoly()

  R=PolynomialRing(ZZ,'x')
  polyz=R(poly.coeffs())

  listfactors=[R(v[0].coeffs()) for v in poly.factor()]

  print "Primes pi=",sorted([gcd(pol(c0)[0][0],x0) for pol in listfactors])
  print sorted([gcd(pol(c0)[0][0],x0) for pol in listfactors]) == sorted(p)

# vim: ft=python

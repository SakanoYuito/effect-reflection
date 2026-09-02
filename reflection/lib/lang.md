# DS

## Syntax

```
Value V, W ::= x 
             | n 
             | \x. P
Comp  P, Q ::= return V 
             | V + W 
             | V W 
             | let x = P in Q 
             | handle P with x, k -> Q 
             | op V
PureCtx  F ::= []
             | let x = F in P
```

## Reduction Rules

```
[β.v]                         (\x. P) V -> P[V/x]
[η.v]                           \x. V x -> V  , if x ∉ fv(V)
[β.let]           let x = return V in P -> P[V/x]
[η.let]           let x = P in return x -> P
[assoc]   let y = (let x = P in Q) in R -> let x = P in let y = Q in R  , if x ∉ fv(R)
[δ.+]                           n1 + n2 -> return n  , where n = n1 + n2
[h.ret]  handle return V with x, k -> P -> return V
[β.op.S]  handle F[op V] with x, k -> P -> P[V/x, (\y. F[return y])/k]
```



# CPS

## Syntax

```
Root    R ::= \j. \m. P
Value   V ::= x 
            | n 
            | \x. \j. \m. P
CFrame  K ::= \v. \j. \m. P
Cont    J ::= j 
            | eps 
            | K :: J
MCont   M ::= m 
            | () 
            | <J, H> :: M
Handler H ::= h 
            | \v. \r. \j. \m. P
Term    P ::= J V M 
            | V W J M 
            | J (V + W) M 
            | M @ V J
```

## Reduction Rules

```
[β.v]            (\x. \j. \m. P) V J M -> P[V/x, J/j, M/m]
[η.v]              \x. \j. \m. V x j m -> V      , if x, j, m ∉ fv(V)
[β.let]     ((\v. \j. \m. P) :: J) V M -> P[V/v, J/j, M/m]
[η.let]       (\v. \j. \m. j v m) :: J -> J
[assoc]                  K1 :: K2 :: J -> (K1 ▷ K2) :: J
             where (\v. \j. \m. P) ▷ K = \v. \j. \m. P[(K :: j)/j]
[δ.+]                    J (n1 + n2) M -> J n M  ,  where n = n1 + n2
[h.ret]            eps V (<J, H> :: M) -> J V M
[β.op.S]         (<J0, H> :: M0) @ V J -> P[V/v, R/r, J0/j0, M0/m0]
             where H = \v. \r. \j0. \m0. P
               and R = \y. \j. \m. (J >> j) y m
                     where j'       >> j = ↑
					       eps      >> j = j
                           (K :: J) >> j = K :: (J >> j)
```


# CPS Translation

```
-- Top Level
P* = \j. \m. (P : j : m)

-- Value
x† = x
n† = n
(\x. P)† = \x. \j. \m. (P : j : m)

-- Computation
return V : J : M 
  = J V† M

V W : J : M 
  = V† W† J M

V + W : J : M
  = J (V† + W†) M

(let x = P in Q) : J : M
  = P : (Kq :: J) : M
    where Kq = \v. \j. \m. (Q[v/x] : j : m)

(handle P with x, k -> Q) : J : M
  = P : eps : (<J, H> :: M)
    where H = \v. \r. \j0. \m0. (Q[v/x, r/k] : j0 : m0)

op V : J : M
  = M @ V† J
```

# DS Translation

```
-- Root
(\j. \m. P)◇ = P#

-- Value
x♮ = x
n♮ = n
(\x. \j. \m. P)♮ = \x. P#

-- CFrame
(\v. \j. \m. P)♭ 
  = let v = [] in P#

-- Cont
j♭♭ = []
eps♭♭ = []
(K :: J)♭ = J♭♭[ K♭[] ]

-- MCont
m## = []
()## = []
(<J, H> :: M)## = M##[ J♭♭[ handle [] with H◇◇ ] ]

-- Handler
h◇◇ = ↑
(\v. \r. \j. \m. P)◇◇ = v, r -> P#

-- Term
(J V M)# = M##[ J♭♭[ return V♮ ] ]
(V W J M)# = M##[ J♭♭[ V♮ W♮ ] ]
(J (V + W) M)# = M##[ J♭♭[ V♮ + W♮ ] ]
(M @ V J)# = M##[ J♭♭[ op V♮ ] ]
```

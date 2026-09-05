# DS Calculus

## Syntax

```
Values       V, W ::= x | n | \x. P

Computations P, Q ::= return V
                    | V W
                    | V + W
                    | let x = P in Q
                    | handle P with x, k -> Q
                    | op V

Pure Contexts   F ::= []
                    | F[let x = [] in P]

Meta Contexts   G ::= [] 
                    | G[F[handle [] with x, k -> P]]

```

## Reduction Rules

```
[β.v]                           (\x. P) V --> P[V/x]
[η.v]                             \x. V x --> V                                  if x ∉ fv(V)     
[β.let]             let x = return V in P --> P[V/x]
[η.let]             let x = P in return x --> P
[assoc]     let x = (let y = P in Q) in R --> let y = P in (let x = Q in R)      if y ∉ fv(R)
[h.ret]    handle return V with x, k -> Q --> return V
[β.op]      handle F[op V] with x, k -> Q --> Q[V/x, (λy. F[return y])/k]
[δ.+]                             n1 + n2 --> return n  where n = n1 + n2
```
および任意の場所での congruence

# CPS Calculus

## Syntax

外から渡される継続 `j` はただ一箇所にかならず出現する. それがどこにあるのかで分類した
- Mode = `c` (current)  
`j` は現在の継続 `J` の末尾にある

- Mode = `s` (stored)  
`j` はメタ継続 `M` に保存されている

```
Root                R ::= \j. \m. P 

Values           V, W ::= n 
                        | x 
                        | \x. \j. \m. P
Handler             H ::= \v. \r. \j. \m. P
Continuation Frame  K ::= \v. \j. \m. P


Mode                μ ::= c | s

Continuation       Jc ::= j  | K :: Jc
                   Js ::= () | K :: Js

Meta-continuation  Mc ::= m
                   Ms ::= <Jc, H> :: Mc 
                        | <Js, H> :: Ms

Term                P ::= Jμ V Mμ
                        | Jμ (V + W) Mμ
                        | V W Jμ Mμ
                        | Mμ @ V Jμ
```

## Reduction rules
```
[β.v]          (\x. \j. \m. P) V Jμ Mμ   ->   P[V/x, Jμ/j, Mμ/m]
[η.v]              \x. \j. \m. V x j m   ->   V      , if x, j, m ∉ fv(V)
[β.let]   ((\v. \j. \m. P) :: Jμ) V Mμ   ->   P[V/v, Jμ/j, Mμ/m]
[η.let]      (\v. \j. \m. j v m) :: Jμ   ->   Jμ
[assoc]                 K1 :: K2 :: Jμ   ->   (K1 ▷ K2) :: Jμ
[δ.+]                  Jμ (n1 + n2) Mμ   ->   Jμ n Mμ  ,  where n = n1 + n2
[h.ret]            () V (<Jμ, H> :: Mμ)  ->   Jμ V Mμ
[β.op.S]      (<J0μ, H> :: M0μ) @ V Js   ->   P[V/v, R/r, J0μ/j0, M0μ/m0]
                            where H = \v. \r. \j0. \m0. P
                              and R = \y. \j. \m. (Js >> j) y m
```
および任意の場所での congruence

ここで

継続の合成 `K1 ▷ K2`
```
(\v. \j. \m. P) ▷ K2 = \v. \j. \m. P[(K2 :: j)/j]
```

閉じた継続の末尾を変数におきかえる操作 `Js >> j`
```
()       >> j = j
(K :: J) >> j = K :: (J >> j)
```

# CPS Translation

## Root
```
P* = \j. \m. (P : j : m)
```

## Value `V†`
```
x† = x
n† = n
(\x. P)† = \x. \j. \m. (P : j : m)
```

## Computation `P : Jμ : Mμ`
```
return V : Jμ : Mμ
  = Jμ V† Mμ

V W : Jμ : Mμ
  = V† W† Jμ Mμ

V + W : Jμ : Mμ
  = Jμ (V† + W†) Mμ
  
let x = P in Q : Jμ : Mμ
  = P : (Kq :: Jμ) : Mμ
    where Kq = \v. \j. \m. Q[v/x] : j : m

handle P with x, k -> Q : Jμ : Mμ
  = P : () : (<Jμ, H> :: Mμ)
    where H = \v. \r. \j0. \m0. Q[v/x, r/k] : j0 : m0

op V : Jμ : Mμ
  = Mμ @ V† Jμ
```

## Pure Context `F : Jμ`
```
[] : Jμ
  = Jμ

F[let x = [] in P] : Jμ
  = K :: (F : Jμ)
    where K = \v. \j. \m. (P[v/x] : j : m)
```

# DS Translation

## Root
```
(\j. \m. P)◇ = P♯
```

## Value `V♮`
```
x♮ = x
n♮ = n
(\x. \j. \m. P)♮ = \x. P♯
```

## Cont. frame `K♭`
```
(\x. \j. \m. P)♭
  = let x = [] in P♯
```

## Handler `H‡`
```
(\v. \r. \j. \m. P)‡
  = v, r → P♯
```

## Continuation `J♭♭`
```
j♭♭ = []
()♭♭ = []
(K :: J)♭♭ = J♭♭[K♭]
```

## Metacontinuation `M♯♯`
```
m♯♯ = []
(<J, H> :: M)♯♯ = M♯♯[J♭♭[handle [] with H‡]]
```

## Term `P♯`
```
(J V M)♯
  = M♯♯[J♭♭[return V♮]]

(J (V + W) M)♯
  = M♯♯[J♭♭[V♮ + W♮]]

(V W J M)♯
  = M♯♯[J♭♭[V♮ W♮]]

(M @ V J)♯
  = M♯♯[J♭♭[op V♮]]
```


# Proof 







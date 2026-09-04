module CPS where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Mode
data Mode : Set where
  current : Mode
  stored  : Mode

-- Terms
interleaved mutual
  data value[_]   (var : Set) : Set
  data frame[_]   (var : Set) : Set
  data cont[_]_   (var : Set) : Mode → Set
  data mcont[_]_  (var : Set) : Mode → Set
  data handler[_] (var : Set) : Set
  data term[_]    (var : Set) : Set

  data value[_] where
    -- x 
    Var : (x : var) → value[ var ]
    -- n 
    Num : (n : ℕ) → value[ var ] 
    -- λx. λj. λm. P
    Fun : (p : var → term[ var ]) → value[ var ] 
  
  data frame[_] where
    -- λx. λj. λm. P
    KLet : (p : var → term[ var ]) → frame[ var ]
  
  data cont[_]_ where
    -- j 
    JVar  : cont[ var ] current
    -- ()
    JNil  : cont[ var ] stored
    -- K :: J 
    JCons : {μ : Mode}
          → (k : frame[ var ]) 
          → (j :  cont[ var ] μ)
          → cont[ var ] μ

  data mcont[_]_ where
    -- m
    MVar  : mcont[ var ] current
    -- ⟨J, H⟩ :: M  
    MCons : {μ : Mode}
          → (j : cont[ var ] μ)
          → (h : handler[ var ])
          → (m : mcont[ var ] μ)
          → mcont[ var ] stored
  
  data handler[_] where
    -- λv. λr. λj. λm. P 
    HFun : (h : var → var → term[ var ]) 
         → handler[ var ] 
  
  data term[_] where 
    -- J V M 
    Send : {μ : Mode}
         → (j :  cont[ var ] μ)
         → (v : value[ var ])
         → (m : mcont[ var ] μ)
         → term[ var ]
    -- J (V + W) M
    Add  : {μ : Mode}
         → (j :  cont[ var ] μ)
         → (v : value[ var ])
         → (w : value[ var ])
         → (m : mcont[ var ] μ)
         → term[ var ]
    -- V W J M
    App  : {μ : Mode}
         → (v : value[ var ])
         → (w : value[ var ])
         → (j :  cont[ var ] μ)
         → (m : mcont[ var ] μ)
         → term[ var ]
    -- M @ V J 
    Op   : {μ : Mode}
         → (m : mcont[ var ] μ)
         → (v : value[ var ])
         → (j :  cont[ var ] μ)
         → term[ var ]

-- example
-- λx. λj. λm. j x m 
val1 : {var : Set} → value[ var ]
val1 = Fun (λ x → Send JVar (Var x) MVar)

-- λj. λm. ((λv. λj'. λm'. j' (v + 2) m') :: j) 1 m
term1 : {var : Set} → term[ var ] 
term1 = Send 
          (JCons 
            (KLet ((λ v → Add JVar (Var v) (Num 2) MVar))) 
             JVar) 
          (Num 1) MVar

-- λj. λm.
-- (<j,
--   (λv. λr. λj'. λm'. r v ((λy. λj''. λm''. j'' (y + 3) m'') :: j') m')> 
-- :: m) 
-- @ 1 ((λv. λj. λm. j (v + 2) m) :: ())
term2 : {var : Set} → term[ var ] 
term2 = 
  Op 
    (MCons JVar H MVar) 
    (Num 1)
    (JCons K+2 JNil)
  where
    K+2 = KLet λ v → Add JVar (Var v) (Num 2) MVar
    K+3 = KLet λ v → Add JVar (Var v) (Num 3) MVar
    H = HFun λ v r → App (Var r) (Var v) (JCons K+3 JVar) MVar

-- Substitutions 
-- Substitute a value
interleaved mutual
  data VSubst  {var : Set} : (var →    term[ var ]) → value[ var ] →    term[ var ] → Set  
  data VSubstV {var : Set} : (var →   value[ var ]) → value[ var ] →   value[ var ] → Set  
  data VSubstK {var : Set} : (var →   frame[ var ]) → value[ var ] →   frame[ var ] → Set
  data VSubstH {var : Set} : (var → handler[ var ]) → value[ var ] → handler[ var ] → Set    
  data VSubstJ {var : Set} : {μ : Mode} → (var →  cont[ var ] μ) → value[ var ] →  cont[ var ] μ → Set  
  data VSubstM {var : Set} : {μ : Mode} → (var → mcont[ var ] μ) → value[ var ] → mcont[ var ] μ → Set  
  
  data VSubstV where
    -- (x)[v/x] = v
    sVar= : {v : value[ var ]}
          → VSubstV (λ x → Var x) v v
    -- (y)[v/_] = y 
    sVar≠ : {v : value[ var ]} {y : var}
          → VSubstV (λ _ → Var y) v (Var y)
    -- (n)[v/_] = n 
    sNum  : {v : value[ var ]} {n : ℕ}
          → VSubstV (λ _ → Num n) v (Num n)
    -- (λx. λj. λm. P)[v/y] = (λx. λj. λm. P[v/y])
    sFun  : {p  : var → var → term[ var ]}
          → {v  : value[ var ]}
          → {p' : var → term[ var ]}
          → ((x : var) → VSubst (λ y → p y x) v (p' x))
          → VSubstV (λ y → Fun λ x → p y x) v (Fun λ x → p' x)

  data VSubstK where
    -- (λx. λj. λm. P)[v/y] = (λx. λj. λm. P[v/y])
    sKFun : {p  : var → var → term[ var ]}
          → {v  : value[ var ]}
          → {p' : var → term[ var ]}
          → ((x : var) → VSubst (λ y → p y x) v (p' x))
          → VSubstK (λ y → KLet λ x → p y x) v (KLet λ x → p' x)
    
  data VSubstJ where
    -- j[v/_] = j 
    sJVar  : {v : value[ var ]}
           → VSubstJ (λ _ → JVar) v JVar
    -- ()[v/_] = ()
    sJNil  : {v : value[ var ]}
           → VSubstJ (λ _ → JNil) v JNil
    -- (K :: J)[v/x] = (K[v/x]) :: (J[v/x])
    sJCons : {μ : Mode}
           → {v  : value[ var ]}
           → {k  : var → frame[ var ]}
           → {j  : var →  cont[ var ] μ}
           → {k' : frame[ var ]}
           → {j' :  cont[ var ] μ}
           → VSubstK k v k'
           → VSubstJ j v j'
           → VSubstJ (λ x → JCons (k x) (j x)) v (JCons k' j')

  data VSubstM where
    -- m[v/_] = m 
    sMVar  : {v : value[ var ]}
           → VSubstM (λ _ → MVar) v MVar
    -- (<J, H> :: M)[v/x] = <J[v/x], H[v/x]> :: M[v/x]
    sMCons : {μ  : Mode}
           → {v  : value[ var ]}
           → {j  : var → cont[ var ] μ}
           → {h  : var → handler[ var ]}
           → {m  : var → mcont[ var ] μ}
           → {j' : cont[ var ] μ}
           → {h' : handler[ var ]} 
           → {m' : mcont[ var ] μ}
           → VSubstJ j v j' 
           → VSubstH h v h' 
           → VSubstM m v m' 
           → VSubstM (λ x → MCons (j x) (h x) (m x)) v (MCons j' h' m')
  
  data VSubstH where
    -- (λv. λr. λj. λm. P)[w/x] = λv. λr. λj. λm. P[w/x]
    sHFun : {p  : var → var → var → term[ var ]}
          → {w  : value[ var ]}
          → {p' : var → var → term[ var ]}
          → ((v r : var) → VSubst (λ x → p x v r) w (p' v r))
          → VSubstH (λ x → HFun (p x)) w (HFun p')

  data VSubst where
    -- (J V M)[w/x] = J[w/x] V[w/x] M[w/x]
    sSend : {μ  : Mode}
          → {j  : var →  cont[ var ] μ}
          → {v  : var → value[ var ]}
          → {m  : var → mcont[ var ] μ}
          → {w  : value[ var ]}
          → {j' :  cont[ var ] μ}
          → {v' : value[ var ]}
          → {m' : mcont[ var ] μ}
          → VSubstJ j w j'
          → VSubstV v w v' 
          → VSubstM m w m' 
          → VSubst (λ x → Send (j x) (v x) (m x)) w (Send j' v' m')
    -- (J (V₁ + V₂) M)[w/x] = J[w/x] (V₁[w/x] + V₂[w/x]) M[w/x]
    sAdd  : {μ  : Mode}
          → {j   : var →  cont[ var ] μ}
          → {v₁  : var → value[ var ]}
          → {v₂  : var → value[ var ]}
          → {m   : var → mcont[ var ] μ}
          → {w   : value[ var ]}
          → {j'  :  cont[ var ] μ}
          → {v₁' : value[ var ]}
          → {v₂' : value[ var ]}
          → {m'  : mcont[ var ] μ}
          → VSubstJ j w j'
          → VSubstV v₁ w v₁'
          → VSubstV v₂ w v₂' 
          → VSubstM m w m' 
          → VSubst (λ x → Add (j x) (v₁ x) (v₂ x) (m x)) w (Add j' v₁' v₂' m')
    -- (V₁ V₂ J M)[w/x] = V₁[w/x] V₂[w/x] J[w/x] M[w/x]
    sApp  : {μ  : Mode}
          → {v₁  : var → value[ var ]}
          → {v₂  : var → value[ var ]}
          → {j   : var →  cont[ var ] μ}
          → {m   : var → mcont[ var ] μ}
          → {w   : value[ var ]}
          → {v₁' : value[ var ]}
          → {v₂' : value[ var ]}
          → {j'  :  cont[ var ] μ}
          → {m' : mcont[ var ] μ}
          → VSubstV v₁ w v₁'
          → VSubstV v₂ w v₂' 
          → VSubstJ j w j'
          → VSubstM m w m' 
          → VSubst (λ x → App (v₁ x) (v₂ x) (j x) (m x)) w (App v₁' v₂' j' m')
    -- (M @ V J)[w/x] = M[w/x] @ V[w/x] J[w/x] 
    sOp   : {μ  : Mode}
          → {m  : var → mcont[ var ] μ}
          → {v  : var → value[ var ]}
          → {j  : var →  cont[ var ] μ}
          → {w  : value[ var ]}
          → {m' : mcont[ var ] μ}
          → {v' : value[ var ]}
          → {j' :  cont[ var ] μ} 
          → VSubstM m w m'
          → VSubstV v w v'
          → VSubstJ j w j' 
          → VSubst (λ x → Op (m x) (v x) (j x)) w (Op m' v' j')

data VSubst2 {var : Set} : (var → var → term[ var ]) 
                        → value[ var ] → value[ var ]
                        → term[ var ] → Set where
  sSubst2 : {p   : var → var → term[ var ]}
          → {v w : value[ var ]}
          → {p'  : var → term[ var ]}
          → {p'' : term[ var ]}
          → ((y : var) → VSubst (λ x → p x y) v (p' y))
          → VSubst p' w p''
          → VSubst2 p v w p'' 

-- Substitute a continuation
_◁_ : Mode → Mode → Mode
current ◁ μ = μ
stored  ◁ μ = stored

JSubstJ : {μ ν : Mode} 
        → {var : Set} 
        → cont[ var ] ν → cont[ var ] μ → cont[ var ] (ν ◁ μ)
-- j[j'/j] = j'
JSubstJ JVar j = j
-- ()[j/_] = ()
JSubstJ JNil j = JNil
-- (K :: J)[j'/j] = K :: (J[j'/j])
JSubstJ (JCons k js) j = JCons k (JSubstJ js j)

-- Subsitute a continuation & a metacontinuation
JMSubstM : {μ ν : Mode}
         → {var : Set} 
         → mcont[ var ] ν
         → cont[ var ] μ
         → mcont[ var ] μ 
         → mcont[ var ] (ν ◁ μ)
-- m[j'/j, m'/m] = m'
JMSubstM MVar j m = m
-- (<J, H> :: M)[j'/j, m'/m] = <J[j'/j], H> :: M[j'/j, m'/m]
JMSubstM (MCons j' h m') j m = MCons (JSubstJ j' j) h (JMSubstM m' j m)

JMSubst  : {μ : Mode}
         → {var : Set}
         → term[ var ] 
         → cont[ var ] μ 
         → mcont[ var ] μ 
         → term[ var ] 
JMSubst (Send j v m)  j' m' = Send (JSubstJ j j') v (JMSubstM m j' m')
JMSubst (Add j v w m) j' m' = Add (JSubstJ j j') v w (JMSubstM m j' m')
JMSubst (App v w j m) j' m' = App v w (JSubstJ j j') (JMSubstM m j' m')
JMSubst (Op m v j)    j' m' = Op (JMSubstM m j' m') v (JSubstJ j j')


-- Reduction relations

composeK : {var : Set} → frame[ var ] → frame[ var ] → frame[ var ] 
-- (λx. λj. λm. P) ▷ K = λx. λj. λm. P[(K :: j)/j]
composeK (KLet p) k = KLet λ x → JMSubst (p x) (JCons k JVar) MVar

openJ : {var : Set} → cont[ var ] stored → cont[ var ] current
openJ JNil = JVar
openJ (JCons k j) = JCons k (openJ j)

interleaved mutual
  data Reduce  {var : Set} :  term[ var ] →  term[ var ] → Set
  data ReduceV {var : Set} : value[ var ] → value[ var ] → Set
  data ReduceK {var : Set} : frame[ var ] → frame[ var ] → Set
  data ReduceH {var : Set} : handler[ var ] → handler[ var ] → Set  
  data ReduceJ {var : Set} : {μ : Mode} → cont[ var ]  μ →  cont[ var ] μ → Set
  data ReduceM {var : Set} : {μ : Mode} → mcont[ var ] μ → mcont[ var ] μ → Set

  data Reduce where
    -- (λx. λj. λm. P) V J M → P[V/v, J/j, M/m]
    RBetaV : {μ  : Mode}
           → {p  : var → term[ var ]}
           → {v  : value[ var ]}
           → {j  :  cont[ var ] μ}
           → {m  : mcont[ var ] μ}
           → {p' :  term[ var ]}
           → VSubst p v p' 
           → Reduce (App (Fun p) v j m) 
                    (JMSubst p' j m)
    -- ((λx. λj. λm. P) :: J) V M → P[V/v, J/j, M/m]
    RBetaLet : {μ : Mode} 
             → {p  : var → term[ var ]}
             → {v  : value[ var ]}
             → {j  :  cont[ var ] μ}
             → {m  : mcont[ var ] μ}
             → {p' :  term[ var ]}
             → VSubst p v p' 
             → Reduce (Send (JCons (KLet p) j) v m)
                      (JMSubst p' j m)
    -- J (n₁ + n₂) M → J n M 
    RDelta+ : {μ : Mode} 
            → {j : cont[ var ] μ}
            → {n₁ n₂ : ℕ}
            → {m : mcont[ var ] μ}
            → Reduce (Add j (Num n₁) (Num n₂) m)
                     (Send j (Num (n₁ + n₂)) m)
    -- () V (<J, H> :: M) → J V M 
    RHandleRet : {μ : Mode} 
               → {j : cont[ var ] μ}
               → {v : value[ var ]}
               → {h : handler[ var ]}
               → {m : mcont[ var ] μ}
               → Reduce (Send JNil v (MCons j h m))
                        (Send j v m)
    -- (<J₀, H> :: M₀) @ V J → P[V/v, R/r, J₀/j₀, M₀/m₀] 
    -- where
    --   H = λv. λr. λj₀. λm₀. P 
    --   R = λy. λj. λm. (J ++ j) y m
    RHandleOp : {μ : Mode} 
              → {v : value[ var ]}
              → {jc : cont[ var ] stored}
              → {j₀ : cont[ var ] μ}
              → {m₀ : mcont[ var ] μ}
              → {p  : var → var → term[ var ]}
              → {p' : term[ var ]}
              → VSubst2 p v 
                  (Fun λ y → Send (openJ jc) (Var y) MVar) p'
              → Reduce (Op (MCons j₀ (HFun p) m₀) v jc)
                       (JMSubst p' j₀ m₀)

    -- congruence rules
    RSendJ : {μ : Mode} 
           → {j j' : cont[ var ] μ}
           → {v : value[ var ]}
           → {m : mcont[ var ] μ}
           → ReduceJ j j' 
           → Reduce (Send j v m) (Send j' v m)
    RSendV : {μ : Mode} 
           → {j : cont[ var ] μ}
           → {v v' : value[ var ]}
           → {m : mcont[ var ] μ}
           → ReduceV v v' 
           → Reduce (Send j v m) (Send j v' m)
    RSendM : {μ : Mode} 
           → {j : cont[ var ] μ}
           → {v : value[ var ]}
           → {m m' : mcont[ var ] μ}
           → ReduceM m m' 
           → Reduce (Send j v m) (Send j v m')
    RAppV  : {μ : Mode} 
           → {v v' w : value[ var ]}
           → {j : cont[ var ] μ}
           → {m : mcont[ var ] μ}
           → ReduceV v v'
           → Reduce (App v w j m) (App v' w j m) 
    RAppW  : {μ : Mode} 
           → {v w w' : value[ var ]}
           → {j : cont[ var ] μ}
           → {m : mcont[ var ] μ}
           → ReduceV w w'
           → Reduce (App v w j m) (App v w' j m)
    RAppJ  : {μ : Mode} 
           → {v w : value[ var ]}
           → {j j' : cont[ var ] μ}
           → {m : mcont[ var ] μ}
           → ReduceJ j j'
           → Reduce (App v w j m) (App v w j' m) 
    RAppM  : {μ : Mode} 
           → {v w : value[ var ]}
           → {j : cont[ var ] μ}
           → {m m' : mcont[ var ] μ}
           → ReduceM m m'
           → Reduce (App v w j m) (App v w j m')
    RAddV  : {μ : Mode} 
           → {v v' w : value[ var ]}
           → {j : cont[ var ] μ}
           → {m : mcont[ var ] μ}
           → ReduceV v v'
           → Reduce (Add j v w m) (Add j v' w m) 
    RAddW  : {μ : Mode} 
           → {v w w' : value[ var ]}
           → {j : cont[ var ] μ}
           → {m : mcont[ var ] μ}
           → ReduceV w w'
           → Reduce (Add j v w m) (Add j v w' m)
    RAddJ  : {μ : Mode} 
           → {v w : value[ var ]}
           → {j j' : cont[ var ] μ}
           → {m : mcont[ var ] μ}
           → ReduceJ j j'
           → Reduce (Add j v w m) (Add j' v w m) 
    RAddM  : {μ : Mode} 
           → {v w : value[ var ]}
           → {j : cont[ var ] μ}
           → {m m' : mcont[ var ] μ}
           → ReduceM m m'
           → Reduce (Add j v w m) (Add j v w m')
    ROpJ   : {μ : Mode} 
           → {j j' : cont[ var ] μ}
           → {v : value[ var ]}
           → {m : mcont[ var ] μ}
           → ReduceJ j j' 
           → Reduce (Op m v j) (Op m v j')
    ROpV   : {μ : Mode} 
           → {j : cont[ var ] μ}
           → {v v' : value[ var ]}
           → {m : mcont[ var ] μ}
           → ReduceV v v' 
           → Reduce (Op m v j) (Op m v' j)
    ROpM   : {μ : Mode} 
           → {j : cont[ var ] μ}
           → {v : value[ var ]}
           → {m m' : mcont[ var ] μ}
           → ReduceM m m' 
           → Reduce (Op m v j) (Op m' v j)

  data ReduceV where
    -- λx. λj. λm. V x j m → V 
    REtaV : {v : value[ var ]}
          → ReduceV (Fun λ x → (App v (Var x) JVar MVar)) v
    
    -- congruence rule 
    RFun : {p p' : var → term[ var ]}
         → ((x : var) → Reduce (p x) (p' x))
         → ReduceV (Fun p) (Fun p')

  data ReduceK where
    -- congruence rule 
    RKLet : {p p' : var → term[ var ]}
          → ((x : var) → Reduce (p x) (p' x))
          → ReduceK (KLet p) (KLet p') 

  data ReduceJ where
    -- (λx. λj. λm. j x m) :: J → J
    REtaLet : {μ : Mode}
            → {j : cont[ var ] μ}
            → ReduceJ 
                (JCons (KLet λ x → Send JVar (Var x) MVar) j) j
    -- K₁ :: K₂ :: J → (K₁ ▷ K₂) :: J
    RAssoc : {μ : Mode}
           → {k₁ k₂ : frame[ var ]}
           → {j : cont[ var ] μ}
           → ReduceJ (JCons k₁ (JCons k₂ j))
                     (JCons (composeK k₁ k₂) j)
    
    -- congruence rules
    RJConsK : {μ : Mode}
            → {k k' : frame[ var ]}
            → {j : cont[ var ] μ}
            → ReduceK k k' 
            → ReduceJ (JCons k j) (JCons k' j)
    RJConsJ : {μ : Mode}
            → {k : frame[ var ]}
            → {j j' : cont[ var ] μ}
            → ReduceJ j j'
            → ReduceJ (JCons k j) (JCons k j')
  
  data ReduceM where
    -- congruence rules
    RMConsJ : {μ : Mode}
            → {j j' : cont[ var ] μ}
            → {h : handler[ var ]}
            → {m : mcont[ var ] μ}
            → ReduceJ j j' 
            → ReduceM (MCons j h m) (MCons j' h m)
    RMConsH : {μ : Mode}
            → {j : cont[ var ] μ}
            → {h h' : handler[ var ]}
            → {m : mcont[ var ] μ}
            → ReduceH h h' 
            → ReduceM (MCons j h m) (MCons j h' m)
    RMConsM : {μ : Mode}
            → {j : cont[ var ] μ}
            → {h : handler[ var ]}
            → {m m' : mcont[ var ] μ}
            → ReduceM m m'
            → ReduceM (MCons j h m) (MCons j h m')
  
  data ReduceH where
    -- congruence rule
    RHFun : {p p' : var → var → term[ var ]}
          → ((v r : var) → Reduce (p v r) (p' v r))
          → ReduceH (HFun p) (HFun p')

data Star {A : Set} (_~_ : A → A → Set) : A → A → Set where
  Refl : {x : A} 
        → Star _~_ x x
  Step : {x y z : A}
        → x ~ y 
        → Star _~_ y z 
        → Star _~_ x z
  
Reduce*  : {var : Set} →    term[ var ] →    term[ var ] → Set
ReduceV* : {var : Set} →   value[ var ] →   value[ var ] → Set
ReduceK* : {var : Set} →   frame[ var ] →   frame[ var ] → Set  
ReduceH* : {var : Set} → handler[ var ] → handler[ var ] → Set
ReduceJ* : {var : Set} → {μ : Mode} →  cont[ var ] μ →  cont[ var ] μ → Set
ReduceM* : {var : Set} → {μ : Mode} → mcont[ var ] μ → mcont[ var ] μ → Set
Reduce*  = Star Reduce
ReduceV* = Star ReduceV
ReduceK* = Star ReduceK
ReduceJ* = Star ReduceJ
ReduceM* = Star ReduceM
ReduceH* = Star ReduceH

-- equational reasoning
module Reasoning {var : Set} where

  infix  1 begin_
  infixr 2 _⟶⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : {p q : term[ var ]} → Reduce* p q → Reduce* p q
  begin_ reds = reds

  _⟶⟨_⟩_ : (p {q r} : term[ var ]) → Reduce p q → Reduce* q r → Reduce* p r
  p ⟶⟨ red ⟩ reds = Step red reds

  _≡⟨_⟩_ : (p {q r} : term[ var ]) → p ≡ q → Reduce* q r → Reduce* p r
  _≡⟨_⟩_ p {q} {r} refl reds = reds

  _∎ : (p : term[ var ]) → Reduce* p p
  p ∎ = Refl

module OneStepReasoning {var : Set} where

  data Phase : Set where
    before after : Phase

  data Chain : Phase → term[ var ] → term[ var ] → Set where
    equal  : {p q : term[ var ]}
           → p ≡ q
           → Chain before p q

    single : {p q : term[ var ]}
           → Reduce p q
           → Chain after p q

  infix  1 begin_
  infixr 2 _⟶⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : {p q : term[ var ]}
         → Chain after p q
         → Reduce p q
  begin single red = red

  _≡⟨_⟩_ : {s : Phase}
           → (p {q r} : term[ var ])
           → p ≡ q
           → Chain s q r
           → Chain s p r
  p ≡⟨ refl ⟩ chain = chain


  _⟶⟨_⟩_ : (p {q r} : term[ var ])
           → Reduce p q
           → Chain before q r
           → Chain after p r
  p ⟶⟨ red ⟩ equal refl = single red

  _∎ : (p : term[ var ])
      → Chain before p p
  p ∎ = equal refl

-- examples
-- λj. λm. ((λv. λj'. λm'. j' (v + 2) m') :: j) 1 m
-- = λj. λm. j 3 m
ex1 : {var : Set} → Reduce* { var }
        (Send (JCons (KLet λ v → Add JVar (Var v) (Num 2) MVar) JVar) (Num 1) MVar)
        (Send JVar (Num 3) MVar)
ex1 = 
  begin
    Send (JCons (KLet (λ v → Add JVar (Var v) (Num 2) MVar)) JVar)
      (Num 1) MVar
  ⟶⟨ RBetaLet (sAdd sJVar sVar= sNum sMVar) ⟩
    Add JVar (Num 1) (Num 2) MVar
  ⟶⟨ RDelta+ ⟩
    Send JVar (Num 3) MVar
  ∎
  where open Reasoning

-- term2 = λj. λm. j 6 m
ex2 : {var : Set} → Reduce* { var } term2 (Send JVar (Num 6) MVar)
ex2 = 
  begin
    (Op 
      (MCons JVar H MVar) 
      (Num 1)
      (JCons K+2 JNil))
  ⟶⟨ RHandleOp
    (sSubst2
     (λ y →
        sApp sVar≠ sVar=
        (sJCons (sKFun (λ x → sAdd sJVar sVar≠ sNum sMVar)) sJVar) sMVar)
     (sApp sVar= sNum
      (sJCons (sKFun (λ x → sAdd sJVar sVar≠ sNum sMVar)) sJVar) sMVar)) ⟩
    JMSubst
          (App
           (Fun
            (λ y →
               Send (JCons (KLet (λ v → Add JVar (Var v) (Num 2) MVar)) JVar)
               (Var y) MVar))
           (Num 1) (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar) MVar)
          JVar MVar
  ≡⟨ refl ⟩
    App (Fun (λ y → Send (JCons (KLet (λ v → Add JVar (Var v) (Num 2) MVar)) JVar) (Var y) MVar)) 
            (Num 1) 
            (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) (JSubstJ JVar JVar)) 
            MVar
  ⟶⟨ RAppV (RFun (λ x → RBetaLet (sAdd sJVar sVar= sNum sMVar))) ⟩
    App (Fun (λ z → JMSubst (Add JVar (Var z) (Num 2) MVar) JVar MVar))
      (Num 1)
      (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar))
       (JSubstJ JVar JVar))
      MVar
  ⟶⟨ RBetaV (sAdd sJVar sVar= sNum sMVar) ⟩
    JMSubst (Add JVar (Num 1) (Num 2) MVar)
      (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar))
       (JSubstJ JVar JVar))
      MVar
  ≡⟨ refl ⟩
    Add (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar)
      (Num 1) (Num 2) MVar
  ⟶⟨ RDelta+ ⟩
    Send (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar)
      (Num (1 + 2)) MVar
  ⟶⟨ RBetaLet (sAdd sJVar sVar= sNum sMVar) ⟩
    JMSubst (Add JVar (Num (1 + 2)) (Num 3) MVar) JVar MVar
  ≡⟨ refl ⟩
    Add JVar (Num 3) (Num 3) MVar
  ⟶⟨ RDelta+ ⟩
    Send JVar (Num 6) MVar
  ∎
  where 
    open Reasoning
    K+2 = KLet λ v → Add JVar (Var v) (Num 2) MVar
    K+3 = KLet λ v → Add JVar (Var v) (Num 3) MVar
    H = HFun λ v r → App (Var r) (Var v) (JCons K+3 JVar) MVar
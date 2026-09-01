module CPS where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Terms
interleaved mutual
  data value[_]   (var : Set) : Set
  data frame[_]   (var : Set) : Set
  data cont[_]    (var : Set) : Set
  data mcont[_]   (var : Set) : Set
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
  
  data cont[_] where
    -- j 
    JVar  : cont[ var ]
    -- ()
    JNil  : cont[ var ]
    -- K :: J 
    JCons : (k : frame[ var ]) 
          → (j :  cont[ var ])
          → cont[ var ] 

  data mcont[_] where
    -- m
    MVar  : mcont[ var ]
    -- ()
    MNil  : mcont[ var ]
    -- ⟨J, H⟩ :: M  
    MCons : (j :  cont[ var ])
          → (h : handler[ var ])
          → mcont[ var ] 
          → mcont[ var ] 
  
  data handler[_] where
    -- λv. λr. λj. λm. P 
    HFun : (h : var → var → term[ var ]) → handler[ var ] 
  
  data term[_] where 
    -- J V M 
    Send : (j :  cont[ var ])
         → (v : value[ var ])
         → (m : mcont[ var ])
         → term[ var ]
    -- J (V + W) M
    Add  : (j :  cont[ var ])
         → (v : value[ var ])
         → (w : value[ var ])
         → (m : mcont[ var ])
         → term[ var ]
    -- V W J M
    App  : (v : value[ var ])
         → (w : value[ var ])
         → (j :  cont[ var ])
         → (m : mcont[ var ])
         → term[ var ]
    -- M @ V J 
    Op   : (m : mcont[ var ])
         → (v : value[ var ])
         → (j :  cont[ var ])
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
term2 = Op 
          (MCons 
            JVar 
            (HFun (λ v r → App 
                             (Var r) 
                             (Var v) 
                             (JCons (KLet λ y → Add JVar (Var y) (Num 3) MVar) JVar) 
                             MVar)) 
            MVar) 
          (Num 1) 
          (JCons 
            (KLet λ v → Add JVar (Var v) (Num 2) MVar) 
            JNil)

interleaved mutual
  data SubstV {var : Set} : (var →   value[ var ]) → value[ var ] →   value[ var ] → Set  
  data SubstK {var : Set} : (var →   frame[ var ]) → value[ var ] →   frame[ var ] → Set  
  data SubstJ {var : Set} : (var →    cont[ var ]) → value[ var ] →    cont[ var ] → Set  
  data SubstM {var : Set} : (var →   mcont[ var ]) → value[ var ] →   mcont[ var ] → Set  
  data SubstH {var : Set} : (var → handler[ var ]) → value[ var ] → handler[ var ] → Set  
  data Subst  {var : Set} : (var →    term[ var ]) → value[ var ] →    term[ var ] → Set  

  data SubstV where
    -- (x)[v/x] = v
    sVar= : {v : value[ var ]}
          → SubstV (λ x → Var x) v v
    -- (y)[v/_] = y 
    sVar≠ : {v : value[ var ]} {y : var}
          → SubstV (λ _ → Var y) v (Var y)
    -- (n)[v/_] = n 
    sNum  : {v : value[ var ]} {n : ℕ}
          → SubstV (λ _ → Num n) v (Num n)
    -- (λx. λj. λm. P)[v/y] = (λx. λj. λm. P[v/y])
    sFun  : {p  : var → var → term[ var ]}
          → {v  : value[ var ]}
          → {p' : var → term[ var ]}
          → ((x : var) → Subst (λ y → p y x) v (p' x))
          → SubstV (λ y → Fun λ x → p y x) v (Fun λ x → p' x)

  data SubstK where
    -- (λx. λj. λm. P)[v/y] = (λx. λj. λm. P[v/y])
    sKFun : {p  : var → var → term[ var ]}
          → {v  : value[ var ]}
          → {p' : var → term[ var ]}
          → ((x : var) → Subst (λ y → p y x) v (p' x))
          → SubstK (λ y → KLet λ x → p y x) v (KLet λ x → p' x)
    
  data SubstJ where
    -- j[v/_] = j 
    sJVar  : {v : value[ var ]}
           → SubstJ (λ _ → JVar) v JVar
    -- ()[v/_] = ()
    sJNil  : {v : value[ var ]}
           → SubstJ (λ _ → JNil) v JNil
    -- (K :: J)[v/x] = (K[v/x]) :: (J[v/x])
    sJCons : {v  : value[ var ]}
           → {k  : var → frame[ var ]}
           → {j  : var →  cont[ var ]}
           → {k' : frame[ var ]}
           → {j' :  cont[ var ]}
           → SubstK k v k'
           → SubstJ j v j'
           → SubstJ (λ x → JCons (k x) (j x)) v (JCons k' j')

  data SubstM where
    -- m[v/_] = m 
    sMVar  : {v : value[ var ]}
           → SubstM (λ _ → MVar) v MVar
    -- ()[v/_] = ()
    sMNil  : {v : value[ var ]}
           → SubstM (λ _ → MNil) v MNil
    -- (<J, H> :: M)[v/x] = <J[v/x], H[v/x]> :: M[v/x]
    sMCons : {v  : value[ var ]}
           → {j  : var → cont[ var ]}
           → {h  : var → handler[ var ]}
           → {m  : var → mcont[ var ]}
           → {j' : cont[ var ]}
           → {h' : handler[ var ]} 
           → {m' : mcont[ var ]}
           → SubstJ j v j' 
           → SubstH h v h' 
           → SubstM m v m' 
           → SubstM (λ x → MCons (j x) (h x) (m x)) v (MCons j' h' m')
  
  data SubstH where
    -- (λv. λr. λj. λm. P)[w/x] = λv. λr. λj. λm. P[w/x]
    sHFun : {p  : var → var → var → term[ var ]}
          → {w  : value[ var ]}
          → {p' : var → var → term[ var ]}
          → ((v r : var) → Subst (λ x → p x v r) w (p' v r))
          → SubstH (λ x → HFun (p x)) w (HFun p')

  data Subst where
    -- (J V M)[w/x] = J[w/x] V[w/x] M[w/x]
    sSend : {j  : var →  cont[ var ]}
          → {v  : var → value[ var ]}
          → {m  : var → mcont[ var ]}
          → {w  : value[ var ]}
          → {j' :  cont[ var ]}
          → {v' : value[ var ]}
          → {m' : mcont[ var ]}
          → SubstJ j w j'
          → SubstV v w v' 
          → SubstM m w m' 
          → Subst (λ x → Send (j x) (v x) (m x)) w (Send j' v' m')
    -- (J (V₁ + V₂) M)[w/x] = J[w/x] (V₁[w/x] + V₂[w/x]) M[w/x]
    sAdd  : {j   : var →  cont[ var ]}
          → {v₁  : var → value[ var ]}
          → {v₂  : var → value[ var ]}
          → {m   : var → mcont[ var ]}
          → {w   : value[ var ]}
          → {j'  :  cont[ var ]}
          → {v₁' : value[ var ]}
          → {v₂' : value[ var ]}
          → {m'  : mcont[ var ]}
          → SubstJ j w j'
          → SubstV v₁ w v₁'
          → SubstV v₂ w v₂' 
          → SubstM m w m' 
          → Subst (λ x → Add (j x) (v₁ x) (v₂ x) (m x)) w (Add j' v₁' v₂' m')
    -- (V₁ V₂ J M)[w/x] = V₁[w/x] V₂[w/x] J[w/x] M[w/x]
    sApp  : {v₁  : var → value[ var ]}
          → {v₂  : var → value[ var ]}
          → {j   : var →  cont[ var ]}
          → {m   : var → mcont[ var ]}
          → {w   : value[ var ]}
          → {v₁' : value[ var ]}
          → {v₂' : value[ var ]}
          → {j'  :  cont[ var ]}
          → {m' : mcont[ var ]}
          → SubstV v₁ w v₁'
          → SubstV v₂ w v₂' 
          → SubstJ j w j'
          → SubstM m w m' 
          → Subst (λ x → App (v₁ x) (v₂ x) (j x) (m x)) w (App v₁' v₂' j' m')
    -- (M @ V J)[w/x] = M[w/x] @ V[w/x] J[w/x] 
    sOp   : {m  : var → mcont[ var ]}
          → {v  : var → value[ var ]}
          → {j  : var →  cont[ var ]}
          → {w  : value[ var ]}
          → {m' : mcont[ var ]}
          → {v' : value[ var ]}
          → {j' :  cont[ var ]} 
          → SubstM m w m'
          → SubstV v w v'
          → SubstJ j w j' 
          → Subst (λ x → Op (m x) (v x) (j x)) w (Op m' v' j')


JSubstJ : {var : Set} → cont[ var ] → cont[ var ] → cont[ var ]
-- j[j'/j] = j'
JSubstJ JVar j = j
-- ()[j/_] = ()
JSubstJ JNil j = JNil
-- (K :: J)[j'/j] = K :: (J[j'/j])
JSubstJ (JCons k js) j = JCons k (JSubstJ js j)

JMSubstM : {var : Set} → mcont[ var ] → cont[ var ] → mcont[ var ] → mcont[ var ] 
-- m[j'/j, m'/m] = m'
JMSubstM MVar j m = m
-- ()[j'/_, m'/_] = ()
JMSubstM MNil j m = MNil
-- (<J, H> :: M)[j'/j, m'/m] = <J[j'/j], H> :: M[j'/j, m'/m]
JMSubstM (MCons j' h m') j m = MCons (JSubstJ j' j) h (JMSubstM m' j m)

JMSubst : {var : Set} → term[ var ] → cont[ var ] → mcont[ var ] → term[ var ]
JMSubst (Send j v m)  j' m' = Send (JSubstJ j j') v (JMSubstM m j' m')
JMSubst (Add j v w m) j' m' = Add (JSubstJ j j') v w (JMSubstM m j' m')
JMSubst (App v w j m) j' m' = App v w (JSubstJ j j') (JMSubstM m j' m')
JMSubst (Op m v j)    j' m' = Op (JMSubstM m j' m') v (JSubstJ j j')

KCompose : {var : Set} → frame[ var ] → frame[ var ] → frame[ var ] 
-- (λx. λj. λm. P) ▷ K = λx. λj. λm. P[(K :: j)/j]
KCompose (KLet p) k = KLet λ x → JMSubst (p x) (JCons k JVar) MVar

data JOpen {var : Set} : cont[ var ] → cont[ var ] → Set where
  -- () >> j = j 
  oNil  : JOpen JNil JVar
  -- (K :: J) >> j = K :: (J >> j)
  oCons : {k : frame[ var ]}
        → {j j' : cont[ var ]}
        → JOpen j j' 
        → JOpen (JCons k j) (JCons k j')

data Subst2 {var : Set} :
  (var → var → term[ var ]) → value[ var ] → value[ var ] → 
  term[ var ] → Set where

  sSubst2 : {p   : var → var → term[ var ]}
          → {v w : value[ var ]}
          → {p'  : var → term[ var ]}
          → {p'' : term[ var ]}
          → ((y : var) → Subst (λ x → p x y) v (p' y))
          → Subst p' w p''
          → Subst2 p v w p'' 


interleaved mutual
  data Reduce  {var : Set} :  term[ var ] →  term[ var ] → Set
  data ReduceV {var : Set} : value[ var ] → value[ var ] → Set
  data ReduceK {var : Set} : frame[ var ] → frame[ var ] → Set  
  data ReduceJ {var : Set} :  cont[ var ] →  cont[ var ] → Set
  data ReduceM {var : Set} : mcont[ var ] → mcont[ var ] → Set
  data ReduceH {var : Set} : handler[ var ] → handler[ var ] → Set

  data Reduce where
    -- (λx. λj. λm. P) V J M → P[V/v, J/j, M/m]
    RBetaV : {p  : var → term[ var ]}
           → {v  : value[ var ]}
           → {j  :  cont[ var ]}
           → {m  : mcont[ var ]}
           → {p' :  term[ var ]}
           → Subst p v p' 
           → Reduce (App (Fun λ x → p x) v j m) 
                    (JMSubst p' j m)
    -- ((λx. λj. λm. P) :: J) V M → P[V/v, J/j, M/m]
    RBetaLet : {p  : var → term[ var ]}
             → {v  : value[ var ]}
             → {j  :  cont[ var ]}
             → {m  : mcont[ var ]}
             → {p' :  term[ var ]}
             → Subst p v p' 
             → Reduce (Send (JCons (KLet (λ x → p x)) j) v m)
                      (JMSubst p' j m)
    -- J (n₁ + n₂) M → J n M 
    RDelta+ : {j : cont[ var ]}
            → {n₁ n₂ : ℕ}
            → {m : mcont[ var ]}
            → Reduce (Add j (Num n₁) (Num n₂) m)
                     (Send j (Num (n₁ + n₂)) m)
    -- () V (<J, H> :: M) → J V M 
    RHandleRet : {j : cont[ var ]}
               → {v : value[ var ]}
               → {h : handler[ var ]}
               → {m : mcont[ var ]}
               → Reduce (Send JNil v (MCons j h m))
                        (Send j v m)
    -- (<J₀, H> :: M₀) @ V J → P[V/v, R/r, J₀/j₀, M₀/m₀] 
    -- where
    --   H = λv. λr. λj₀. λm₀. P 
    --   R = λy. λj. λm. (J ++ j) y m
    RHandleOp : {v     : value[ var ]}
              → {j₀ j' j'' :  cont[ var ]}
              → {m₀    : mcont[ var ]}
              → {p     : var → var → term[ var ]}
              → {p'    : term[ var ]}
              → JOpen j' j''
              → Subst2 p v (Fun λ y → Send j'' (Var y) MVar) p'
              → Reduce (Op (MCons j₀ (HFun p) m₀) v j')
                       (JMSubst p' j₀ m₀)

    -- congruence rules
    RSendJ : {j j' : cont[ var ]}
           → {v : value[ var ]}
           → {m : mcont[ var ]}
           → ReduceJ j j' 
           → Reduce (Send j v m) (Send j' v m)
    RSendV : {j : cont[ var ]}
           → {v v' : value[ var ]}
           → {m : mcont[ var ]}
           → ReduceV v v' 
           → Reduce (Send j v m) (Send j v' m)
    RSendM : {j : cont[ var ]}
           → {v : value[ var ]}
           → {m m' : mcont[ var ]}
           → ReduceM m m' 
           → Reduce (Send j v m) (Send j v m')
    RAppV  : {v v' w : value[ var ]}
           → {j : cont[ var ]}
           → {m : mcont[ var ]}
           → ReduceV v v'
           → Reduce (App v w j m) (App v' w j m) 
    RAppW  : {v w w' : value[ var ]}
           → {j : cont[ var ]}
           → {m : mcont[ var ]}
           → ReduceV w w'
           → Reduce (App v w j m) (App v w' j m)
    RAppJ  : {v w : value[ var ]}
           → {j j' : cont[ var ]}
           → {m : mcont[ var ]}
           → ReduceJ j j'
           → Reduce (App v w j m) (App v w j' m) 
    RAppM  : {v w : value[ var ]}
           → {j : cont[ var ]}
           → {m m' : mcont[ var ]}
           → ReduceM m m'
           → Reduce (App v w j m) (App v w j m')
    RAddV  : {v v' w : value[ var ]}
           → {j : cont[ var ]}
           → {m : mcont[ var ]}
           → ReduceV v v'
           → Reduce (Add j v w m) (Add j v' w m) 
    RAddW  : {v w w' : value[ var ]}
           → {j : cont[ var ]}
           → {m : mcont[ var ]}
           → ReduceV w w'
           → Reduce (Add j v w m) (Add j v w' m)
    RAddJ  : {v w : value[ var ]}
           → {j j' : cont[ var ]}
           → {m : mcont[ var ]}
           → ReduceJ j j'
           → Reduce (Add j v w m) (Add j' v w m) 
    RAddM  : {v w : value[ var ]}
           → {j : cont[ var ]}
           → {m m' : mcont[ var ]}
           → ReduceM m m'
           → Reduce (Add j v w m) (Add j v w m')
    ROpJ   : {j j' : cont[ var ]}
           → {v : value[ var ]}
           → {m : mcont[ var ]}
           → ReduceJ j j' 
           → Reduce (Op m v j) (Op m v j')
    ROpV   : {j : cont[ var ]}
           → {v v' : value[ var ]}
           → {m : mcont[ var ]}
           → ReduceV v v' 
           → Reduce (Op m v j) (Op m v' j)
    ROpM   : {j : cont[ var ]}
           → {v : value[ var ]}
           → {m m' : mcont[ var ]}
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
    REtaLet : {j : cont[ var ]}
            → ReduceJ (JCons (KLet λ x → Send JVar (Var x) MVar) j) j
    -- K₁ :: K₂ :: J → (K₁ ▷ K₂) :: J
    RAssoc : {k₁ k₂ : frame[ var ]}
           → {j : cont[ var ]}
           → ReduceJ (JCons k₁ (JCons k₂ j))
                     (JCons (KCompose k₁ k₂) j)
    
    -- congruence rules
    RJConsK : {k k' : frame[ var ]}
            → {j : cont[ var ]}
            → ReduceK k k' 
            → ReduceJ (JCons k j) (JCons k' j)
    RJConsJ : {k : frame[ var ]}
            → {j j' : cont[ var ]}
            → ReduceJ j j'
            → ReduceJ (JCons k j) (JCons k j')
  
  data ReduceM where
    -- congruence rules
    RMConsJ : {j j' : cont[ var ]}
            → {h : handler[ var ]}
            → {m : mcont[ var ]}
            → ReduceJ j j' 
            → ReduceM (MCons j h m) (MCons j' h m)
    RMConsH : {j : cont[ var ]}
            → {h h' : handler[ var ]}
            → {m : mcont[ var ]}
            → ReduceH h h' 
            → ReduceM (MCons j h m) (MCons j h' m)
    RMConsM : {j : cont[ var ]}
            → {h : handler[ var ]}
            → {m m' : mcont[ var ]}
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
ReduceJ* : {var : Set} →    cont[ var ] →    cont[ var ] → Set
ReduceM* : {var : Set} →   mcont[ var ] →   mcont[ var ] → Set
ReduceH* : {var : Set} → handler[ var ] → handler[ var ] → Set
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

-- examples
-- λj. λm. ((λv. λj'. λm'. j' (v + 2) m') :: j) 1 m
-- = λj. λm. j 3 m
ex1 : {var : Set} → Reduce* { var }
        (Send (JCons (KLet λ v → Add JVar (Var v) (Num 2) MVar) JVar) (Num 1) MVar)
        (Send JVar (Num 3) MVar)
ex1 = begin
        Send 
          (JCons (KLet (λ v → Add JVar (Var v) (Num 2) MVar)) JVar)
          (Num 1) MVar
      ⟶⟨ RBetaLet (sAdd sJVar sVar= sNum sMVar) ⟩ 
        JMSubst (Add JVar (Num 1) (Num 2) MVar) JVar MVar
      ⟶⟨ RDelta+ ⟩
        Send JVar (Num 3) MVar
      ∎
      where open Reasoning

-- λj. λm.
-- (<j,
--   (λv. λr. λj'. λm'. r v ((λy. λj''. λm''. j'' (y + 3) m'') :: j') m')> 
-- :: m) 
-- @ 1 ((λv. λj. λm. j (v + 2) m) :: ())
-- = λj. λm. j 6 m 
ex2 : {var : Set} → Reduce* { var }
        (Op 
          (MCons 
             JVar 
             (HFun (λ v r → App (Var r) 
                                (Var v) 
                                (JCons (KLet λ y → Add JVar (Var y) (Num 3) MVar) JVar) 
                                MVar)) 
             MVar) 
          (Num 1) 
          (JCons (KLet λ v → Add JVar (Var v) (Num 2) MVar) JNil))
        (Send JVar (Num 6) MVar)
ex2 = begin
        Op
          (MCons JVar
           (HFun
            (λ v r →
               App (Var r) (Var v)
               (JCons (KLet (λ y → Add JVar (Var y) (Num 3) MVar)) JVar) MVar))
           MVar)
          (Num 1) (JCons (KLet (λ v → Add JVar (Var v) (Num 2) MVar)) JNil) 
      ⟶⟨ RHandleOp 
            (oCons oNil) 
            (sSubst2 
              ((λ y → sApp sVar≠ sVar= (sJCons (sKFun (λ x → sAdd sJVar sVar≠ sNum sMVar)) sJVar) sMVar)) 
              (sApp sVar= sNum (sJCons (sKFun (λ x → sAdd sJVar sVar≠ sNum sMVar)) sJVar) sMVar)) ⟩
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
      ⟶⟨ RBetaV (sSend (sJCons (sKFun (λ x → sAdd sJVar sVar≠ sNum sMVar)) sJVar) sVar= sMVar) ⟩ 
        JMSubst
          (Send (JCons (KLet (λ z → Add JVar (Var z) (Num 2) MVar)) JVar) (Num 1) MVar)
          (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) (JSubstJ JVar JVar))
          MVar
      ≡⟨ refl ⟩ 
        Send (JCons (KLet (λ z → Add JVar (Var z) (Num 2) MVar)) 
                (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) 
                  JVar)) 
              (Num 1) MVar
      ⟶⟨ RSendJ RAssoc ⟩ 
        Send
          (JCons
           (KCompose (KLet (λ z → Add JVar (Var z) (Num 2) MVar))
            (KLet (λ z → Add JVar (Var z) (Num 3) MVar)))
           JVar)
          (Num 1) MVar
      ≡⟨ refl ⟩ 
        Send (JCons (KLet λ v → 
            Add (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar) 
                (Var v) 
                (Num 2) 
                MVar) JVar) (Num 1) MVar
      ⟶⟨ RBetaLet
        (sAdd (sJCons (sKFun (λ x → sAdd sJVar sVar≠ sNum sMVar)) sJVar)
         sVar= sNum sMVar) ⟩ 
        Add (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar) (Num 1) (Num 2) MVar
      ⟶⟨ RDelta+ ⟩ 
        Send 
          (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar)
          (Num (1 + 2)) MVar
      ≡⟨ refl ⟩ 
        Send (JCons (KLet (λ z → Add JVar (Var z) (Num 3) MVar)) JVar)
          (Num 3) MVar
      ⟶⟨ RBetaLet (sAdd sJVar sVar= sNum sMVar) ⟩ 
        Add JVar (Num 3) (Num 3) MVar
      ⟶⟨ RDelta+ ⟩ 
        Send JVar (Num 6) MVar
      ∎
      where open Reasoning
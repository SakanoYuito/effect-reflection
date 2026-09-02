module DS where
open import Data.Nat using (ℕ; zero; suc; _+_)

-- Terms
interleaved mutual
  data value[_] (var : Set) : Set
  data comp[_]  (var : Set) : Set

  data value[_] where
    -- x
    Var : (x : var) → value[ var ]
    -- n
    Num : (n : ℕ) → value[ var ]
    -- λx. P
    Fun : (f : var → comp[ var ]) → value[ var ]

  data comp[_] where
    -- return V
    Return : (v : value[ var ]) → comp[ var ] 
    -- V W 
    App : (v : value[ var ]) → (w : value[ var ]) → comp[ var ]
    -- V + W 
    Add : (v : value[ var ]) → (w : value[ var ]) → comp[ var ]
    -- let x = P in Q
    Let : (p : comp[ var ]) 
        → (q : var → comp[ var ])
        → comp[ var ]
    -- handle P with x, k → Q
    Handle : (p : comp[ var ])
           → (q : var → var → comp[ var ])
           → comp[ var ]
    -- op V 
    Op : (v : value[ var ]) → comp[ var ] 


-- examples
-- λx. return x
val1 : {var : Set} → value[ var ]
val1 = Fun (λ x → Return (Var x))

-- let x = return 1 in x + 2
comp1 : {var : Set} → comp[ var ]
comp1 = Let (Return (Num 1)) (λ x → Add (Var x) (Num 2))

-- handle let x = op 1 in x + 2 
-- with x, k → let y = k x in y + 3
comp2 : {var : Set} → comp[ var ]
comp2 = Handle (Let (Op (Num 1)) (λ x → Add (Var x) (Num 2))) 
          (λ x k → Let (App (Var k) (Var x)) λ y → Add (Var y) (Num 3))


-- Evaluation context
data PCtx[_] (var : Set) : Set where
  -- [] 
  FHole : PCtx[ var ] 
  -- F[ let x = [] in P ] 
  FLet : (f : PCtx[ var ])
       → (p : var → comp[ var ])
       → PCtx[ var ]

data MCtx[_] (var : Set) : Set where
  -- []
  MHole : MCtx[ var ]
  -- G[ F[ handle [] with x, k → P ] ]
  MHandle : (g : MCtx[ var ])
          → (f : PCtx[ var ])
          → (h : var → var → comp[ var ])
          → MCtx[ var ]

-- Plug
plug : {var : Set} → (f : PCtx[ var ]) → (p : comp[ var ]) → comp[ var ]
plug FHole p = p
plug (FLet f q) p = plug f (Let p q)

plugM : {var : Set} → (m : MCtx[ var ]) → (p : comp[ var ]) → comp[ var ] 
plugM MHole p = p
plugM (MHandle g f h) p = plugM g (plug f (Handle p h))

-- Substitution relation P[V/x]
interleaved mutual
  data SubstV {var : Set} : (var → value[ var ]) → value[ var ] → value[ var ] → Set
  data Subst  {var : Set} : (var →  comp[ var ]) → value[ var ] →  comp[ var ] → Set

  data SubstV where
    -- (x)[v/x] → v
    sVar= : {v : value[ var ]}
          → SubstV (λ x → Var x) v v 
    -- (x)[v/y] → y 
    sVar≠ : {v : value[ var ]} {x : var}
          → SubstV (λ _ → Var x) v (Var x) 
    -- (n)[v/x] → n 
    sNum  : {v : value[ var ]} {n : ℕ}
          → SubstV (λ _ → Num n) v (Num n)
    -- (λx. P)[v/y] → λx. (P[v/y])
    sFun  : {v  : value[ var ]}
          → {p  : var → var → comp[ var ]}
          → {p' : var → comp[ var ]}
          → ((x : var) → Subst (λ y → (p y) x) v (p' x))
          → SubstV (λ y → Fun (p y)) v (Fun p')
    
  data Subst where
    -- (return v)[w/x] → return (v[w/x])
    sReturn : {v  : var → value[ var ]}
            → {w  : value[ var ]}
            → {v' : value[ var ]}
            → SubstV v w v'
            → Subst (λ x → Return (v x)) w (Return v')
    -- (v₁ v₂)[w/x] → (v₁[w/x]) (v₂[w/x])
    sApp : {v₁  : var → value[ var ]}
         → {v₂  : var → value[ var ]}
         → {v₁' : value[ var ]}
         → {v₂' : value[ var ]}
         → {w : value[ var ]}
         → SubstV v₁ w v₁'
         → SubstV v₂ w v₂'
         → Subst (λ x → App (v₁ x) (v₂ x)) w (App v₁' v₂')
    -- (v₁ + v₂)[w/x] → (v₁[w/x]) + (v₂[w/x])
    sAdd : {v₁  : var → value[ var ]}
         → {v₂  : var → value[ var ]}
         → {v₁' : value[ var ]}
         → {v₂' : value[ var ]}
         → {w : value[ var ]}
         → SubstV v₁ w v₁'
         → SubstV v₂ w v₂'
         → Subst (λ x → Add (v₁ x) (v₂ x)) w (Add v₁' v₂')
    -- (let x = P in Q)[v/y] → let x = P[v/y] in Q[v/y]
    sLet : {v  : value[ var ]}
         → {p  : var → comp[ var ]}
         → {q  : var → var → comp[ var ]}
         → {p' : comp[ var ]}
         → {q' : var → comp[ var ]}
         → Subst p v p'
         → ((x : var) → Subst (λ y → (q y) x) v (q' x))
         → Subst (λ y → Let (p y) (q y)) v (Let p' q')
    -- (handle P with x, k → Q)[v/y] → handle P[v/y] with x, k → Q[v/y]
    sHandle : {v  : value[ var ]}
            → {p  : var → comp[ var ]}
            → {q  : var → var → var → comp[ var ]}
            → {p' : comp[ var ]}
            → {q' : var → var → comp[ var ]}
            → Subst p v p'
            → ((x : var) (k : var) → Subst (λ y → (q y) x k) v (q' x k))
            → Subst (λ y → Handle (p y) (q y)) v (Handle p' q')
    -- (op v)[w/x] → op (v[w/x])
    sOp : {v    : var → value[ var ]}
        → {v' w : value[ var ]}
        → SubstV v w v'
        → Subst (λ x → Op (v x)) w (Op v')

data Subst2 {var : Set} :
  (var → var → comp[ var ]) → value[ var ] → value[ var ] → 
  comp[ var ] → Set where

  sSubst2 : {p   : var → var → comp[ var ]}
          → {v w : value[ var ]}
          → {p'  : var → comp[ var ]}
          → {p'' : comp[ var ]}
          → ((y : var) → Subst (λ x → p x y) v (p' y))
          → Subst p' w p''
          → Subst2 p v w p'' 
  


interleaved mutual
  data ReduceV {var : Set} : value[ var ] → value[ var ] → Set
  data Reduce  {var : Set} :  comp[ var ] →  comp[ var ] → Set 
  
  data ReduceV where
    -- λx. V x  → V
    REtaV : {v : value[ var ]}
          → ReduceV (Fun (λ x → App v (Var x))) v
    
    -- congruence rule 
    RFun  : {p p' : var → comp[ var ]}
          → ((x : var) → Reduce (p x) (p' x))
          → ReduceV (Fun p) (Fun p')

  data Reduce where
    -- (λx. P) V → P[V/x]
    RBetaV : {p   : var → comp[ var ]}
           → {v   : value[ var ]}
           → {p'  : comp[ var ]}
           → (sub : Subst p v p')
           → Reduce (App (Fun p) v) p'
    -- let x = return V in P → P[V/x]
    RBetaLet : {p   : var → comp[ var ]}
             → {v   : value[ var ]}
             → {p'  : comp[ var ]}
             → (sub : Subst p v p')
             → Reduce (Let (Return v) p) p'
    -- let x = P in return x → P 
    REtaLet : {p : comp[ var ]}
            → Reduce (Let p (λ x → Return (Var x))) p
    -- let y = (let x = P in Q) in R → let x = P in let y = Q in R
    RAssoc : {p   : comp[ var ]}
           → {q r : var → comp[ var ]}
           → Reduce (Let (Let p q) r) 
                    (Let p (λ x → Let (q x) r))
    -- n₁ + n₂ → return n 
    RDelta+ : {n₁ n₂ : ℕ}
            → Reduce (Add (Num n₁) (Num n₂)) (Return (Num (n₁ + n₂)))
    -- (handle return V with x, k → P) → return V 
    RHandleRet : {v : value[ var ]}
               → {p : var → var → comp[ var ]}
               → Reduce (Handle (Return v) p) (Return v)
    -- (handle F[op V] with x, k → P) → P[V/x, (λy. F[return y])/k]
    RHandleOp  : {p   : var → var → comp[ var ]}
               → {f   : PCtx[ var ]}
               → {v   : value[ var ]}
               → {p'  : comp[ var ]}
               → (sub : Subst2 p v (Fun (λ y → plug f (Return (Var y)))) p')
               → Reduce (Handle (plug f (Op v)) p) p'
    
    -- congruence rules
    RReturn  : {v v' : value[ var ]}
             → ReduceV v v'
             → Reduce (Return v) (Return v')
    RApp₁    : {v v' w : value[ var ]}
             → ReduceV v v'
             → Reduce (App v w) (App v' w)
    RApp₂    : {v w w' : value[ var ]}
             → ReduceV w w'
             → Reduce (App v w) (App v w')
    RAdd₁    : {v v' w : value[ var ]}
             → ReduceV v v'
             → Reduce (Add v w) (Add v' w)
    RAdd₂    : {v w w' : value[ var ]}
             → ReduceV w w'
             → Reduce (Add v w) (Add v w')
    RLet₁    : {p p' : comp[ var ]}
             → {q : var → comp[ var ]}
             → Reduce p p'
             → Reduce (Let p q) (Let p' q)
    RLet₂    : {p : comp[ var ]}
             → {q q' : var → comp[ var ]}
             → ((x : var) → Reduce (q x) (q' x))
             → Reduce (Let p q) (Let p q')
    RHandle₁ : {p p' : comp[ var ]}
             → {q : var → var → comp[ var ]}
             → Reduce p p'
             → Reduce (Handle p q) (Handle p' q)
    RHandle₂ : {p : comp[ var ]}
             → {q q' : var → var → comp[ var ]}
             → ((x k : var) → Reduce (q x k) (q' x k))
             → Reduce (Handle p q) (Handle p q')
    ROp      : {v v' : value[ var ]}
             → ReduceV v v'
             → Reduce (Op v) (Op v')

data Star {A : Set} (_~_ : A → A → Set) : A → A → Set where
  Refl : {x : A} 
        → Star _~_ x x
  Step : {x y z : A}
        → x ~ y 
        → Star _~_ y z 
        → Star _~_ x z

Reduce* : {var : Set} → comp[ var ] → comp[ var ] → Set
Reduce* = Star Reduce

ReduceV* : {var : Set} → value[ var ] → value[ var ] → Set
ReduceV* = Star ReduceV

-- equational reasoning
module Reasoning {var : Set} where

  infix  1 begin_
  infixr 2 _⟶⟨_⟩_
  infix  3 _∎

  begin_ : {p q : comp[ var ]} → Reduce* p q → Reduce* p q
  begin_ reds = reds

  _⟶⟨_⟩_ : (p {q r} : comp[ var ]) → Reduce p q → Reduce* q r → Reduce* p r
  p ⟶⟨ red ⟩ reds = Step red reds

  _∎ : (p : comp[ var ]) → Reduce* p p
  p ∎ = Refl


-- examples

-- let x = return 1 in x + 2 = return 3
ex1 : {var : Set} → Reduce* { var } 
        (Let (Return (Num 1)) (λ x → Add (Var x) (Num 2)))
        (Return (Num 3))
ex1 = begin 
        Let (Return (Num 1)) (λ x → Add (Var x) (Num 2))
      ⟶⟨ RBetaLet (sAdd sVar= sNum) ⟩
        Add (Num 1) (Num 2)
      ⟶⟨ RDelta+ ⟩
        Return (Num 3)
      ∎
      where open Reasoning

-- handle (let x = op 1 in x + 2) with x, k → (let y = k x in y + 3)
-- = Return 6
ex2 : {var : Set} → Reduce* { var }
        (Handle (Let (Op (Num 1)) (λ x → Add (Var x) (Num 2))) 
                (λ x k → Let (App (Var k) (Var x)) (λ y → Add (Var y) (Num 3))))
        (Return (Num 6))
ex2 { var } = begin
        (Handle (Let (Op (Num 1)) (λ x → Add (Var x) (Num 2))) 
                (λ x k → Let (App (Var k) (Var x)) (λ y → Add (Var y) (Num 3))))
        ⟶⟨ RHandleOp 
             {f = captured}
             (sSubst2 (λ k → sLet (sApp sVar≠ sVar=) 
                      (λ x → sAdd sVar≠ sNum)) 
             (sLet (sApp sVar= sNum) 
                   (λ x → sAdd sVar≠ sNum))) ⟩
        -- let y = (λy. let x = return y in x + 2) 1 in y + 3
          Let (App resumption (Num 1)) 
              (λ y → Add (Var y) (Num 3))
        ⟶⟨ RLet₁ (RBetaV (sLet (sReturn sVar=) 
                               (λ x → sAdd sVar≠ sNum))) ⟩
        -- let y = (let x = return 1 in x + 2) in y + 3
          Let (Let (Return (Num 1)) (λ x → Add (Var x) (Num 2)))
              (λ y → Add (Var y) (Num 3))
        ⟶⟨ RAssoc ⟩
        -- let x = return 1 in let y = x + 2 in y + 3 
          Let (Return (Num 1)) 
              (λ x → Let (Add (Var x) (Num 2))
                         (λ y → Add (Var y) (Num 3)))
        ⟶⟨ RBetaLet (sLet (sAdd sVar= sNum) 
                          (λ x → sAdd sVar≠ sNum)) ⟩ 
        -- let y = 1 + 2 in y + 3
          Let (Add (Num 1) (Num 2)) 
              (λ y → Add (Var y) (Num 3)) 
        ⟶⟨ RLet₁ RDelta+ ⟩
        -- let y = 3 in y + 3
          Let (Return (Num 3)) 
              (λ y → Add (Var y) (Num 3))
        ⟶⟨ RBetaLet (sAdd sVar= sNum) ⟩
        -- 3 + 3
          Add (Num 3) (Num 3)
        ⟶⟨ RDelta+ ⟩
          Return (Num 6)
        ∎
        where 
        open Reasoning

        -- captuerd context F : let x = [] in x + 2
        captured : PCtx[ var ] 
        captured = FLet FHole (λ x → Add (Var x) (Num 2))
        -- resumption k = λy. (F[return y])
        resumption : value[ var ] 
        resumption = Fun (λ y → plug captured (Return (Var y)))
module _Reflect2 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

import DS 
import CPS 
open import DS-CPS
open import CPS-DS
open import Extensionality

data JEnd : Set where
  jOpen   : JEnd 
  jClosed : JEnd

data JEndsAt {var : Set} : JEnd → CPS.cont[ var ] → Set where
  at-var  : JEndsAt jOpen CPS.JVar
  at-nil  : JEndsAt jClosed CPS.JNil
  at-cons : {e : JEnd}
          → {k : CPS.frame[ var ]}
          → {j : CPS.cont[ var ]}
          → JEndsAt e j 
          → JEndsAt e (CPS.JCons k j)

baseJ : {var : Set} → JEnd → CPS.cont[ var ]
baseJ jOpen   = CPS.JVar
baseJ jClosed = CPS.JNil

data Location : Set where
  current : Location
  stored  : Location

end : Location → JEnd
end current = jOpen
end stored  = jClosed

data MLocated {var : Set} : Location → CPS.mcont[ var ] → Set where
  m-current : MLocated current CPS.MVar
  m-store   : {j : CPS.cont[ var ]}
            → JEndsAt jOpen j
            → {h : CPS.handler[ var ]}
            → MLocated stored (CPS.MCons j h CPS.MVar)
  m-cons    : {j : CPS.cont[ var ]}
            → JEndsAt jClosed j 
            → {m : CPS.mcont[ var ]}
            → MLocated stored m
            → {h : CPS.handler[ var ]} 
            → MLocated stored (CPS.MCons j h m)

data Located {var : Set} : Location → CPS.cont[ var ] → CPS.mcont[ var ] → Set where 
  loc-current : {j : CPS.cont[ var ]}
              → (tj : JEndsAt jOpen j) 
              → {m : CPS.mcont[ var ]}
              → (tm : MLocated current m) 
              → Located current j m  
  loc-stored  : {j : CPS.cont[ var ]}
              → (tj : JEndsAt jClosed j) 
              → {m : CPS.mcont[ var ]}
              → (tm : MLocated stored m) 
              → Located stored j m 

termJ : {var : Set} → CPS.term[ var ] → CPS.cont[ var ]
termJ (CPS.Send j v m)  = j
termJ (CPS.Add j v w m) = j
termJ (CPS.App v w j m) = j
termJ (CPS.Op m v j)    = j

termM : {var : Set} → CPS.term[ var ] → CPS.mcont[ var ]
termM (CPS.Send j v m)  = m
termM (CPS.Add j v w m) = m
termM (CPS.App v w j m) = m
termM (CPS.Op m v j)    = m

interleaved mutual
  data GoodP {var : Set} : Location → CPS.term[ var ] → Set
  data GoodK {var : Set} : CPS.frame[ var ] → Set 
  data GoodJ {var : Set} : JEnd → CPS.cont[ var ] → Set
  data GoodV {var : Set} : CPS.value[ var ] → Set
  data GoodM {var : Set} : Location → CPS.mcont[ var ] → Set
  data GoodH {var : Set} : CPS.handler[ var ] → Set

  data GoodP where
    good-send : {l : Location}
              → {j : CPS.cont[ var ]}
              → {v : CPS.value[ var ]}
              → {m : CPS.mcont[ var ]}
              → (gj : GoodJ (end l) j)
              → (gv : GoodV v) 
              → (gm : GoodM l m)
              → GoodP l (CPS.Send j v m)
    good-add  : {l : Location}
              → {j : CPS.cont[ var ]}
              → {v w : CPS.value[ var ]}
              → {m : CPS.mcont[ var ]}
              → (gj : GoodJ (end l) j)
              → (gv : GoodV v)
              → (gw : GoodV w)
              → (gm : GoodM l m)
              → GoodP l (CPS.Add j v w m)
    good-app  : {l : Location}
              → {j : CPS.cont[ var ]}
              → {v w : CPS.value[ var ]}
              → {m : CPS.mcont[ var ]}
              → (gv : GoodV v)
              → (gw : GoodV w )
              → (gj : GoodJ (end l) j) 
              → (gm : GoodM l m)
              → GoodP l (CPS.App v w j m)
    good-op   : {l : Location}
              → {j : CPS.cont[ var ]}
              → {v : CPS.value[ var ]}
              → {m : CPS.mcont[ var ]} 
              → (gm : GoodM l m)
              → (gv : GoodV v)
              → (gj : GoodJ (end l) j)
              → GoodP l (CPS.Op m v j)

  data GoodV where
    good-var : {x : var} → GoodV (CPS.Var x)
    good-num : {n : ℕ} → GoodV (CPS.Num n)
    good-fun : {f : var → CPS.term[ var ]} 
             → {l : Location}
             → (gb : ((x : var) 
                       → Σ Location (λ l → GoodP l (f x))))
             → GoodV (CPS.Fun f)
  
  data GoodK where
    good-klet : {f : var → CPS.term[ var ]}
              → {l : Location}
              → (gb : ((x : var) 
                        → Σ Location (λ l → GoodP l (f x))))
              → GoodK (CPS.KLet f)
  
  data GoodJ where
    good-jvar  : GoodJ jOpen CPS.JVar
    good-jnil  : GoodJ jClosed CPS.JNil
    good-jcons : {k : CPS.frame[ var ]}
               → {e : JEnd}
               → {j : CPS.cont[ var ]}
               → (gk : GoodK k)
               → (gj : GoodJ e j) 
               → GoodJ e (CPS.JCons k j)
  
  data GoodM where
    good-mvar : GoodM current CPS.MVar
    good-mcons-o : {j : CPS.cont[ var ]}
                 → {h : CPS.handler[ var ]}
                 → (gj : GoodJ jOpen j)
                 → (gh : GoodH h)
                 → GoodM stored (CPS.MCons j h CPS.MVar) 
    good-mcons-c : {j : CPS.cont[ var ]}
                 → {h : CPS.handler[ var ]}
                 → {m : CPS.mcont[ var ]}
                 → (gj : GoodJ jClosed j) 
                 → (gh : GoodH h) 
                 → (gm : GoodM stored m)
                 → GoodM stored (CPS.MCons j h m)
  
  data GoodH where
    good-hfun : {h : var → var → CPS.term[ var ]}
              → {l : Location}
              → (gb : ((v r : var) 
                        → Σ Location (λ l → GoodP l (h v r))))
              → GoodH (CPS.HFun h)


interleaved mutual
  correctP  : {var : Set}
            → {l : Location}
            → {p : CPS.term[ var ]}
            → (g : GoodP l p)
            → cpsP (dsP p) CPS.JVar CPS.MVar ≡ p
  correctV  : {var : Set}
            → {v : CPS.value[ var ]}
            → (gv : GoodV v)
            → cpsV (dsV v) ≡ v
  correctJ  : {var : Set}
            → {e : JEnd}
            → {j : CPS.cont[ var ]}
            → (gj : GoodJ e j)
            → (p : DS.comp[ var ])
            → (m : CPS.mcont[ var ])
            → cpsP (DS.plug (dsJ j) p) (baseJ e) m
            ≡ cpsP p j m
  correctJM : {var : Set}
            → {l : Location}
            → {m : CPS.mcont[ var ]}
            → {j : CPS.cont[ var ]}
            → (gm : GoodM l m)
            → (gj : GoodJ (end l) j)
            → (p : DS.comp[ var ])
            → cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) p)) CPS.JVar CPS.MVar
            ≡ cpsP p j m 
  correctH  : {var : Set}
            → {h : CPS.handler[ var ]}
            → (gh : GoodH h)
            → CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)
            ≡ h
  
  correctP (good-send {j = j} {v} {m} gj gv gm) = 
    begin
      cpsP (dsP (CPS.Send j v m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM gm gj (DS.Return (dsV v)) ⟩
      cpsP (DS.Return (dsV v)) j m
    ≡⟨ refl ⟩
      CPS.Send j (cpsV (dsV v)) m
    ≡⟨ cong (λ v' → CPS.Send j v' m) (correctV gv) ⟩
      CPS.Send j v m
    ∎
  correctP (good-add {j = j} {v} {w} {m} gj gv gw gm) =
    begin
      cpsP (dsP (CPS.Add j v w m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM gm gj (DS.Add (dsV v) (dsV w)) ⟩
      cpsP (DS.Add (dsV v) (dsV w)) j m
    ≡⟨ refl ⟩
      CPS.Add j (cpsV (dsV v)) (cpsV (dsV w)) m
    ≡⟨ cong₂ (λ v' w' → CPS.Add j v' w' m) (correctV gv) (correctV gw) ⟩
      CPS.Add j v w m
    ∎
  correctP (good-app {j = j} {v = v} {w} {m} gv gw gj gm) = 
    begin
      cpsP (dsP (CPS.App v w j m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM gm gj (DS.App (dsV v) (dsV w)) ⟩
      cpsP (DS.App (dsV v) (dsV w)) j m
    ≡⟨ refl ⟩
      CPS.App (cpsV (dsV v)) (cpsV (dsV w)) j m
    ≡⟨ cong₂ (λ v' w' → CPS.App v' w' j m) (correctV gv) (correctV gw) ⟩
      CPS.App v w j m
    ∎
  correctP (good-op {j = j} {v = v} {m = m} gm gv gj) = 
    begin
      cpsP (dsP (CPS.Op m v j)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))) CPS.JVar CPS.MVar
    ≡⟨ correctJM gm gj (DS.Op (dsV v)) ⟩
      cpsP (DS.Op (dsV v)) j m
    ≡⟨ refl ⟩
      CPS.Op m (cpsV (dsV v)) j
    ≡⟨ cong (λ v' → CPS.Op m v' j) (correctV gv) ⟩
      CPS.Op m v j
    ∎
  
  correctV good-var = refl
  correctV good-num = refl
  correctV (good-fun {f} gb) = 
    begin
      cpsV (dsV (CPS.Fun f))
    ≡⟨ refl ⟩
      CPS.Fun f'
    ≡⟨ cong CPS.Fun f'≡f ⟩
      CPS.Fun f
    ∎
    where
      f' = λ x → cpsP (dsP (f x)) CPS.JVar CPS.MVar
      f'≡f = extensionality λ x → correctP (gb x .Data.Product.proj₂)
  

  correctJ good-jvar p m = refl
  correctJ good-jnil p m = refl
  correctJ {e = e} (good-jcons {j = j} (good-klet {f} gb) gj) p m = 
    begin
      cpsP (DS.plug (dsJ (CPS.JCons (CPS.KLet f) j)) p) (baseJ e) m
    ≡⟨ refl ⟩
      cpsP (DS.plug (dsJ j) (DS.Let p (λ x → dsP (f x)))) (baseJ e) m
    ≡⟨ correctJ gj (DS.Let p (λ x → dsP (f x))) m ⟩
      cpsP (DS.Let p (λ x → dsP (f x))) j m
    ≡⟨ refl ⟩
      cpsP p (CPS.JCons (CPS.KLet f') j) m
    ≡⟨ cong (λ f' → cpsP p (CPS.JCons (CPS.KLet f') j) m) f'≡f ⟩
      cpsP p (CPS.JCons (CPS.KLet f) j) m
    ∎
    where
      f' = λ x → cpsP (dsP (f x)) CPS.JVar CPS.MVar
      f'≡f = extensionality λ x → correctP (gb x .Data.Product.proj₂)
  
  correctJM good-mvar good-jvar g = refl
  correctJM good-mvar (good-jcons {j = j} (good-klet {f} gb) gj) g = 
    begin
      cpsP
        (DS.plugM (dsM CPS.MVar)
         (DS.plug (dsJ (CPS.JCons (CPS.KLet f) j)) g))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plug (dsJ j) (DS.Let g (λ x → dsP (f x)))) CPS.JVar CPS.MVar
    ≡⟨ correctJ gj (DS.Let g (λ x → dsP (f x))) CPS.MVar ⟩
      cpsP (DS.Let g (λ x → dsP (f x))) j CPS.MVar
    ≡⟨ refl ⟩
      cpsP g (CPS.JCons (CPS.KLet f') j) CPS.MVar
    ≡⟨ cong (λ f' → cpsP g (CPS.JCons (CPS.KLet f') j) CPS.MVar) f'≡f ⟩
      cpsP g (CPS.JCons (CPS.KLet f) j) CPS.MVar
    ∎
    where 
      f' = λ v → cpsP (dsP (f v)) CPS.JVar CPS.MVar
      f'≡f = extensionality λ x → correctP (gb x .Data.Product.proj₂)

  correctJM {j = j₁} (good-mcons-o {j} {CPS.HFun h} gj₁ gh) gj g = 
    begin
      cpsP
        (DS.plugM (dsM (CPS.MCons j (CPS.HFun h) CPS.MVar))
         (DS.plug (dsJ j₁) g))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP
        (DS.plug (dsJ j)
         (DS.Handle (DS.plug (dsJ j₁) g) (λ v r → dsP (h v r))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJ gj₁ (DS.Handle (DS.plug (dsJ j₁) g) (λ v r → dsP (h v r))) CPS.MVar ⟩
      cpsP (DS.Handle (DS.plug (dsJ j₁) g) (λ v r → dsP (h v r))) j
        CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plug (dsJ j₁) g) CPS.JNil
        (CPS.MCons j (CPS.HFun h') CPS.MVar)
    ≡⟨ correctJ gj g (CPS.MCons j (CPS.HFun h') CPS.MVar) ⟩
      cpsP g j₁ (CPS.MCons j (CPS.HFun h') CPS.MVar)
    ≡⟨ cong (λ h' → cpsP g j₁ (CPS.MCons j h' CPS.MVar)) (correctH gh) ⟩
      cpsP g j₁ (CPS.MCons j (CPS.HFun h) CPS.MVar)
    ∎
    where 
      h' = λ v r → cpsP (dsP (h v r)) CPS.JVar CPS.MVar
      
  correctJM {j = j₁} (good-mcons-c {j} {h} {m} gj₁ gh gm) gj g =
    begin
      cpsP (DS.plugM (dsM (CPS.MCons j h m)) (DS.plug (dsJ j₁) g))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP
        (DS.plugM (dsM m)
         (DS.plug (dsJ j) (DS.Handle (DS.plug (dsJ j₁) g) (dsH h))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM gm gj₁ (DS.Handle (DS.plug (dsJ j₁) g) (dsH h)) ⟩
      cpsP (DS.Handle (DS.plug (dsJ j₁) g) (dsH h)) j m
    ≡⟨ refl ⟩
      cpsP (DS.plug (dsJ j₁) g) CPS.JNil
        (CPS.MCons j h' m)
    ≡⟨ correctJ gj g (CPS.MCons j h' m) ⟩
      cpsP g j₁ (CPS.MCons j h' m)
    ≡⟨ cong (λ h' → cpsP g j₁ (CPS.MCons j h' m)) (correctH gh) ⟩
      cpsP g j₁ (CPS.MCons j h m)
    ∎
    where h' = CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)

  correctH (good-hfun {h} gb) =
    begin
      CPS.HFun (λ v r → cpsP (dsH (CPS.HFun h) v r) CPS.JVar CPS.MVar)
    ≡⟨ refl ⟩
      CPS.HFun h'
    ≡⟨ cong CPS.HFun h'≡h ⟩
      CPS.HFun h
    ∎
    where 
      h' = λ v r → cpsP (dsP (h v r)) CPS.JVar CPS.MVar
      h'≡h = extensionality λ x → 
                extensionality λ y → correctP (gb x y .Data.Product.proj₂)

right-inverse : {var : Set}
              → {l : Location}
              → {p : CPS.term[ var ]}
              → GoodP l p
              → cpsP (dsP p) CPS.JVar CPS.MVar ≡ p
right-inverse = correctP

push-good : {var : Set}
          → {l : Location}
          → {j : CPS.cont[ var ]}
          → {h : CPS.handler[ var ]}
          → {m : CPS.mcont[ var ]}
          → GoodJ (end l) j
          → GoodH h
          → GoodM l m
          → GoodM stored (CPS.MCons j h m)

push-good gj gh good-mvar =
  good-mcons-o gj gh

push-good gj gh gm@(good-mcons-o _ _) =
  good-mcons-c gj gh gm

push-good gj gh gm@(good-mcons-c _ _ _) =
  good-mcons-c gj gh gm

interleaved mutual
  cps-good  : {var : Set} 
            → {l : Location}
            → {j : CPS.cont[ var ]}
            → {m : CPS.mcont[ var ]}
            → (p : DS.comp[ var ]) 
            → (gj : GoodJ (end l) j)
            → (gm : GoodM l m)
            → Σ Location (λ l' → GoodP l' (cpsP p j m))
  cpsV-good : {var : Set} → (v : DS.value[ var ]) → GoodV (cpsV v)

  cps-good {l = l} (DS.Return v) gj gm   = l , good-send gj (cpsV-good v) gm
  cps-good {l = l} (DS.App v w) gj gm    = l , good-app (cpsV-good v) (cpsV-good w) gj gm
  cps-good {l = l} (DS.Add v w) gj gm    = l , good-add gj (cpsV-good v) (cpsV-good w) gm
  cps-good {l = l} (DS.Let p q) gj gm    = cps-good p 
                                            (good-jcons 
                                              (good-klet λ x → cps-good (q x) good-jvar good-mvar) gj) gm
  cps-good {l = l} (DS.Handle p q) gj gm = cps-good p good-jnil (push-good gj gh gm)
                                              where 
                                                gh = good-hfun λ v r → cps-good (q v r) good-jvar good-mvar
  cps-good {l = l} (DS.Op v) gj gm       = l , good-op gm (cpsV-good v) gj


  cpsV-good (DS.Var x) = good-var
  cpsV-good (DS.Num n) = good-num
  cpsV-good (DS.Fun f) = good-fun λ x → cps-good (f x) good-jvar good-mvar

well-formed : {var : Set}
            → (p : DS.comp[ var ])
            → Σ Location (λ l → GoodP l (cpsP p CPS.JVar CPS.MVar))
well-formed p = cps-good p good-jvar good-mvar


-- interleaved mutual
--   correctV  : {var : Set}
--             → (v : CPS.value[ var ])
--             → cpsV (dsV v) ≡ v
--   correctP  : {var : Set}
--             → {l : Location}
--             → (p : CPS.term[ var ])
--             → (t : Located l (termJ p) (termM p))
--             → cpsP (dsP p) CPS.JVar CPS.MVar ≡ p
--   correctJ  : {var : Set}
--             → {l : Location}
--             → {j : CPS.cont[ var ]}
--             → {m : CPS.mcont[ var ]}
--             → (t : Located l j m)
--             → (p : DS.comp[ var ])
--             → cpsP (DS.plug (dsJ j) p) CPS.JVar CPS.MVar
--             ≡ cpsP p j m
--   correctJM : {var : Set}
--             → {l : Location}
--             → {j : CPS.cont[ var ]}
--             → {m : CPS.mcont[ var ]}
--             → (t : Located l j m)
--             → (p : DS.comp[ var ])
--             → cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) p)) CPS.JVar CPS.MVar 
--             ≡ cpsP p j m
  
--   correctV (CPS.Var x) = refl
--   correctV (CPS.Num n) = refl
--   correctV (CPS.Fun p) = 
--     begin
--       cpsV (dsV (CPS.Fun p))
--     ≡⟨ refl ⟩
--       CPS.Fun p'
--     ≡⟨ cong CPS.Fun p'≡p ⟩
--       CPS.Fun p
--     ∎
--     where
--       p' = λ x → cpsP (dsP (p x)) CPS.JVar CPS.MVar
--       p'≡p = extensionality λ x → {!   !}

--   correctP (CPS.Send j v m) t =
--     begin
--       cpsP (dsP (CPS.Send j v m)) CPS.JVar CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v))))
--         CPS.JVar CPS.MVar
--     ≡⟨ correctJM t (DS.Return (dsV v)) ⟩
--       cpsP (DS.Return (dsV v)) j m
--     ≡⟨ refl ⟩
--       CPS.Send j (cpsV (dsV v)) m
--     ≡⟨ cong (λ v' → CPS.Send j v' m) (correctV v) ⟩
--       CPS.Send j v m
--     ∎
--   correctP (CPS.Add j v w m) t = 
--     begin
--       cpsP (dsP (CPS.Add j v w m)) CPS.JVar CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w))))
--         CPS.JVar CPS.MVar
--     ≡⟨ correctJM t (DS.Add (dsV v) (dsV w)) ⟩
--       cpsP (DS.Add (dsV v) (dsV w)) j m
--     ≡⟨ refl ⟩
--       CPS.Add j (cpsV (dsV v)) (cpsV (dsV w)) m
--     ≡⟨ cong₂ (λ v' w' → CPS.Add j v' w' m) (correctV v) (correctV w) ⟩
--       CPS.Add j v w m
--     ∎
--   correctP (CPS.App v w j m) t = 
--     begin
--       cpsP (dsP (CPS.App v w j m)) CPS.JVar CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w))))
--         CPS.JVar CPS.MVar
--     ≡⟨ correctJM t (DS.App (dsV v) (dsV w)) ⟩
--       cpsP (DS.App (dsV v) (dsV w)) j m
--     ≡⟨ refl ⟩
--       CPS.App (cpsV (dsV v)) (cpsV (dsV w)) j m
--     ≡⟨ cong₂ (λ v' w' → CPS.App v' w' j m) (correctV v) (correctV w) ⟩
--       CPS.App v w j m
--     ∎
--   correctP (CPS.Op m v j) t = 
--     begin
--       cpsP (dsP (CPS.Op m v j)) CPS.JVar CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))) 
--         CPS.JVar CPS.MVar
--     ≡⟨ correctJM t (DS.Op (dsV v)) ⟩
--       cpsP (DS.Op (dsV v)) j m
--     ≡⟨ refl ⟩
--       CPS.Op m (cpsV (dsV v)) j
--     ≡⟨ cong (λ z → CPS.Op m z j) (correctV v) ⟩
--       CPS.Op m v j
--     ∎

--   correctJM {j = j} {m = m} (loc-current tj m-current) p =
--     begin
--       cpsP (DS.plugM (dsM CPS.MVar) (DS.plug (dsJ j) p)) CPS.JVar
--         CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plug (dsJ j) p) CPS.JVar CPS.MVar
--     ≡⟨ correctJ (loc-current tj m-current) p ⟩
--       cpsP p j CPS.MVar
--     ∎
--   correctJM {j = j} {m = m} (loc-stored tj (m-store {j'} x {h})) p = 
--     begin
--       cpsP (DS.plugM (dsM (CPS.MCons j' h CPS.MVar)) (DS.plug (dsJ j) p))
--         CPS.JVar CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plug (dsJ j') (DS.Handle (DS.plug (dsJ j) p) (dsH h)))
--         CPS.JVar CPS.MVar
--     ≡⟨ correctJ (loc-current x m-current) (DS.Handle (DS.plug (dsJ j) p) (dsH h)) ⟩
--       cpsP (DS.Handle (DS.plug (dsJ j) p) (dsH h)) j' CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP (DS.plug (dsJ j) p) CPS.JNil
--         (CPS.MCons j'
--          (CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)) CPS.MVar)
--     ≡⟨ correctJ (loc-current at-var m-current) {!   !} ⟩
--       {!   !}
--     ≡⟨ cong (λ h' → cpsP p j (CPS.MCons j' h' CPS.MVar)) h'≡h ⟩
--       cpsP p j (CPS.MCons j' h CPS.MVar)
--     ∎
--     where
--       h' = CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)
--       h'≡h =  {!   !}

--   correctJM {j = j} {m = m} (loc-stored tj (m-cons {j₁} x {m₁} tm {h})) p =
--     begin
--       cpsP (DS.plugM (dsM (CPS.MCons j₁ h m₁)) (DS.plug (dsJ j) p))
--         CPS.JVar CPS.MVar
--     ≡⟨ refl ⟩
--       cpsP
--         (DS.plugM (dsM m₁)
--          (DS.plug (dsJ j₁) (DS.Handle (DS.plug (dsJ j) p) (dsH h))))
--         CPS.JVar CPS.MVar
--     ≡⟨ correctJM (loc-stored x tm) (DS.Handle (DS.plug (dsJ j) p) (dsH h)) ⟩
--       cpsP (DS.Handle (DS.plug (dsJ j) p) (dsH h)) j₁ m₁
--     ≡⟨ refl ⟩
--       cpsP (DS.plug (dsJ j) p) CPS.JNil
--         (CPS.MCons j₁
--          (CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)) m₁)
--     ≡⟨ correctJ {!   !} {!   !} ⟩
--       cpsP p j (CPS.MCons j₁ h' m₁)
--     ≡⟨ cong (λ h' → cpsP p j (CPS.MCons j₁ h' m₁)) h'≡h ⟩
--       cpsP p j (CPS.MCons j₁ h m₁)
--     ∎
--     where 
--       h' = CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)
--       h'≡h = {!   !}

--   correctJ = {!   !}

  -- correctJM-one : {var : Set}
  --               → {jc jo : CPS.cont[ var ]}
  --               → {h : var → var → CPS.term[ var ]}
  --               → JEndsAt jClosed jc 
  --               → JEndsAt jOpen jo 
  --               → ((v r : var)
  --                   → cpsP (dsP (h v r)) CPS.JVar CPS.MVar ≡ h v r)
  --               → (p : DS.comp[ var ])
  --               → cpsP (DS.plugM (dsM (CPS.MCons jo (CPS.HFun h) CPS.MVar))
  --                         (DS.plug (dsJ jc) p))
  --                       CPS.JVar CPS.MVar
  --               ≡ cpsP p jc (CPS.MCons jo (CPS.HFun h) CPS.MVar)
  -- correctJM-one {jc = jc} {jo = jo} {h = h} ec eo eh p = 
  --   begin
  --     cpsP
  --       (DS.plugM (dsM (CPS.MCons jo (CPS.HFun h) CPS.MVar))
  --        (DS.plug (dsJ jc) p))
  --       CPS.JVar CPS.MVar
  --   ≡⟨ refl ⟩
  --       cpsP
  --         (DS.plug (dsJ jo)
  --           (DS.Handle (DS.plug (dsJ jc) p) (λ v r → dsP (h v r))))
  --         CPS.JVar CPS.MVar
  --   ≡⟨ correctJ eo (DS.Handle (DS.plug (dsJ jc) p) (λ v r → dsP (h v r))) CPS.MVar ⟩
  --     cpsP (DS.Handle (DS.plug (dsJ jc) p) (λ v r → dsP (h v r))) 
  --       jo CPS.MVar
  --   ≡⟨ refl ⟩
  --     cpsP (DS.plug (dsJ jc) p) CPS.JNil
  --       (CPS.MCons jo
  --         (CPS.HFun (λ v r → cpsP (dsP (h v r)) CPS.JVar CPS.MVar)) CPS.MVar)
  --   ≡⟨ correctJ ec p (CPS.MCons jo
  --      (CPS.HFun (λ v r → cpsP (dsP (h v r)) CPS.JVar CPS.MVar)) CPS.MVar) ⟩
  --     cpsP p jc (CPS.MCons jo
  --        (CPS.HFun h') CPS.MVar)
  --   ≡⟨ cong (λ h' → cpsP p jc (CPS.MCons jo (CPS.HFun h') CPS.MVar)) h'≡h ⟩ 
  --     cpsP p jc (CPS.MCons jo 
  --        (CPS.HFun h) CPS.MVar)
  --   ∎
  --   where
  --     h' = λ v r → cpsP (dsP (h v r)) CPS.JVar CPS.MVar
  --     h'≡h = extensionality λ x → 
  --               extensionality λ k → eh x k
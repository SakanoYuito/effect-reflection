-- completeness
module Reflect4 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning

import DS 
import CPS 
open import DS-CPS
open import CPS-DS
open import Extensionality
-- open CPS.Reasoning


-- P → Q implies F[P] → F[Q]
reduce-plugF  : {var : Set}
              → (f : DS.PCtx[ var ])
              → {p q : DS.comp[ var ]}
              → DS.Reduce p q 
              → DS.Reduce
                  (DS.plug f p)
                  (DS.plug f q)
-- P → Q implies G[P] → G[Q]
reduce-plugG  : {var : Set}
              → (g : DS.MCtx[ var ])
              → {p q : DS.comp[ var ]}
              → DS.Reduce p q 
              → DS.Reduce
                  (DS.plugM g p)
                  (DS.plugM g q)
-- P → Q implies m♯♯[ j♭♭[P] ] → m♯♯[ j♭♭[Q] ]
reduce-plug : {var : Set}
            → {μ : CPS.Mode}
            → {p q : DS.comp[ var ]}
            → (m : CPS.mcont[ var ] μ)
            → (j : CPS.cont[ var ] μ)
            → DS.Reduce p q
            → DS.Reduce
                (DS.plugM (dsM m) (DS.plug (dsJ j) p))
                (DS.plugM (dsM m) (DS.plug (dsJ j) q))

reduce-plugF DS.FHole red = red
reduce-plugF (DS.FLet f p) red = reduce-plugF f (DS.RLet₁ red)
reduce-plugG DS.MHole red = red
reduce-plugG (DS.MHandle g f h) red = reduce-plugG g (reduce-plugF f (DS.RHandle₁ red))
reduce-plug m j p = reduce-plugG (dsM m) (reduce-plugF (dsJ j) p)


-- J'♭♭[P] = J♭♭[ J₀♭♭[P] ] where J₀[J/j] = J'
plug-J-current  : {var : Set}
                → {μ  : CPS.Mode} 
                → (j₀ : CPS.cont[ var ] CPS.current)
                → (j  : CPS.cont[ var ] μ)
                → (p  : DS.comp[ var ])
                → DS.plug (dsJ (CPS.JSubstJ j₀ j)) p
                ≡ DS.plug (dsJ j) (DS.plug (dsJ j₀) p)
plug-J-current CPS.JVar j p = refl
plug-J-current (CPS.JCons (CPS.KLet q) j₀) j p = plug-J-current j₀ j (DS.Let p (λ x → dsP (q x)))

-- J₀[J/j] = J₀
JSubst-stored : {var : Set}
              → {μ  : CPS.Mode}
              → (j₀ : CPS.cont[ var ] CPS.stored)
              → (j  : CPS.cont[ var ] μ)
              → CPS.JSubstJ j₀ j ≡ j₀
JSubst-stored CPS.JNil j = refl
JSubst-stored (CPS.JCons k j₀) j = cong (CPS.JCons k) (JSubst-stored j₀ j)

-- (M'♯♯[ J'♭♭[P] ]) = M♯♯[ J♭♭[ M₀♯♯[ J₀♭♭[P] ] ] ]
--   where M₀[M/m, J/j] = M' and J₀[J/j] = J'
plug-JM : {var : Set}
        → {μ ν : CPS.Mode}
        → (j₀ : CPS.cont[ var ] ν)
        → (m₀ : CPS.mcont[ var ] ν)
        → (j  : CPS.cont[ var ] μ)
        → (m  : CPS.mcont[ var ] μ)
        → (p  : DS.comp[ var ])
        → DS.plugM (dsM (CPS.JMSubstM m₀ j m))
              (DS.plug (dsJ (CPS.JSubstJ j₀ j)) p)
        ≡ DS.plugM (dsM m)
            (DS.plug (dsJ j)
              (DS.plugM (dsM m₀)
                (DS.plug (dsJ j₀) p)))
plug-JM CPS.JVar CPS.MVar j m p =
  begin
    DS.plugM (dsM (CPS.JMSubstM CPS.MVar j m))
      (DS.plug (dsJ (CPS.JSubstJ CPS.JVar j)) p)
  ≡⟨ refl ⟩
    DS.plugM (dsM m) (DS.plug (dsJ j) p)
  ≡⟨ refl ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ j)
       (DS.plugM (dsM CPS.MVar) (DS.plug (dsJ CPS.JVar) p)))
  ∎
  where open ≡-Reasoning
plug-JM (CPS.JCons (CPS.KLet q) j₀) CPS.MVar j m p = 
  begin
    DS.plugM (dsM (CPS.JMSubstM CPS.MVar j m))
      (DS.plug (dsJ (CPS.JSubstJ (CPS.JCons (CPS.KLet q) j₀) j)) p)
  ≡⟨ refl ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ (CPS.JSubstJ j₀ j)) (DS.Let p (λ x → dsP (q x))))
  ≡⟨ cong (DS.plugM (dsM m)) (plug-J-current (CPS.JCons (CPS.KLet q) j₀) j p) ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ j) (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j₀)) p))
  ≡⟨ refl ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ j) (DS.plug (dsJ j₀) (DS.Let p (λ x → dsP (q x)))))
  ≡⟨ refl ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ j)
       (DS.plugM (dsM CPS.MVar)
        (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j₀)) p)))
  ∎
  where open ≡-Reasoning
plug-JM j₀ (CPS.MCons j₁ h m₁) j m p =
  begin
    DS.plugM (dsM (CPS.JMSubstM (CPS.MCons j₁ h m₁) j m))
      (DS.plug (dsJ (CPS.JSubstJ j₀ j)) p)
  ≡⟨ refl ⟩
    DS.plugM (dsM (CPS.JMSubstM m₁ j m))
      (DS.plug (dsJ (CPS.JSubstJ j₁ j))
       (DS.Handle (DS.plug (dsJ (CPS.JSubstJ j₀ j)) p) (dsH h)))
  ≡⟨ cong (λ j' → DS.plugM (dsM (CPS.JMSubstM m₁ j m))
                   (DS.plug (dsJ (CPS.JSubstJ j₁ j))
                    (DS.Handle (DS.plug (dsJ j') p) (dsH h)))) 
       (JSubst-stored j₀ j) ⟩
    DS.plugM (dsM (CPS.JMSubstM m₁ j m))
      (DS.plug (dsJ (CPS.JSubstJ j₁ j))
       (DS.Handle (DS.plug (dsJ j₀) p) (dsH h)))
  ≡⟨ plug-JM j₁ m₁ j m (DS.Handle (DS.plug (dsJ j₀) p) (dsH h)) ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ j)
       (DS.plugM (dsM m₁)
        (DS.plug (dsJ j₁) (DS.Handle (DS.plug (dsJ j₀) p) (dsH h)))))
  ≡⟨ refl ⟩
    DS.plugM (dsM m)
      (DS.plug (dsJ j)
       (DS.plugM (dsM (CPS.MCons j₁ h m₁)) (DS.plug (dsJ j₀) p)))
  ∎
  where open ≡-Reasoning

-- (P[J/j, M/m])♯ = M♯♯[ J♭♭[ P♯ ]]
ds-JMsubst  : {var : Set}
            → {μ : CPS.Mode}
            → (p : CPS.term[ var ])
            → (j : CPS.cont[ var ] μ)
            → (m : CPS.mcont[ var ] μ)
            → dsP (CPS.JMSubst p j m)
            ≡ DS.plugM (dsM m) (DS.plug (dsJ j) (dsP p))
ds-JMsubst (CPS.Send j v m) j' m' =
  begin
    dsP (CPS.JMSubst (CPS.Send j v m) j' m')
  ≡⟨ refl ⟩
    DS.plugM (dsM (CPS.JMSubstM m j' m'))
      (DS.plug (dsJ (CPS.JSubstJ j j')) (DS.Return (dsV v)))
  ≡⟨ plug-JM j m j' m' (DS.Return (dsV v)) ⟩
    DS.plugM (dsM m')
      (DS.plug (dsJ j')
       (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))))
  ≡⟨ refl ⟩
    DS.plugM (dsM m') (DS.plug (dsJ j') (dsP (CPS.Send j v m)))
  ∎
  where open ≡-Reasoning
ds-JMsubst (CPS.Add j v w m) j' m' = plug-JM j m j' m' (DS.Add (dsV v) (dsV w))
ds-JMsubst (CPS.App v w j m) j' m' = plug-JM j m j' m' (DS.App (dsV v) (dsV w))
ds-JMsubst (CPS.Op m v j) j' m'    = plug-JM j m j' m' (DS.Op (dsV v))

interleaved mutual
  -- P[V/x] = P' implies P♯[V♮/x] = P'♯
  ds-subst  : {var : Set}
            → {p  : var → CPS.term[ var ]}
            → {p' : CPS.term[ var ]}
            → {v : CPS.value[ var ]}
            → (sub : CPS.VSubst p v p')
            → DS.Subst
                (λ x → dsP (p x)) (dsV v) (dsP p')
  -- V[W/x] = V' implies V♮[W♮/x] = V'♮
  ds-substV : {var : Set}
            → {v : var → CPS.value[ var ]}
            → {w v' : CPS.value[ var ]}
            → (sub : CPS.VSubstV v w v')
            → DS.SubstV 
                (λ x → dsV (v x)) (dsV w) (dsV v')
  -- J[V/x] = J' and P[V/x] = P' implies (J♭♭[P])[V♮/x] = J'♭♭[P']
  ds-substJ : {var : Set}
            → {μ  : CPS.Mode}
            → {j  : var → CPS.cont[ var ] μ}
            → {j' : CPS.cont[ var ] μ}
            → {v  : CPS.value[ var ]}
            → {p  : var → DS.comp[ var ]}
            → {p' : DS.comp[ var ]}
            → (subj : CPS.VSubstJ j v j')
            → (subp : DS.Subst p (dsV v) p')
            → DS.Subst
                (λ x → DS.plug (dsJ (j x)) (p x))
                (dsV v)
                (DS.plug (dsJ j') p')
  -- M[V/x] = M' and P[V/x] = P' implies (M♯♯[P])[V♮/x] = M'♯♯[P']
  ds-substM : {var : Set}
            → {μ  : CPS.Mode}
            → {m  : var → CPS.mcont[ var ] μ}
            → {m' : CPS.mcont[ var ] μ}
            → {v  : CPS.value[ var ]}
            → {p  : var → DS.comp[ var ]}
            → {p' : DS.comp[ var ]}
            → (subm : CPS.VSubstM m v m')
            → (subp : DS.Subst p (dsV v) p')
            → DS.Subst
                (λ x → DS.plugM (dsM (m x)) (p x))
                (dsV v)
                (DS.plugM (dsM m') p')
  
  ds-substV CPS.sVar= = DS.sVar=
  ds-substV CPS.sVar≠ = DS.sVar≠
  ds-substV CPS.sNum = DS.sNum
  ds-substV (CPS.sFun x) = DS.sFun λ v → ds-subst (x v)

  ds-substJ CPS.sJVar subp = subp
  ds-substJ CPS.sJNil subp = subp
  ds-substJ (CPS.sJCons (CPS.sKFun q) subj) subp =
      ds-substJ subj (DS.sLet subp λ v → ds-subst (q v))

  ds-substM CPS.sMVar subp = subp
  ds-substM (CPS.sMCons subj (CPS.sHFun q) subm) subp = 
      ds-substM subm (ds-substJ subj (DS.sHandle subp λ x k → ds-subst (q x k)))

  ds-subst (CPS.sSend subj subv subm) = ds-substM subm (ds-substJ subj (DS.sReturn (ds-substV subv)))
  ds-subst (CPS.sAdd subj subv subw subm) = ds-substM subm (ds-substJ subj (DS.sAdd (ds-substV subv) (ds-substV subw)))
  ds-subst (CPS.sApp subv subw subj subm) = ds-substM subm (ds-substJ subj (DS.sApp (ds-substV subv) (ds-substV subw)))
  ds-subst (CPS.sOp subm subv subj) = ds-substM subm (ds-substJ subj (DS.sOp (ds-substV subv)))

-- P[V/x, W/y] = P' implies P♯[V♮/x, W♮/y] = P'♯
ds-subst2 : {var : Set}
          → {p : var → var → CPS.term[ var ]}
          → {v w : CPS.value[ var ]}
          → {q : CPS.term[ var ]}
          → CPS.VSubst2 p v w q 
          → DS.Subst2 
              (λ x k → dsP (p x k))
              (dsV v) (dsV w)
              (dsP q)
ds-subst2 (CPS.sSubst2 subx suby) = DS.sSubst2 (λ y → ds-subst (subx y)) (ds-subst suby)

-- 
ds-openJ  : {var : Set}
          → (j : CPS.cont[ var ] CPS.stored)
          → dsJ (CPS.openJ j) ≡ dsJ j
ds-openJ CPS.JNil = refl
ds-openJ (CPS.JCons (CPS.KLet p) j) = cong (λ j' → DS.FLet j' (λ x → dsP (p x))) (ds-openJ j)

-- (λy. λj. λm. (F >> j) y m)♮ = λy. F♭♭[Return y]
ds-resumption : {var : Set}
              → (f : CPS.cont[ var ] CPS.stored)
              → dsV (CPS.Fun λ y →
                   CPS.Send (CPS.openJ f) (CPS.Var y) CPS.MVar)
              ≡ DS.Fun (λ y →
                   DS.plug (dsJ f) (DS.Return (DS.Var y)))
ds-resumption f = cong DS.Fun (extensionality λ v → 
                    cong (λ j' → DS.plug j' (DS.Return (DS.Var v))) (ds-openJ f))

interleaved mutual 
  -- P → Q implies P♯ → Q♯
  correctP  : {var : Set}
            → {p q : CPS.term[ var ]}
            → CPS.Reduce p q
            → DS.Reduce (dsP p) (dsP q)
  
  -- J → J' implies J♭♭[P] → J'♭♭[P]
  correctJ  : {var : Set}
            → {μ : CPS.Mode}
            → {j j' : CPS.cont[ var ] μ}
            → (p : DS.comp[ var ])
            → CPS.ReduceJ j j'
            → DS.Reduce (DS.plug (dsJ j) p) (DS.plug (dsJ j') p)
  -- M → M' implies M♯♯[P] → M'♯♯[P]
  correctM  : {var : Set}
            → {μ : CPS.Mode}
            → {m m' : CPS.mcont[ var ] μ}
            → (p : DS.comp[ var ])
            → CPS.ReduceM m m'
            → DS.Reduce (DS.plugM (dsM m) p) (DS.plugM (dsM m') p)
  -- V → V' implies V♮ → V'♮
  correctV  : {var : Set}
            → {v v' : CPS.value[ var ]}
            → CPS.ReduceV v v' 
            → DS.ReduceV (dsV v) (dsV v')
  -- K → K' implies K♭ → K'♭
  correctK  : {var : Set}
            → {k k' : CPS.frame[ var ]}
            → (p : DS.comp[ var ])
            → CPS.ReduceK k k'
            → DS.Reduce (DS.plug (dsK k) p) (DS.plug (dsK k') p)
  -- H → H' implies H‡ → H'‡
  correctH  : {var : Set}
            → {h h' : CPS.handler[ var ]}
            → CPS.ReduceH h h'
            → (v r : var)
            → DS.Reduce (dsH h v r) (dsH h' v r)

  correctV CPS.REtaV = DS.REtaV
  correctV (CPS.RFun x) = DS.RFun λ v → correctP (x v)

  correctK p (CPS.RKLet x) = DS.RLet₂ λ v → correctP (x v)

  correctH (CPS.RHFun {p} {p'} x) v r = correctP (x v r) 

  correctJ p (CPS.REtaLet {j = j}) = reduce-plugF (dsJ j) DS.REtaLet
  correctJ p (CPS.RAssoc {k₁ = CPS.KLet q} {k₂ = CPS.KLet r} {j = j}) = 
    begin
      DS.plug (dsJ (CPS.JCons (CPS.KLet q) (CPS.JCons (CPS.KLet r) j))) p
    ⟶⟨ reduce-plugF (dsJ j) DS.RAssoc ⟩
      DS.plug (dsJ j)
        (DS.Let p (λ x → 
            DS.Let (dsP (q x)) (λ x₁ → dsP (r x₁))))
    ≡⟨ cong (λ body → DS.plug (dsJ j) (DS.Let p body)) 
        (extensionality λ x → 
          sym (ds-JMsubst (q x) (CPS.JCons (CPS.KLet r) CPS.JVar) CPS.MVar)) ⟩
      DS.plug (dsJ j) 
        (DS.Let p (λ x → 
            dsP (CPS.JMSubst (q x) (CPS.JCons (CPS.KLet r) CPS.JVar) CPS.MVar)))
    ≡⟨ refl ⟩
      DS.plug
        (dsJ (CPS.JCons (CPS.composeK (CPS.KLet q) (CPS.KLet r)) j)) p
    ∎
    where open DS.OneStepReasoning
  correctJ p (CPS.RJConsK {j = j} (CPS.RKLet red)) = reduce-plugF (dsJ j) (DS.RLet₂ λ x → correctP (red x))
  correctJ p (CPS.RJConsJ {k = CPS.KLet q} red) = correctJ (DS.Let p (λ x → dsP (q x))) red

  correctM p (CPS.RMConsJ {j = j} {j'} {CPS.HFun h} {m} red) = 
    begin
      DS.plugM (dsM (CPS.MCons j (CPS.HFun h) m)) p
    ≡⟨ refl ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.Handle p (λ v r → dsP (h v r))))
    ⟶⟨ reduce-plugG (dsM m) (correctJ (DS.Handle p (λ v r → dsP (h v r)))  red) ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j') (DS.Handle p (λ v r → dsP (h v r))))
    ≡⟨ refl ⟩
      DS.plugM (dsM (CPS.MCons j' (CPS.HFun h) m)) p
    ∎
    where open DS.OneStepReasoning
  correctM p (CPS.RMConsH {j = j} {CPS.HFun h} {CPS.HFun h'} {m} red) =
    begin
      DS.plugM (dsM (CPS.MCons j (CPS.HFun h) m)) p
    ≡⟨ refl ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.Handle p (λ v r → dsP (h v r))))
    ⟶⟨ reduce-plug m j (DS.RHandle₂ λ x k → correctH red x k) ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.Handle p (λ v r → dsP (h' v r))))
    ≡⟨ refl ⟩
      DS.plugM (dsM (CPS.MCons j (CPS.HFun h') m)) p
    ∎
    where open DS.OneStepReasoning
  correctM p (CPS.RMConsM {j = j} {CPS.HFun h} {m} {m'} red) =
    begin
      DS.plugM (dsM (CPS.MCons j (CPS.HFun h) m)) p
    ≡⟨ refl ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.Handle p (λ v r → dsP (h v r))))
    ⟶⟨ correctM (DS.plug (dsJ j) (DS.Handle p (λ v r → dsP (h v r)))) red ⟩
      DS.plugM (dsM m')
        (DS.plug (dsJ j) (DS.Handle p (λ v r → dsP (h v r))))
    ≡⟨ refl ⟩
      DS.plugM (dsM (CPS.MCons j (CPS.HFun h) m')) p
    ∎
    where open DS.OneStepReasoning

  correctP (CPS.RBetaV {p = p} {v} {j} {m} {p'} x) = 
    begin
      dsP (CPS.App (CPS.Fun p) v j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.App (DS.Fun (λ x → dsP (p x))) (dsV v)))
    ⟶⟨ reduce-plug m j (DS.RBetaV (ds-subst x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (dsP p'))
    ≡⟨ sym (ds-JMsubst p' j m) ⟩
      dsP (CPS.JMSubst p' j m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RBetaLet {p = p} {v} {j} {m} {p'} x) =
    begin
      dsP (CPS.Send (CPS.JCons (CPS.KLet p) j) v m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.Let (DS.Return (dsV v)) (λ x → dsP (p x))))
    ⟶⟨ reduce-plug m j (DS.RBetaLet (ds-subst x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (dsP p'))
    ≡⟨ sym (ds-JMsubst p' j m) ⟩
      dsP (CPS.JMSubst p' j m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RDelta+ {j = j} {n₁} {n₂} {m}) = 
    begin
      dsP (CPS.Add j (CPS.Num n₁) (CPS.Num n₂) m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (DS.Num n₁) (DS.Num n₂)))
    ⟶⟨ reduce-plug m j DS.RDelta+ ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (DS.Num (n₁ + n₂))))
    ≡⟨ sym (ds-JMsubst (CPS.Send CPS.JVar (CPS.Num (n₁ + n₂)) CPS.MVar) j m) ⟩
      dsP
        (CPS.JMSubst (CPS.Send CPS.JVar (CPS.Num (n₁ + n₂)) CPS.MVar) j m)
    ≡⟨ refl ⟩
      dsP (CPS.Send j (CPS.Num (n₁ + n₂)) m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RHandleRet {j = j} {v} {h} {m}) =
    begin
      dsP (CPS.Send CPS.JNil v (CPS.MCons j h m))
    ≡⟨ refl ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ j) (DS.Handle (DS.Return (dsV v)) (dsH h)))
    ⟶⟨ reduce-plug m j DS.RHandleRet ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))
    ≡⟨ sym (ds-JMsubst (CPS.Send CPS.JVar v CPS.MVar) j m) ⟩
      dsP (CPS.JMSubst (CPS.Send CPS.JVar v CPS.MVar) j m)
    ≡⟨ refl ⟩
      dsP (CPS.Send j v m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RHandleOp {v = v} {jc} {j₀} {m₀} {p} {p'} x) =
    begin
      dsP (CPS.Op (CPS.MCons j₀ (CPS.HFun p) m₀) v jc)
    ≡⟨ refl ⟩
      DS.plugM (dsM m₀)
        (DS.plug (dsJ j₀)
         (DS.Handle (DS.plug (dsJ jc) (DS.Op (dsV v)))
          (λ v r → dsP (p v r))))
    ⟶⟨ reduce-plug m₀ j₀ (DS.RHandleOp {f = dsJ jc} (ds-subst2-op x)) ⟩
      DS.plugM (dsM m₀) (DS.plug (dsJ j₀) (dsP p'))
    ≡⟨ sym (ds-JMsubst p' j₀ m₀) ⟩
      dsP (CPS.JMSubst p' j₀ m₀)
    ∎
    where 
      open DS.OneStepReasoning
      ds-subst2-op : {var : Set}
                   → {p : var → var → CPS.term[ var ]}
                   → {v : CPS.value[ var ]}
                   → {jc : CPS.cont[ var ] CPS.stored}
                   → {q : CPS.term[ var ]}
                   → CPS.VSubst2 
                        p 
                        v (CPS.Fun λ y → CPS.Send (CPS.openJ jc) (CPS.Var y) CPS.MVar) 
                        q
                   → DS.Subst2 
                        (λ x k → dsP (p x k)) 
                        (dsV v) (DS.Fun λ y → DS.plug (dsJ jc) (DS.Return (DS.Var y))) 
                        (dsP q)
      ds-subst2-op {jc = jc} sub 
        rewrite sym (ds-resumption jc) = ds-subst2 sub

  -- congruence rules
  correctP (CPS.RSendJ {j = j} {j'} {v} {m} x) = 
    begin
      dsP (CPS.Send j v m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))
    ⟶⟨ reduce-plugG (dsM m) (correctJ (DS.Return (dsV v)) x) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j') (DS.Return (dsV v)))
    ≡⟨ refl ⟩
      dsP (CPS.Send j' v m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RSendV {j = j} {v} {v'} {m} x) =
    begin
      dsP (CPS.Send j v m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))
    ⟶⟨ reduce-plug m j (DS.RReturn (correctV x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v')))
    ≡⟨ refl ⟩
      dsP (CPS.Send j v' m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RSendM {j = j} {v} {m} {m'} x) =
    begin
      dsP (CPS.Send j v m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))
    ⟶⟨ correctM (DS.plug (dsJ j) (DS.Return (dsV v))) x ⟩
      DS.plugM (dsM m') (DS.plug (dsJ j) (DS.Return (dsV v)))
    ≡⟨ refl ⟩
      dsP (CPS.Send j v m')
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RAppV {v = v} {v'} {w} {j} {m} x) =
    begin
      dsP (CPS.App v w j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w)))
    ⟶⟨ reduce-plug m j (DS.RApp₁ (correctV x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v') (dsV w)))
    ≡⟨ refl ⟩
      dsP (CPS.App v' w j m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RAppW {v = v} {w} {w'} {j} {m} x) =
    begin
      dsP (CPS.App v w j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w)))
    ⟶⟨ reduce-plug m j (DS.RApp₂ (correctV x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w')))
    ≡⟨ refl ⟩
      dsP (CPS.App v w' j m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RAppJ {v = v} {w} {j} {j'} {m} x) =
    begin
      dsP (CPS.App v w j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w)))
    ⟶⟨ reduce-plugG (dsM m) (correctJ (DS.App (dsV v) (dsV w)) x) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j') (DS.App (dsV v) (dsV w)))
    ≡⟨ refl ⟩
      dsP (CPS.App v w j' m)
    ∎
    where open DS.OneStepReasoning 
  correctP (CPS.RAppM {v = v} {w} {j} {m} {m'} x) =
    begin
      dsP (CPS.App v w j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w)))
    ⟶⟨ correctM (DS.plug (dsJ j) (DS.App (dsV v) (dsV w))) x ⟩
      DS.plugM (dsM m') (DS.plug (dsJ j) (DS.App (dsV v) (dsV w)))
    ≡⟨ refl ⟩
      dsP (CPS.App v w j m')
    ∎
    where open DS.OneStepReasoning 
  correctP (CPS.RAddV {v = v} {v'} {w} {j} {m} x) = 
    begin
      dsP (CPS.Add j v w m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w)))
    ⟶⟨ reduce-plug m j (DS.RAdd₁ (correctV x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v') (dsV w)))
    ≡⟨ refl ⟩
      dsP (CPS.Add j v' w m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RAddW {v = v} {w} {w'} {j} {m} x) = 
    begin
      dsP (CPS.Add j v w m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w)))
    ⟶⟨ reduce-plug m j (DS.RAdd₂ (correctV x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w')))
    ≡⟨ refl ⟩
      dsP (CPS.Add j v w' m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RAddJ {v = v} {w} {j} {j'} {m} x) = 
    begin
      dsP (CPS.Add j v w m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w)))
    ⟶⟨ reduce-plugG (dsM m) (correctJ (DS.Add (dsV v) (dsV w)) x) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j') (DS.Add (dsV v) (dsV w)))
    ≡⟨ refl ⟩
      dsP (CPS.Add j' v w m)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.RAddM {v = v} {w} {j} {m} {m'} x) = 
    begin
      dsP (CPS.Add j v w m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w)))
    ⟶⟨ correctM (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w))) x ⟩
      DS.plugM (dsM m') (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w)))
    ≡⟨ refl ⟩
      dsP (CPS.Add j v w m')
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.ROpJ {j = j} {j'} {v} {m} x) = 
    begin
      dsP (CPS.Op m v j)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))
    ⟶⟨ reduce-plugG (dsM m) (correctJ (DS.Op (dsV v)) x) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j') (DS.Op (dsV v)))
    ≡⟨ refl ⟩
      dsP (CPS.Op m v j')
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.ROpV {j = j} {v} {v'} {m} x) = 
    begin
      dsP (CPS.Op m v j)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))
    ⟶⟨ reduce-plug m j (DS.ROp (correctV x)) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v')))
    ≡⟨ refl ⟩
      dsP (CPS.Op m v' j)
    ∎
    where open DS.OneStepReasoning
  correctP (CPS.ROpM {j = j} {v} {m} {m'} x) = 
    begin
      dsP (CPS.Op m v j)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))
    ⟶⟨ correctM (DS.plug (dsJ j) (DS.Op (dsV v))) x ⟩
      DS.plugM (dsM m') (DS.plug (dsJ j) (DS.Op (dsV v)))
    ≡⟨ refl ⟩
      dsP (CPS.Op m' v j)
    ∎
    where open DS.OneStepReasoning
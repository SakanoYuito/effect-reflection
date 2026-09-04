-- soundness
module Reflect3 where 

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning

import DS 
import CPS 
open import DS-CPS
open import CPS-DS
open import Extensionality
-- open CPS.Reasoning

interleaved mutual
  -- P[V/x] = P', J[V†/x] = J', M[V†/x] = M' implies  (P : J : M)[V†/x] = P' : J' : M'
  cps-subst : {var : Set}
            → {μ  : CPS.Mode}
            → {p  : var → DS.comp[ var ]}
            → {p' : DS.comp[ var ]}
            → {v  : DS.value[ var ]}
            → {j  : var → CPS.cont[ var ] μ}
            → {j' : CPS.cont[ var ] μ}
            → {m  : var → CPS.mcont[ var ] μ}
            → {m' : CPS.mcont[ var ] μ}
            → (subp : DS.Subst p v p')
            → (subj : CPS.VSubstJ j (cpsV v) j')
            → (subm : CPS.VSubstM m (cpsV v) m')
            → CPS.VSubst
                (λ x → cpsP (p x) (j x) (m x))
                (cpsV v)
                (cpsP p' j' m') 
  
  -- V[V'/x] = W implies (V†)[V'† /x] = W† 
  cps-substV : {var : Set}
            → {p : var → DS.value[ var ]}
            → {v p' : DS.value[ var ]}
            → (subv : DS.SubstV p v p')
            → CPS.VSubstV
                (λ x → cpsV (p x))
                (cpsV v)
                (cpsV p')

  cps-subst (DS.sReturn v) j m = CPS.sSend j (cps-substV v) m
  cps-subst (DS.sApp v w) j m = CPS.sApp (cps-substV v) (cps-substV w) j m
  cps-subst (DS.sAdd v w) j m = CPS.sAdd j (cps-substV v) (cps-substV w) m
  cps-subst (DS.sLet p q) j m = cps-subst p 
                                  (CPS.sJCons 
                                    (CPS.sKFun λ x → cps-subst (q x) CPS.sJVar CPS.sMVar) j) m
  cps-subst (DS.sHandle p h) j m = cps-subst p CPS.sJNil 
                                    (CPS.sMCons j 
                                      (CPS.sHFun λ x k → cps-subst (h x k) CPS.sJVar CPS.sMVar) m)
  cps-subst (DS.sOp v) j m = CPS.sOp m (cps-substV v) j

  cps-substV DS.sVar= = CPS.sVar=
  cps-substV DS.sVar≠ = CPS.sVar≠
  cps-substV DS.sNum  = CPS.sNum
  cps-substV (DS.sFun f) = CPS.sFun λ x → cps-subst (f x) CPS.sJVar CPS.sMVar

-- P[V/x, W/k] = Q implies (P : j : m)[V†/x, W†/k] = Q : j : m
cps-subst2  : {var : Set}
            → {p : var → var → DS.comp[ var ]}
            → {v w : DS.value[ var ]}
            → {q : DS.comp[ var ]}
            → (sub : DS.Subst2 p v w q)
            → CPS.VSubst2 (λ x k → cpsP (p x k) CPS.JVar CPS.MVar)
                          (cpsV v) (cpsV w)
                          (cpsP q CPS.JVar CPS.MVar)
cps-subst2 (DS.sSubst2 s1 s2) = CPS.sSubst2 
          (λ k → cps-subst (s1 k) CPS.sJVar CPS.sMVar) 
          (cps-subst s2 CPS.sJVar CPS.sMVar)

-- (P : j₀ : m₀)[J/j, M/m] = P : j₀[J/j] : m₀[M/m]
cps-JMsubst' : {var : Set}
        → {μ ν : CPS.Mode}
        → (p   : DS.comp[ var ])
        → (j₀  : CPS.cont[ var ]  ν)
        → (m₀  : CPS.mcont[ var ] ν)
        → (j   : CPS.cont[ var ]  μ)
        → (m   : CPS.mcont[ var ] μ)
        → CPS.JMSubst (cpsP p j₀ m₀) j m
        ≡ cpsP p (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)

-- Especially, (P : j : m)[J/j, M/m] = P : J : M
cps-JMsubst : {var : Set}
            → {μ : CPS.Mode}
            → (p : DS.comp[ var ])
            → (j : CPS.cont[ var ] μ)
            → (m : CPS.mcont[ var ] μ)
            → CPS.JMSubst (cpsP p CPS.JVar CPS.MVar) j m
            ≡ cpsP p j m 

cps-JMsubst' (DS.Return v) j₀ m₀ j m = 
  begin
    CPS.JMSubst (cpsP (DS.Return v) j₀ m₀) j m
  ≡⟨ refl ⟩
    CPS.Send (CPS.JSubstJ j₀ j) (cpsV v) (CPS.JMSubstM m₀ j m)
  ≡⟨ refl ⟩
    cpsP (DS.Return v) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ∎
  where open ≡-Reasoning
cps-JMsubst' (DS.App v w) j₀ m₀ j m =
  begin
    CPS.JMSubst (cpsP (DS.App v w) j₀ m₀) j m
  ≡⟨ refl ⟩
    CPS.App (cpsV v) (cpsV w) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ≡⟨ refl ⟩
    cpsP (DS.App v w) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ∎ 
  where open ≡-Reasoning
cps-JMsubst' (DS.Add v w) j₀ m₀ j m =
  begin
    CPS.JMSubst (cpsP (DS.Add v w) j₀ m₀) j m
  ≡⟨ refl ⟩
    CPS.Add (CPS.JSubstJ j₀ j) (cpsV v) (cpsV w) (CPS.JMSubstM m₀ j m)
  ≡⟨ refl ⟩
    cpsP (DS.Add v w) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ∎ 
  where open ≡-Reasoning
cps-JMsubst' (DS.Let p q) j₀ m₀ j m =
  begin
    CPS.JMSubst (cpsP (DS.Let p q) j₀ m₀) j m
  ≡⟨ refl ⟩
    CPS.JMSubst
      (cpsP p
       (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j₀) m₀)
      j m
  ≡⟨ cps-JMsubst' p (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j₀) m₀ j m ⟩
    cpsP p
      (CPS.JSubstJ
       (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j₀) j)
      (CPS.JMSubstM m₀ j m)
  ≡⟨ refl ⟩
    cpsP p
      (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar))
       (CPS.JSubstJ j₀ j))
      (CPS.JMSubstM m₀ j m)
  ≡⟨ refl ⟩
    cpsP (DS.Let p q) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ∎
  where open ≡-Reasoning
cps-JMsubst' (DS.Handle p q) j₀ m₀ j m =
  begin
    CPS.JMSubst (cpsP (DS.Handle p q) j₀ m₀) j m
  ≡⟨ refl ⟩
    CPS.JMSubst
      (cpsP p CPS.JNil
       (CPS.MCons j₀ (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar))
        m₀))
      j m
  ≡⟨ cps-JMsubst' p CPS.JNil (CPS.MCons j₀ (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar))
     m₀) j m ⟩
    cpsP p (CPS.JSubstJ CPS.JNil j)
      (CPS.JMSubstM
       (CPS.MCons j₀ (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar))
        m₀)
       j m)
  ≡⟨ refl ⟩
    cpsP p CPS.JNil
      (CPS.MCons (CPS.JSubstJ j₀ j)
       (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar))
       (CPS.JMSubstM m₀ j m))
  ≡⟨ refl ⟩
    cpsP (DS.Handle p q) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ∎
  where open ≡-Reasoning
cps-JMsubst' (DS.Op v) j₀ m₀ j m = 
  begin
    CPS.JMSubst (cpsP (DS.Op v) j₀ m₀) j m
  ≡⟨ refl ⟩
    CPS.Op (CPS.JMSubstM m₀ j m) (cpsV v) (CPS.JSubstJ j₀ j)
  ≡⟨ refl ⟩
    cpsP (DS.Op v) (CPS.JSubstJ j₀ j) (CPS.JMSubstM m₀ j m)
  ∎
  where open ≡-Reasoning

cps-JMsubst p j m = cps-JMsubst' p CPS.JVar CPS.MVar j m

-- F[P] : J : M = P : (F : J) : M
cpsF-plug  : {var : Set}
          → {μ : CPS.Mode}
          → (f : DS.PCtx[ var ])
          → (p : DS.comp[ var ])
          → (j : CPS.cont[ var ] μ)
          → (m : CPS.mcont[ var ] μ)
          → cpsP (DS.plug f p) j m 
          ≡ cpsP p (cpsF f j) m

cpsF-plug DS.FHole p j m = refl
cpsF-plug (DS.FLet f q) p j m = cpsF-plug f (DS.Let p q) j m

-- F : j = (F : ()) >> j
cpsF-open : {var : Set}
          → (f : DS.PCtx[ var ])
          → cpsF f CPS.JVar
          ≡ CPS.openJ (cpsF f CPS.JNil) 
cpsF-open DS.FHole = refl
cpsF-open (DS.FLet f p) = 
      cong (λ y → CPS.JCons (CPS.KLet (λ x → cpsP (p x) CPS.JVar CPS.MVar)) y) 
        (cpsF-open f)

-- (λy. F[return y])† = λy. λj. λm. ((F : ()) >> j) y m
cps-resumption  : {var : Set}
                → (f : DS.PCtx[ var ])
                → cpsV (DS.Fun λ y → DS.plug f (DS.Return (DS.Var y)))
                ≡ CPS.Fun λ y → CPS.Send (CPS.openJ (cpsF f CPS.JNil)) (CPS.Var y) CPS.MVar
cps-resumption f = cong CPS.Fun (extensionality λ y → (
      begin
        cpsP (DS.plug f (DS.Return (DS.Var y))) CPS.JVar CPS.MVar
      ≡⟨ cpsF-plug f (DS.Return (DS.Var y)) CPS.JVar CPS.MVar ⟩
        cpsP (DS.Return (DS.Var y)) (cpsF f CPS.JVar) CPS.MVar
      ≡⟨ refl ⟩
        CPS.Send (cpsF f CPS.JVar) (CPS.Var y) CPS.MVar
      ≡⟨ cong (λ j → CPS.Send j (CPS.Var y) CPS.MVar) (cpsF-open f) ⟩
        CPS.Send (CPS.openJ (cpsF f CPS.JNil)) (CPS.Var y) CPS.MVar
      ∎
    ))
    where open ≡-Reasoning

-- P[V/x, (λy. F[return y])/k] = Q implies
--   (P : j : m)[V†/x, (λy. F[return y])†/k] = Q : j : m 
cps-subst2-op : {var : Set}
              → {p : var → var → DS.comp[ var ]}
              → {f : DS.PCtx[ var ]}
              → {v : DS.value[ var ]}
              → {q : DS.comp[ var ]}
              → DS.Subst2 p 
                          v (DS.Fun (λ y → DS.plug f (DS.Return (DS.Var y)))) 
                          q
              → CPS.VSubst2 (λ x k → cpsP (p x k) CPS.JVar CPS.MVar) 
                            (cpsV v) 
                            (CPS.Fun λ y → CPS.Send (CPS.openJ (cpsF f CPS.JNil)) (CPS.Var y) CPS.MVar)
                            (cpsP q CPS.JVar CPS.MVar)
cps-subst2-op {var} {p} {f} {v} {q} sub =
  subst substAtR res-eq subst-res₁
  where
    -- (λy. F[return y])† 
    res₁ : CPS.value[ var ]
    res₁ = cpsV (DS.Fun λ y → DS.plug f (DS.Return (DS.Var y)))
    -- λy. λj. λm. ((F : ()) >> j) y m
    res₂ : CPS.value[ var ]
    res₂ = CPS.Fun (λ y → CPS.Send (CPS.openJ (cpsF f CPS.JNil)) (CPS.Var y) CPS.MVar)

    res-eq : res₁ ≡ res₂
    res-eq = cps-resumption f

    substAtR : CPS.value[ var ] → Set 
    substAtR r = CPS.VSubst2 (λ x k → cpsP (p x k) CPS.JVar CPS.MVar) 
                             (cpsV v) 
                             r
                             (cpsP q CPS.JVar CPS.MVar)

    subst-res₁ : substAtR res₁
    subst-res₁ = cps-subst2 sub
    

interleaved mutual
  -- J → J' implies (P : J : M) → (P : J' : M)
  correctJ  : {var : Set}
            → {μ : CPS.Mode} 
            → {j j' : CPS.cont[ var ] μ}
            → (p : DS.comp[ var ])
            → (m : CPS.mcont[ var ] μ)
            → (red : CPS.ReduceJ j j')
            → CPS.Reduce (cpsP p j m) (cpsP p j' m)
  -- M → M' implies (P : J : M) → (P : J : M')
  correctM  : {var : Set}
            → {μ : CPS.Mode} 
            → {m m' : CPS.mcont[ var ] μ}
            → (p : DS.comp[ var ])
            → (j : CPS.cont[ var ] μ)
            → (red : CPS.ReduceM m m')
            → CPS.Reduce (cpsP p j m) (cpsP p j m')
  
  correctJ (DS.Return v) m red = CPS.RSendJ red
  correctJ (DS.App v w) m red = CPS.RAppJ red
  correctJ (DS.Add v w) m red = CPS.RAddJ red
  correctJ (DS.Let p q) m red = correctJ p m (CPS.RJConsJ red)
  correctJ (DS.Handle p q) m red = correctM p CPS.JNil (CPS.RMConsJ red)
  correctJ (DS.Op v) m red = CPS.ROpJ red

  correctM (DS.Return v) j red = CPS.RSendM red
  correctM (DS.App v w) j red = CPS.RAppM red
  correctM (DS.Add v w) j red = CPS.RAddM red
  correctM (DS.Let p q) j red = correctM p
    (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j) red
  correctM (DS.Handle p q) j red = correctM p CPS.JNil (CPS.RMConsM red)
  correctM (DS.Op v) j red = CPS.ROpM red

interleaved mutual
  -- P → Q implies (P : J : M) → (Q : J : M)
  correctP  : {var : Set}
            → {p q : DS.comp[ var ]}
            → {μ   : CPS.Mode}
            → (red : DS.Reduce p q) 
            → (j   : CPS.cont[ var ] μ)
            → (m   : CPS.mcont[ var ] μ)
            → CPS.Reduce (cpsP p j m) (cpsP q j m)
  -- V → W implies V† → W†
  correctV  : {var : Set}
            → {v w : DS.value[ var ]}
            → (red : DS.ReduceV v w)
            → CPS.ReduceV (cpsV v) (cpsV w)
  -- P → Q implies (λx. λj. λm. P) → (λx. λj. λm. Q)
  correctK  : {var : Set}
            → {p q : var → DS.comp[ var ]}
            → ((x : var) → DS.Reduce (p x) (q x))
            → CPS.ReduceK
                (CPS.KLet λ x →
                  cpsP (p x) CPS.JVar CPS.MVar)
                (CPS.KLet λ x →
                  cpsP (q x) CPS.JVar CPS.MVar)
  -- P → Q implies (λv. λr. λj. λm. P) → (λv. λr. λj. λm. Q)
  correctH  : {var : Set}
            → {p q : var → var → DS.comp[ var ]}
            → ((x k : var) → DS.Reduce (p x k) (q x k))
            → CPS.ReduceH 
                (CPS.HFun λ v r → cpsP (p v r) CPS.JVar CPS.MVar)
                (CPS.HFun λ v r → cpsP (q v r) CPS.JVar CPS.MVar)
  correctH red = CPS.RHFun λ v r → correctP (red v r) CPS.JVar CPS.MVar

  correctV DS.REtaV = CPS.REtaV
  correctV (DS.RFun f) = CPS.RFun λ x → correctP (f x) CPS.JVar CPS.MVar
  correctK red = CPS.RKLet λ x → correctP (red x) CPS.JVar CPS.MVar
  
  correctP {q = q} (DS.RBetaV {p} {v} sub) j m =
    begin
      cpsP (DS.App (DS.Fun p) v) j m
    ≡⟨ refl ⟩
      CPS.App (CPS.Fun (λ x → cpsP (p x) CPS.JVar CPS.MVar)) (cpsV v) j m
    ⟶⟨ CPS.RBetaV (cps-subst sub CPS.sJVar CPS.sMVar) ⟩
      CPS.JMSubst (cpsP q CPS.JVar CPS.MVar) j m
    ≡⟨ cps-JMsubst q j m ⟩
      cpsP q j m
    ∎
    where open CPS.OneStepReasoning
  correctP {q = q} (DS.RBetaLet {p} {v} sub) j m =
    begin
      cpsP (DS.Let (DS.Return v) p) j m
    ≡⟨ refl ⟩
      CPS.Send
        (CPS.JCons (CPS.KLet (λ v → cpsP (p v) CPS.JVar CPS.MVar)) j)
        (cpsV v) m
    ⟶⟨ CPS.RBetaLet (cps-subst sub CPS.sJVar CPS.sMVar) ⟩
      CPS.JMSubst (cpsP q CPS.JVar CPS.MVar) j m
    ≡⟨ cps-JMsubst q j m ⟩
      cpsP q j m
    ∎
    where open CPS.OneStepReasoning
  correctP {q = q} (DS.REtaLet {p}) j m =
    begin
      cpsP (DS.Let q (λ x → DS.Return (DS.Var x))) j m
    ≡⟨ refl ⟩
      cpsP q
        (CPS.JCons
         (CPS.KLet (λ v → CPS.Send CPS.JVar (CPS.Var v) CPS.MVar)) j)
        m
    ⟶⟨ correctJ q m CPS.REtaLet ⟩
      cpsP q j m
    ∎
    where open CPS.OneStepReasoning
  correctP {q = p'} (DS.RAssoc {p} {q} {r}) j m =
    begin
      cpsP (DS.Let (DS.Let p q) r) j m
    ≡⟨ refl ⟩
      cpsP p
        (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar))
         (CPS.JCons (CPS.KLet (λ v → cpsP (r v) CPS.JVar CPS.MVar)) j))
        m
    ⟶⟨ correctJ p m CPS.RAssoc ⟩
      cpsP p
        (CPS.JCons
         (CPS.composeK (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar))
          (CPS.KLet (λ v → cpsP (r v) CPS.JVar CPS.MVar)))
         j)
        m
    ≡⟨ refl ⟩
      cpsP p
        (CPS.JCons k j)
        m
    ≡⟨ cong (λ k → cpsP p (CPS.JCons k j) m) k'≡k ⟩
      cpsP p
        (CPS.JCons k' j)
        m
    ≡⟨ refl ⟩
      cpsP (DS.Let p (λ x → DS.Let (q x) r)) j m
    ∎
    where 
      open CPS.OneStepReasoning
      k = CPS.KLet
        (λ x →
           CPS.JMSubst (cpsP (q x) CPS.JVar CPS.MVar)
           (CPS.JCons (CPS.KLet (λ v → cpsP (r v) CPS.JVar CPS.MVar))
            CPS.JVar)
           CPS.MVar)
      k' = CPS.KLet (λ v → cpsP (DS.Let (q v) r) CPS.JVar CPS.MVar)
      k'≡k = cong CPS.KLet (extensionality λ x → 
                  cps-JMsubst (q x) (CPS.JCons (CPS.KLet (λ v → cpsP (r v) CPS.JVar CPS.MVar)) CPS.JVar) CPS.MVar)
  correctP (DS.RDelta+ {n₁} {n₂}) j m =
    begin
      cpsP (DS.Add (DS.Num n₁) (DS.Num n₂)) j m
    ≡⟨ refl ⟩
      CPS.Add j (CPS.Num n₁) (CPS.Num n₂) m
    ⟶⟨ CPS.RDelta+ ⟩
      CPS.Send j (CPS.Num (n₁ + n₂)) m
    ≡⟨ refl ⟩
      cpsP (DS.Return (DS.Num (n₁ + n₂))) j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RHandleRet {v} {p}) j m =
    begin
      cpsP (DS.Handle (DS.Return v) p) j m
    ≡⟨ refl ⟩
      CPS.Send CPS.JNil (cpsV v)
        (CPS.MCons j (CPS.HFun (λ v r → cpsP (p v r) CPS.JVar CPS.MVar)) m)
    ⟶⟨ CPS.RHandleRet ⟩
      CPS.Send j (cpsV v) m
    ≡⟨ refl ⟩
      cpsP (DS.Return v) j m
    ∎
    where open CPS.OneStepReasoning
  correctP {q = q} (DS.RHandleOp {p} {f} {v} sub) j m =
    begin
      cpsP (DS.Handle (DS.plug f (DS.Op v)) p) j m
    ≡⟨ refl ⟩
      cpsP (DS.plug f (DS.Op v)) CPS.JNil
        (CPS.MCons j (CPS.HFun (λ v r → cpsP (p v r) CPS.JVar CPS.MVar)) m)
    ≡⟨ cpsF-plug f (DS.Op v) CPS.JNil (CPS.MCons j (CPS.HFun (λ v₁ r → cpsP (p v₁ r) CPS.JVar CPS.MVar)) m) ⟩
      cpsP (DS.Op v) (cpsF f CPS.JNil)
        (CPS.MCons j (CPS.HFun (λ v₁ r → cpsP (p v₁ r) CPS.JVar CPS.MVar)) m)
    ≡⟨ refl ⟩
      CPS.Op
        (CPS.MCons j (CPS.HFun (λ v₁ r → cpsP (p v₁ r) CPS.JVar CPS.MVar))
         m)
        (cpsV v) (cpsF f CPS.JNil)
    ⟶⟨ CPS.RHandleOp (cps-subst2-op sub) ⟩
      CPS.JMSubst (cpsP q CPS.JVar CPS.MVar) j m
    ≡⟨ cps-JMsubst q j m ⟩
      cpsP q j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RReturn {v} {v'} x) j m =
    begin
      cpsP (DS.Return v) j m
    ≡⟨ refl ⟩
      CPS.Send j (cpsV v) m
    ⟶⟨ CPS.RSendV (correctV x) ⟩
      CPS.Send j (cpsV v') m
    ≡⟨ refl ⟩
      cpsP (DS.Return v') j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RApp₁ {v} {v'} {w} x) j m =
    begin
      cpsP (DS.App v w) j m
    ≡⟨ refl ⟩
      CPS.App (cpsV v) (cpsV w) j m
    ⟶⟨ CPS.RAppV (correctV x) ⟩
      CPS.App (cpsV v') (cpsV w) j m
    ≡⟨ refl ⟩
      cpsP (DS.App v' w) j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RApp₂ {v} {w} {w'} x) j m =
    begin
      cpsP (DS.App v w) j m
    ≡⟨ refl ⟩
      CPS.App (cpsV v) (cpsV w) j m
    ⟶⟨ CPS.RAppW (correctV x) ⟩
      CPS.App (cpsV v) (cpsV w') j m
    ≡⟨ refl ⟩
      cpsP (DS.App v w') j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RAdd₁ {v} {v'} {w} x) j m =
    begin
      cpsP (DS.Add v w) j m
    ≡⟨ refl ⟩
      CPS.Add j (cpsV v) (cpsV w) m
    ⟶⟨ CPS.RAddV (correctV x) ⟩
      CPS.Add j (cpsV v') (cpsV w) m
    ≡⟨ refl ⟩
      cpsP (DS.Add v' w) j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RAdd₂ {v} {w} {w'} x) j m =
    begin
      cpsP (DS.Add v w) j m
    ≡⟨ refl ⟩
      CPS.Add j (cpsV v) (cpsV w) m
    ⟶⟨ CPS.RAddW (correctV x) ⟩
      CPS.Add j (cpsV v) (cpsV w') m
    ≡⟨ refl ⟩
      cpsP (DS.Add v w') j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RLet₁ {p} {p'} {q} x) j m =
    begin
      cpsP (DS.Let p q) j m
    ≡⟨ refl ⟩
      cpsP p
        (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j) m
    ⟶⟨ correctP x (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j) m ⟩
      cpsP p'
        (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j) m
    ≡⟨ refl ⟩
      cpsP (DS.Let p' q) j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RLet₂ {p} {q} {q'} x) j m =
    begin
      cpsP (DS.Let p q) j m
    ≡⟨ refl ⟩
      cpsP p
        (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j) m
    ⟶⟨ correctJ p m (CPS.RJConsK (correctK x)) ⟩
      cpsP p
        (CPS.JCons (CPS.KLet (λ x₁ → cpsP (q' x₁) CPS.JVar CPS.MVar)) j) m
    ≡⟨ refl ⟩
      cpsP (DS.Let p q') j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RHandle₁ {p} {p'} {q} x) j m =
    begin
      cpsP (DS.Handle p q) j m
    ≡⟨ refl ⟩
      cpsP p CPS.JNil
        (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar)) m)
    ⟶⟨ correctP x CPS.JNil (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar)) m) ⟩
      cpsP p' CPS.JNil
        (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar)) m)
    ≡⟨ refl ⟩
      cpsP (DS.Handle p' q) j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.RHandle₂ {p} {q} {q'} x) j m =
    begin
      cpsP (DS.Handle p q) j m
    ≡⟨ refl ⟩
      cpsP p CPS.JNil
        (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar)) m)
    ⟶⟨ correctM p CPS.JNil (CPS.RMConsH (correctH x)) ⟩
      cpsP p CPS.JNil
        (CPS.MCons j (CPS.HFun (λ v r → cpsP (q' v r) CPS.JVar CPS.MVar))
         m)
    ≡⟨ refl ⟩
      cpsP (DS.Handle p q') j m
    ∎
    where open CPS.OneStepReasoning
  correctP (DS.ROp {v} {v'} x) j m = 
    begin
      cpsP (DS.Op v) j m
    ≡⟨ refl ⟩
      CPS.Op m (cpsV v) j
    ⟶⟨ CPS.ROpV (correctV x) ⟩
      CPS.Op m (cpsV v') j
    ≡⟨ refl ⟩
      cpsP (DS.Op v') j m
    ∎
    where open CPS.OneStepReasoning
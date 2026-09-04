-- right inverse
module Reflect2 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

import DS 
import CPS 
open import DS-CPS
open import CPS-DS
open import Extensionality

baseJ : {var : Set} → (μ : CPS.Mode) → CPS.cont[ var ] μ
baseJ CPS.current = CPS.JVar
baseJ CPS.stored  = CPS.JNil

interleaved mutual
  -- (ds P) : j : m = P 
  correctP  : {var : Set}
            → (p : CPS.term[ var ])
            → cpsP (dsP p) CPS.JVar CPS.MVar ≡ p
  -- lemmas
  -- (M♯♯[ J♭♭[ P ]]) : j : m = P : J : M
  correctJM : {μ : CPS.Mode}
            → {var : Set}
            → (m : CPS.mcont[ var ] μ)
            → (j : CPS.cont[ var ] μ)
            → (p : DS.comp[ var ])
            → cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) p)) CPS.JVar CPS.MVar
            ≡ cpsP p j m 
  -- (J♭♭[ P ]) : j : M = P : J : M 
  correctJ  : {μ : CPS.Mode}
            → {var : Set}
            → (m : CPS.mcont[ var ] μ)
            → (j : CPS.cont[ var ] μ)
            → (p : DS.comp[ var ])
            → cpsP (DS.plug (dsJ j) p) (baseJ μ) m 
            ≡ cpsP p j m
  -- cpsV (dsV V) = V
  correctV  : {var : Set}
            → (v : CPS.value[ var ])
            → cpsV (dsV v) ≡ v
  -- λx. λj. λm. (cps (ds P)) ≡ λx. λj. λm. P
  correctK  : {var : Set}
            → (q : var → CPS.term[ var ])
            → CPS.KLet (λ x → cpsP (dsP (q x)) CPS.JVar CPS.MVar)
            ≡ CPS.KLet q
  -- λv. λr. λj. λm. (cps (ds P)) ≡ λv. λr. λj. λm. P
  correctH  : {var : Set}
            → (h : CPS.handler[ var ])
            → CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar) 
            ≡ h
  
  correctP (CPS.Send j v m) = 
    begin
      cpsP (dsP (CPS.Send j v m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM m j (DS.Return (dsV v)) ⟩
      cpsP (DS.Return (dsV v)) j m
    ≡⟨ refl ⟩
      CPS.Send j (cpsV (dsV v)) m
    ≡⟨ cong (λ v' → CPS.Send j v' m) (correctV v) ⟩
      CPS.Send j v m
    ∎
  correctP (CPS.Add j v w m) = 
    begin
      cpsP (dsP (CPS.Add j v w m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM m j (DS.Add (dsV v) (dsV w)) ⟩
      cpsP (DS.Add (dsV v) (dsV w)) j m
    ≡⟨ refl ⟩
      CPS.Add j (cpsV (dsV v)) (cpsV (dsV w)) m
    ≡⟨ cong₂ (λ v' w' → CPS.Add j v' w' m) (correctV v) (correctV w) ⟩
      CPS.Add j v w m
    ∎
  correctP (CPS.App v w j m) = 
    begin
      cpsP (dsP (CPS.App v w j m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM m j (DS.App (dsV v) (dsV w)) ⟩
      cpsP (DS.App (dsV v) (dsV w)) j m
    ≡⟨ refl ⟩
      CPS.App (cpsV (dsV v)) (cpsV (dsV w)) j m
    ≡⟨ cong₂ (λ v' w' → CPS.App v' w' j m) (correctV v) (correctV w) ⟩
      CPS.App v w j m
    ∎
  correctP (CPS.Op m v j) = 
    begin
      cpsP (dsP (CPS.Op m v j)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))) CPS.JVar
        CPS.MVar
    ≡⟨ correctJM m j (DS.Op (dsV v)) ⟩
      cpsP (DS.Op (dsV v)) j m
    ≡⟨ refl ⟩
      CPS.Op m (cpsV (dsV v)) j
    ≡⟨ cong (λ v' → CPS.Op m v' j) (correctV v) ⟩
      CPS.Op m v j
    ∎

  correctJM CPS.MVar CPS.JVar p = refl
  correctJM CPS.MVar (CPS.JCons k j) p =
    begin
      cpsP (DS.plugM (dsM CPS.MVar) (DS.plug (dsJ (CPS.JCons k j)) p))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plug (dsJ (CPS.JCons k j)) p) CPS.JVar CPS.MVar
    ≡⟨ correctJ CPS.MVar (CPS.JCons k j) p ⟩
      cpsP p (CPS.JCons k j) CPS.MVar
    ∎
  correctJM (CPS.MCons j₀ h m₀) CPS.JNil p =
    begin
      cpsP
        (DS.plugM (dsM (CPS.MCons j₀ h m₀)) (DS.plug (dsJ CPS.JNil) p))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m₀) (DS.plug (dsJ j₀) (DS.Handle p (dsH h))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM m₀ j₀ (DS.Handle p (dsH h)) ⟩
      cpsP (DS.Handle p (dsH h)) j₀ m₀
    ≡⟨ refl ⟩
      cpsP p CPS.JNil (CPS.MCons j₀ h' m₀)
    ≡⟨ cong (λ h' → cpsP p CPS.JNil (CPS.MCons j₀ h' m₀)) (correctH h) ⟩
      cpsP p CPS.JNil (CPS.MCons j₀ h m₀)
    ∎
    where
      h' = CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)
  correctJM (CPS.MCons j₀ h m₀) (CPS.JCons k j) p =
    begin
      cpsP
        (DS.plugM (dsM (CPS.MCons j₀ h m₀))
         (DS.plug (dsJ (CPS.JCons k j)) p))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP
        (DS.plugM (dsM m₀)
         (DS.plug (dsJ j₀)
          (DS.Handle (DS.plug (dsJ (CPS.JCons k j)) p) (dsH h))))
        CPS.JVar CPS.MVar
    ≡⟨ correctJM m₀ j₀ (DS.Handle (DS.plug (dsJ (CPS.JCons k j)) p) (dsH h)) ⟩
      cpsP (DS.Handle (DS.plug (dsJ (CPS.JCons k j)) p) (dsH h)) j₀ m₀
    ≡⟨ refl ⟩
      cpsP (DS.plug (dsJ (CPS.JCons k j)) p) CPS.JNil
        (CPS.MCons j₀ h' m₀)
    ≡⟨ correctJ (CPS.MCons j₀ h' m₀) (CPS.JCons k j) p ⟩
      cpsP p (CPS.JCons k j) (CPS.MCons j₀ h' m₀)
    ≡⟨ cong (λ h' → cpsP p (CPS.JCons k j) (CPS.MCons j₀ h' m₀)) (correctH h) ⟩
      cpsP p (CPS.JCons k j) (CPS.MCons j₀ h m₀)
    ∎
    where 
      h' = CPS.HFun (λ v r → cpsP (dsH h v r) CPS.JVar CPS.MVar)


  correctJ m CPS.JVar p = 
      begin
        cpsP (DS.plug (dsJ CPS.JVar) p) (baseJ CPS.current) m
      ≡⟨ refl ⟩
        cpsP p CPS.JVar m
      ∎
  correctJ m CPS.JNil p = 
    begin
      cpsP (DS.plug (dsJ CPS.JNil) p) (baseJ CPS.stored) m
    ≡⟨ refl ⟩
      cpsP p CPS.JNil m
    ∎
  correctJ {μ} m (CPS.JCons (CPS.KLet q) j) p =
    begin
      cpsP (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j)) p) (baseJ μ) m
    ≡⟨ correctJ m j (DS.Let p (λ x → dsP (q x))) ⟩
      cpsP (DS.Let p (λ x → dsP (q x))) j m
    ≡⟨ refl ⟩
      cpsP p (CPS.JCons (CPS.KLet q') j) m
    ≡⟨ cong (λ q' → cpsP p (CPS.JCons q' j) m) (correctK q) ⟩
      cpsP p (CPS.JCons (CPS.KLet q) j) m
    ∎
    where
      q' = λ v → cpsP (dsP (q v)) CPS.JVar CPS.MVar

  correctV (CPS.Var x) = refl
  correctV (CPS.Num n) = refl
  correctV (CPS.Fun p) = 
    begin
      cpsV (dsV (CPS.Fun p))
    ≡⟨ refl ⟩
      CPS.Fun p'
    ≡⟨ cong CPS.Fun p'≡p ⟩
      CPS.Fun p
    ∎
    where 
      p' = λ x → cpsP (dsP (p x)) CPS.JVar CPS.MVar
      p'≡p = extensionality λ x → correctP (p x)
  
  correctK f =
    begin
      CPS.KLet f'
    ≡⟨ cong CPS.KLet f'≡f ⟩
      CPS.KLet f
    ∎
    where
      f' = λ x → cpsP (dsP (f x)) CPS.JVar CPS.MVar
      f'≡f = extensionality λ x → correctP (f x)
  
  correctH (CPS.HFun h) = 
    begin
      CPS.HFun h'
    ≡⟨ cong CPS.HFun h'≡h ⟩
      CPS.HFun h
    ∎
    where 
      h' = λ v r → cpsP (dsP (h v r)) CPS.JVar CPS.MVar
      h'≡h = extensionality λ x →
                extensionality λ y → correctP (h x y)
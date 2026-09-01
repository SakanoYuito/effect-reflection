module Reflect1 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

import DS 
import CPS 
open import DS-CPS
open import CPS-DS
open import Extensionality

-- lemma 
interleaved mutual
  correctV : {var : Set} 
           → (v : DS.value[ var ]) 
           → dsV (cpsV v) ≡ v
  correctP : {var : Set} 
           → (p : DS.comp[ var ]) 
           → (j : CPS.cont[ var ])
           → (m : CPS.mcont[ var ])
           → dsP (cpsP p j m)
           ≡ DS.plugM (dsM m) (DS.plug (dsJ j) p)

  correctV (DS.Var x) = refl
  correctV (DS.Num n) = refl
  correctV (DS.Fun p) = 
    begin
      dsV (cpsV (DS.Fun p))
    ≡⟨ refl ⟩
      DS.Fun p'
    ≡⟨ cong DS.Fun p'≡p ⟩
      DS.Fun p
    ∎
    where 
      p' = λ x → dsP (cpsP (p x) CPS.JVar CPS.MVar)
      p'≡p = extensionality λ x → correctP (p x) CPS.JVar CPS.MVar
  
  correctP (DS.Return v) j m = 
    begin
      dsP (cpsP (DS.Return v) j m)
    ≡⟨ refl ⟩ 
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV (cpsV v))))
    ≡⟨ cong (λ v' → DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return v'))) (correctV v) ⟩ 
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return v)) 
    ∎

  correctP (DS.App v w) j m =
    begin 
      dsP (cpsP (DS.App v w) j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV (cpsV v)) (dsV (cpsV w))))
    ≡⟨ cong₂ (λ v' w' → DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App v' w'))) (correctV v) (correctV w) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App v w))
    ∎ 

  correctP (DS.Add v w) j m =
    begin 
      dsP (cpsP (DS.Add v w) j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV (cpsV v)) (dsV (cpsV w))))
    ≡⟨ cong₂ (λ v' w' → DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add v' w'))) (correctV v) (correctV w) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add v w))
    ∎ 

  correctP (DS.Let p q) j m =
    begin
      dsP (cpsP (DS.Let p q) j m)
    ≡⟨ correctP p (CPS.JCons kq j) m ⟩
      DS.plugM (dsM m)
        (DS.plug (dsJ (CPS.JCons kq j)) p)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Let p q'))
    ≡⟨ cong (λ q'' →  DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Let p q''))) q'≡q ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Let p q))
    ∎
    where
      kq = CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)
      q' = λ x → dsP (cpsP (q x) CPS.JVar CPS.MVar)
      q'≡q = extensionality λ x → correctP (q x) CPS.JVar CPS.MVar

  correctP (DS.Handle p q) j m =
    begin
      dsP (cpsP (DS.Handle p q) j m)
    ≡⟨ correctP p CPS.JNil
      (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar)) m) ⟩
      DS.plugM
        (dsM
         (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar))
          m))
        (DS.plug (dsJ CPS.JNil) p)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Handle p q'))
    ≡⟨ cong (λ q'' → DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Handle p q''))) q'≡q ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Handle p q))
    ∎
    where
      q' = λ v r → dsP (cpsP (q v r) CPS.JVar CPS.MVar)
      q'≡q = extensionality λ v 
              → extensionality λ r 
                → correctP (q v r) CPS.JVar CPS.MVar

  correctP (DS.Op v) j m = 
    begin
      dsP (cpsP (DS.Op v) j m)
    ≡⟨ refl ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV (cpsV v))))
    ≡⟨ cong (λ w → DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op w))) (correctV v) ⟩
      DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op v))
    ∎

-- theorem
left-inverse : {var : Set} 
             → (p : DS.comp[ var ])
             → dsP (cpsP p CPS.JVar CPS.MVar) ≡ p 
left-inverse p = correctP p CPS.JVar CPS.MVar
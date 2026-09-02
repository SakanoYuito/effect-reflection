module Reflect2 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

import DS 
import CPS 
open import DS-CPS
open import CPS-DS
open import Extensionality

data End : Set where
  eOpen   : End 
  eClosed : End

data EndsAt {var : Set} : End → CPS.cont[ var ] → Set where
  at-var  : EndsAt eOpen CPS.JVar
  at-nil  : EndsAt eClosed CPS.JNil
  at-cons : {e : End}
          → {k : CPS.frame[ var ]}
          → {j : CPS.cont[ var ]}
          → EndsAt e j 
          → EndsAt e (CPS.JCons k j)

baseJ : {var : Set} → End → CPS.cont[ var ]
baseJ eOpen   = CPS.JVar
baseJ eClosed = CPS.JNil

interleaved mutual
  correctV  : {var : Set}
            → (v : CPS.value[ var ])
            → cpsV (dsV v) ≡ v
  correctP  : {var : Set}
            → (p : CPS.term[ var ])
            → cpsP (dsP p) CPS.JVar CPS.MVar ≡ p
  correctJ  : {var : Set}
            → {e : End}
            → {j : CPS.cont[ var ]}
            → EndsAt e j
            → (p : DS.comp[ var ])
            → (m : CPS.mcont[ var ])
            → cpsP (DS.plug (dsJ j) p) (baseJ e) m
            ≡ cpsP p j m
  correctJM : {var : Set}
            → (j : CPS.cont[ var ])
            → (m : CPS.mcont[ var ])
            → (p : DS.comp[ var ])
            → cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) p)) CPS.JVar CPS.MVar 
            ≡ cpsP p j m
  
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

  correctP (CPS.Send j v m) = 
    begin
      cpsP (dsP (CPS.Send j v m)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))) CPS.JVar CPS.MVar
    ≡⟨ {!  !} ⟩
      {!   !}
    ≡⟨ {!   !} ⟩
      {!   !}
    ≡⟨ {!   !} ⟩
      CPS.Send j v m
    ∎
  correctP (CPS.Add j v w m) = {!   !}
  correctP (CPS.App v w j m) = {!   !}
  correctP (CPS.Op m v j) = {!   !}

  correctJM CPS.JVar CPS.MVar p = 
    begin
      -- (m♯♯[ j♭♭[ p ] ]) : j : m 
      cpsP (DS.plugM (dsM CPS.MVar) (DS.plug (dsJ CPS.JVar) p)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- p : j : m
      cpsP p CPS.JVar CPS.MVar
    ∎
  correctJM CPS.JVar CPS.MNil p = 
    begin
      -- ( ()♯♯[ j♭♭[ p ]] ) : j : m 
      cpsP (DS.plugM (dsM CPS.MNil) (DS.plug (dsJ CPS.JVar) p)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- p : j : m
      cpsP p CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : j : ()
      cpsP p CPS.JVar CPS.MNil
    ∎
  correctJM CPS.JVar (CPS.MCons j h m) p = 
    begin
      -- ( (<j0, h>::m)♯♯[ j♭♭[ p ]] ) : j : m 
      cpsP (DS.plugM (dsM (CPS.MCons j h m)) (DS.plug (dsJ CPS.JVar) p)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- ( m♯♯[ j0♭♭[ handle p with h‡ ]] ) : j : m
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Handle p (dsH h)))) CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : j : (<j0, h>::m)
      cpsP p CPS.JVar (CPS.MCons j h m)
    ∎
  correctJM CPS.JNil CPS.MVar p = 
    begin
      -- (m♯♯[ ()♭♭[ p ]]) : j : m 
      cpsP (DS.plugM (dsM CPS.MVar) (DS.plug (dsJ CPS.JNil) p)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- p : j : m 
      cpsP p CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : () : m
      cpsP p CPS.JNil CPS.MVar
    ∎
  correctJM CPS.JNil CPS.MNil p = 
    begin
      -- ( ()♯♯[ ()♭♭[ p ]] ) : j : m
      cpsP (DS.plugM (dsM CPS.MNil) (DS.plug (dsJ CPS.JNil) p)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- p : j : m 
      cpsP p CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : () : ()
      cpsP p CPS.JNil CPS.MNil
    ∎
  correctJM CPS.JNil (CPS.MCons j h m) p = 
    begin
      -- ( (<j, h>::m)♯♯[ ()♭♭[ p ]] ) : j : m 
      cpsP (DS.plugM (dsM (CPS.MCons j h m)) (DS.plug (dsJ CPS.JNil) p)) CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- ( m♯♯[ j♭♭ [handle p with h‡]] ) : j : m
      cpsP (DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Handle p (dsH h)))) CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : () : (<j, h> :: m)
      cpsP p CPS.JNil (CPS.MCons j h m)
    ∎
  correctJM (CPS.JCons (CPS.KLet q) j) CPS.MVar p = 
    begin
      -- ( m♯♯[ (k :: j')♭♭[ p ]] ) : j : m
      cpsP
        (DS.plugM (dsM CPS.MVar)
         (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j)) p))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- (j'♭♭[ let x = p in q♯ ]) : j : m 
      cpsP (DS.plug (dsJ j) (DS.Let p (λ x → dsP (q x)))) CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : (k :: j') : m
      cpsP p (CPS.JCons (CPS.KLet q) j) CPS.MVar
    ∎
  correctJM (CPS.JCons (CPS.KLet q) j) CPS.MNil p = 
    begin
      -- ()♯[ (k :: j')♭♭[ p ]] : j : m 
      cpsP
        (DS.plugM (dsM CPS.MNil)
         (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j)) p))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- j♭♭[ let x = p in q♯ ] : j : m 
      cpsP (DS.plug (dsJ j) (DS.Let p (λ x → dsP (q x)))) CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p : (k :: j) : () 
      cpsP p (CPS.JCons (CPS.KLet q) j) CPS.MNil
    ∎
  correctJM (CPS.JCons (CPS.KLet q) j) (CPS.MCons j0 h m0) p = 
    begin
      -- (<j0, h>::m0)♯♯[ (k :: j)♭♭[ p ]] : j' : m'
      cpsP
        (DS.plugM (dsM (CPS.MCons j0 h m0))
         (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j)) p))
        CPS.JVar CPS.MVar
    ≡⟨ refl ⟩
      -- m0♯♯[ j0♭♭[ handle j♭[ let x = p in q♯ ] with h‡ ]] : j' : m' 
      cpsP
        (DS.plugM (dsM m0)
         (DS.plug (dsJ j0)
          (DS.Handle (DS.plug (dsJ j) (DS.Let p (λ x → dsP (q x))))
           (dsH h))))
        CPS.JVar CPS.MVar
    ≡⟨ {!   !} ⟩
      -- p :: (k :: j) : (<j0. h>::m0)
      cpsP p (CPS.JCons (CPS.KLet q) j) (CPS.MCons j0 h m0)
    ∎

  correctJ at-var p m = 
    begin
      -- (j'♭♭[p]) : j : m  
      cpsP (DS.plug (dsJ CPS.JVar) p) (baseJ eOpen) m
    ≡⟨ refl ⟩
      -- p : j : m
      cpsP p CPS.JVar m
    ∎
  correctJ at-nil p m =
    begin
      -- ( ()♭♭[p] ) : () : m
      cpsP (DS.plug (dsJ CPS.JNil) p) (baseJ eClosed) m
    ≡⟨ refl ⟩
      -- p : () : m
      cpsP p CPS.JNil m
    ∎
  correctJ (at-cons {e} {CPS.KLet q} {j} es) p m =
    begin
      -- ( (k :: j)♭♭[p] ) : jₑ : m
      cpsP (DS.plug (dsJ (CPS.JCons (CPS.KLet q) j)) p) (baseJ e) m
    ≡⟨ refl ⟩
      -- ( j♭♭[ let x = p in q♯ ] ) : jₑ : m
      cpsP (DS.plug (dsJ j) (DS.Let p (λ x → dsP (q x)))) (baseJ e) m
    ≡⟨ correctJ es (DS.Let p (λ x → dsP (q x))) m ⟩
      -- (let x = p in q♯) : j : m
      cpsP (DS.Let p (λ x → dsP (q x))) j m
    ≡⟨ refl ⟩
      -- p : (Kq' : j) : m
      --   where Kq' = λvjm. ((q v)♯) : j : m
      cpsP p (CPS.JCons (CPS.KLet q') j) m
    ≡⟨ cong (λ q' → cpsP p (CPS.JCons (CPS.KLet q') j) m) q'≡q ⟩
      -- p : (Kq : j) : m
      --  where Kq = q j m
      cpsP p (CPS.JCons (CPS.KLet q) j) m
    ∎
    where
      q' = λ v → cpsP (dsP (q v)) CPS.JVar CPS.MVar 
      q'≡q = extensionality λ x → correctP (q x)
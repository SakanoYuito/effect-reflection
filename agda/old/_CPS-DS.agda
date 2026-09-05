module CPS-DS where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DS
import CPS

-- DS translation
interleaved mutual
  dsV : {var : Set} → CPS.value[ var ] → DS.value[ var ]
  dsP : {var : Set} → CPS.term[ var ] → DS.comp[ var ]
  dsK : {var : Set} → CPS.frame[ var ] → DS.PCtx[ var ]
  dsJ : {var : Set} → CPS.cont[ var ] → DS.PCtx[ var ]
  dsM : {var : Set} → CPS.mcont[ var ] → DS.MCtx[ var ]
  dsH : {var : Set} → CPS.handler[ var ] → (var → var → DS.comp[ var ])

  -- value 
  --- x♮ = x 
  dsV (CPS.Var x) = DS.Var x
  --- n♮ = n 
  dsV (CPS.Num n) = DS.Num n
  --- (λx. λj. λm. P)♮ = λx. P♯
  dsV (CPS.Fun p) = DS.Fun (λ x → dsP (p x))

  -- term 
  --- (J V M)♯ = M♯♯[ J♭♭[ return V♮ ] ]
  dsP (CPS.Send j v m) = DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Return (dsV v)))
  --- (J (V + W) M)♯ = M♯♯[ J♭♭[ V♮ + W♮ ] ] 
  dsP (CPS.Add j v w m) = DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Add (dsV v) (dsV w)))
  --- (V W J M)♯ = M♯♯[ J♭♭[ V♮ W♮ ] ]
  dsP (CPS.App v w j m) = DS.plugM (dsM m) (DS.plug (dsJ j) (DS.App (dsV v) (dsV w)))
  --- (M @ V J)♯ = M♯♯[ J♭♭[ op V♮ ] ]
  dsP (CPS.Op m v j) = DS.plugM (dsM m) (DS.plug (dsJ j) (DS.Op (dsV v)))

  -- cont. frame 
  --- (λx. λj. λm. P)♭ = (let x = [] in P#)
  dsK (CPS.KLet p) = DS.FLet DS.FHole (λ x → dsP (p x))

  -- cont 
  --- j♭♭ = [] 
  dsJ CPS.JVar = DS.FHole
  --- ()♭♭ = [] 
  dsJ CPS.JNil = DS.FHole
  --- (K :: J)♭♭ = J♭♭[ K♭ ]
  dsJ (CPS.JCons (CPS.KLet p) j) = DS.FLet (dsJ j) (λ x → dsP (p x))

  -- mcont 
  --- m♯♯ = [] 
  dsM CPS.MVar = DS.MHole
  --- ()♯♯ = [] 
  dsM CPS.MNil = DS.MHole
  --- (<J, H> :: M)♯♯ = M♯♯[ J♭♭ [handle [] with H‡] ] 
  dsM (CPS.MCons j h m) = DS.MHandle (dsM m) (dsJ j) (dsH h) 

  -- handler 
  --- (λv. λr. λj. λm. P)‡ = v, r → P#
  dsH (CPS.HFun h) = λ v r → dsP (h v r)

ds-val1 : {var : Set} → dsV (CPS.val1 {var}) ≡ DS.val1
ds-val1 = refl

ds-term1 : {var : Set} → dsP (CPS.term1 {var}) ≡ DS.comp1 
ds-term1 = refl

ds-term2 : {var : Set} → dsP (CPS.term2 {var}) ≡ DS.comp2
ds-term2 = refl
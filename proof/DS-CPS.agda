module DS-CPS where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DS
import CPS

-- CPS translation

interleaved mutual
  cpsV : {var : Set} → DS.value[ var ] → CPS.value[ var ]
  cpsP : {var : Set} → DS.comp[ var ] → CPS.cont[ var ] → CPS.mcont[ var ] → CPS.term[ var ]

  -- value translation V†
  --- x† = x
  cpsV (DS.Var x) = CPS.Var x
  --- n† = n
  cpsV (DS.Num n) = CPS.Num n
  --- (λx. P)† = λx. λj. λm. (P : j : m)
  cpsV (DS.Fun f) = CPS.Fun (λ x → cpsP (f x) CPS.JVar CPS.MVar)

  -- computation translation (P : J : M)
  --- return V : J : M = J V† M
  cpsP (DS.Return v)   j m = CPS.Send j (cpsV v) m
  --- V W : J : M = V† W† J M
  cpsP (DS.App v w)    j m = CPS.App (cpsV v) (cpsV w) j m
  --- V + W : J : M = J (V† + W†) M
  cpsP (DS.Add v w)    j m = CPS.Add j (cpsV v) (cpsV w) m
  --- (let x = P in Q) : J : M = P : (Kq :: J) : M 
  ---   where Kq = λv. λj. λm. (Q[v/x] : j : m)
  cpsP (DS.Let p q)    j m = cpsP p
                                  (CPS.JCons (CPS.KLet (λ v → cpsP (q v) CPS.JVar CPS.MVar)) j) 
                                  m
  --- (handle P with x, k → Q) : J : M = P : () : (<J, H> :: M)
  ---   where H = λv. λr. λj. λm. (P[v/x, r/k] : j : m)
  cpsP (DS.Handle p q) j m = cpsP p 
                                  CPS.JNil
                                  (CPS.MCons j (CPS.HFun (λ v r → cpsP (q v r) CPS.JVar CPS.MVar)) m)
  --- op V : J : M = M @ V† J
  cpsP (DS.Op v)       j m = CPS.Op m (cpsV v) j


cps-val1 : {var : Set} → cpsV (DS.val1 {var}) ≡ CPS.val1
cps-val1 = refl

cps-comp1 : {var : Set} → cpsP (DS.comp1 {var}) CPS.JVar CPS.MVar ≡ CPS.term1
cps-comp1 = refl

cps-comp2 : {var : Set} → cpsP (DS.comp2 {var}) CPS.JVar CPS.MVar ≡ CPS.term2
cps-comp2 = refl

module TranslationExamples where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DS
import CPS
import DS-CPS as C
import CPS-DS as D

left-comp1 : {var : Set} →
  D.dsP (C.cpsP (DS.comp1 {var}) CPS.JVar CPS.MVar)
  ≡ DS.comp1
left-comp1 = refl

left-comp2 : {var : Set} →
  D.dsP (C.cpsP (DS.comp2 {var}) CPS.JVar CPS.MVar)
  ≡ DS.comp2
left-comp2 = refl

right-term1 : {var : Set} →
  C.cpsP (D.dsP (CPS.term1 {var})) CPS.JVar CPS.MVar
  ≡ CPS.term1
right-term1 = refl

right-term2 : {var : Set} →
  C.cpsP (D.dsP (CPS.term2 {var})) CPS.JVar CPS.MVar
  ≡ CPS.term2
right-term2 = refl
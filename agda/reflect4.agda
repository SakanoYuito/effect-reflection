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

interleaved mutual 
  -- P → Q implies P♯ → Q♯
  correctP : {var : Set}
             -> {!   !}
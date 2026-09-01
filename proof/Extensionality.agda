module Extensionality where

open import Level using (Level)
open import Axiom.Extensionality.Propositional

postulate
  extensionality : {a b : Level} → Extensionality a b
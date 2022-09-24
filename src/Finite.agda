
-- This module implements a simple universe of finite sets which is
-- more convenient to work with than Data.Fin
module Finite where

import Data.Empty as Empty
import Data.Product as Prod
import Data.Sum as Sum
import Data.Unit as Unit

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

data Finite : Set
[_] : Finite → Set

-- The finite sets we will consider are the empty set, the singleton set,
-- disjoint unions of finite sets, and products of finite sets.
data Finite where
  ⊥ ⊤ : Finite
  _+_ _×_ : (s t : Finite) → Finite

-- [_] takes the above descriptions of finite sets to their type of values.
[ ⊥ ] = Empty.⊥
[ ⊤ ] = Unit.⊤
[ s + t ] = [ s ] Sum.⊎ [ t ]
[ s × t ] = [ s ] Prod.× [ t ]

-- This provides some of the functions necessary for working with values of
-- the above finite sets.
open Empty using (⊥-elim) public
open Prod using (_,_; proj₁; proj₂) public
open Sum using (inj₁; inj₂) public

-- It is possible to decide equality of elements of finite sets.
_≟_ : {S : Finite} → (x y : [ S ]) → Dec (x ≡ y)
_≟_ {⊤} x y = yes refl
_≟_ {S + T} (inj₁ x) (inj₁ y) with x ≟ y
... | yes refl = yes refl
... | no x≠y = no λ{ refl → x≠y refl }
_≟_ {S + T} (inj₂ x) (inj₂ y) with x ≟ y
... | yes refl = yes refl
... | no x≠y = no λ{ refl → x≠y refl }
_≟_ {S + T} (inj₁ _) (inj₂ _) = no λ()
_≟_ {S + T} (inj₂ _) (inj₁ _) = no λ()
_≟_ {S × T} (w , y) (x , z) with w ≟ x | y ≟ z
... | no w≠x | _ = no (w≠x ∘ cong proj₁)
... | _ | no y≠z = no (y≠z ∘ cong proj₂)
... | yes refl | yes refl = yes refl

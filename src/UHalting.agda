
open import Finite hiding (_×_)

import Data.Empty as Empty
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Turing.Machine
open Tp

-- For the below building blocks, we only care about 'equivalence' of
-- machines with respect halting/looping behavior, and the final value
-- focused upon halting.
module UHalting
  -- Suppose we have a scheme for representing Turing machines as
  -- inputs to machines...
  (enc : TM -> Input)
  -- ... and an encoding for a pair of inputs.
  (pair : Input -> Input -> Input)
  -- Suppose we have a way of modifying a Turing machine to access its
  -- own encoding ...
  (μ : TM -> TM)
  -- ... such that executing `μ tm` on `i` is equivalent to executing
  -- `tm` on `pair i (enc (μ tm))`.
  (μ-↓ : ∀{tm i s}
       → execute tm (pair i (enc (μ tm))) ↓ s
       → Σ[ t ∈ _ ]
           execute (μ tm) i ↓ t
         × focus s ≡ focus t)
  (μ-↑ : ∀{tm i}
       → execute tm (pair i (enc (μ tm))) ↑
       → execute (μ tm) i ↑)
  -- Suppose we have a way of modifying a Turing machine to first copy
  -- part of the input...
  (Δ : TM -> TM)
  -- ... such that executing `Δ tm` on `pair i j` is equivalent to
  -- executing `tm` on `pair i (pair j i)`.
  (Δ-↓ : ∀{tm s i j}
       → execute tm (pair i (pair j i)) ↓ s
       → Σ[ t ∈ _ ]
           execute (Δ tm) (pair i j) ↓ t
         × focus s ≡ focus t)
  (Δ-↑ : ∀{tm i j}
       → execute tm (pair i (pair j i)) ↑
       → execute (Δ tm) (pair i j) ↑)
  -- Suppose we have a universal Turing machine ...
  (U : TM)
  -- ... such that executing U on `pair tm i` is equivalent to
  -- executing `tm` on `i`
  (U-↓ : ∀{tm i s}
       → execute tm i ↓ s
       → Σ[ t ∈ _ ]
           execute U (pair (enc tm) i) ↓ t
         × focus s ≡ focus t)
  (U-↑ : ∀{tm i} → execute tm i ↑ -> execute U (pair (enc tm) i) ↑)
  where

-- A tape `tp` predicts the behavior of a machine `tm` and input `i`
-- if ...
--   when the focused value of the tape is 0ₛ, `execute tm i` loops
--   when the focused value of the tape is 1ₛ, `execute tm i` halts
--   the focued value of the tape is not blank
Predicts : TM -> Input -> Tape -> Set
Predicts tm i tp with focus tp
... | 0ₛ = execute tm i ↑
... | 1ₛ = Σ[ s ∈ _ ] execute tm i ↓ s
... | ∙  = Empty.⊥

-- For H to decide halting, evaluating it on a machine-input pair must
-- always halt in a tape that predicts the behavior of that pair.
Decides-Halting : TM -> Set
Decides-Halting H
  = ∀ tm i
  → Σ[ tp ∈ Tape ]
      execute H (pair (enc tm) i) ↓ tp
    × Predicts tm i tp

-- First we construct a new machine ¬U by adding one additional state
-- to U. The new state will trivially loop to itself forever. The
-- rules for the new machine on the old states will be copied from U,
-- except any rules that halt. For the latter, if the final tape would
-- focus on 1ₛ, we instead transition to the looping state.
--
-- Visually, you can imagine we are adding cases like:
--
--                1ₛ
--        ---> h ---> new --
--       /           ^  ^   \
--  ... -           /    \__/
--      \---> h'---/ 1ₛ
--
-- This implements the translations of U's rules to ¬U's rules.
upgrade
  : [ states U ]
  → (Symbol -> Action (states U))
  → (Symbol -> Action (states U + ⊤))
upgrade s f sy with f sy
... | next d sy st = next d sy (inj₁ st)
-- if we were going to halt indicating 'yes', go to the new loop
upgrade s f 1ₛ | halt = next ⇓ 1ₛ (inj₂ _)
-- otherwise just halt
upgrade s f  _ | halt = halt

-- ¬U is the new Turing machine described above.
¬U : TM
-- Adjoin a new state to U's states
¬U .states = states U + ⊤
-- Use U's table for the states embedded from U's state set, except
-- for halting states.
¬U .table (inj₁ s) = upgrade s (U .table s)
-- The new state should just loop to itself
¬U .table (inj₂ _) sy = next ⇓ sy (inj₂ _)
-- Just use U's starting state
¬U .start = inj₁ (start U)

-- The new state definitely loops
loop-lemma : ∀{tp} → unfold ¬U tp (inj₂ _) ↑
loop-lemma .force = steps loop-lemma

-- If U executed with some input `i` halts with 0ₛ focused, then ¬U
-- with that input halts.
no-lemma : ∀ i tp → focus tp ≡ 0ₛ -> execute U i ↓ tp -> execute ¬U i ↓ tp
no-lemma i tp hz = sub where
  sub : ∀{tp₀ s} → unfold U tp₀ s ↓ tp -> unfold ¬U tp₀ (inj₁ s) ↓ tp
  sub {tp₀} {s} h with table U s (tp₀ .focus)
  sub (steps tr) | next d sy st = steps (sub tr)
  sub (finish _) | halt rewrite hz = finish tp

-- If U executed with input `i` halts with 1ₛ focused, then ¬U loops
-- on that input.
yes-lemma : ∀ i tp → focus tp ≡ 1ₛ -> execute U i ↓ tp -> execute ¬U i ↑
yes-lemma i tp ho = sub where
  sub : ∀{tp₀ s} → unfold U tp₀ s ↓ tp -> unfold ¬U tp₀ (inj₁ s) ↑
  sub {tp₀} {s} h .force with table U s (tp₀ .focus)
  sub (steps tr) .force | next d sy st = steps (sub tr)
  sub (finish _) .force | halt rewrite ho = steps loop-lemma

-- Let Û be the machine that first pairs the tape contents with its
-- own encoding, then applies the Δ operation to copy the original
-- input, then evalutes ¬U on the compound input.
--
--   Û(M) = Δ¬U(M,Û) = ¬U(M,(Û,M))
Û = μ (Δ ¬U)

module _ (H : TM) (tp : Tape) where
  -- The compound input that results from Û(H)
  inp : Input
  inp = pair (enc H) (pair (enc Û) (enc H))

  -- Suppose H evaluated with `pair (enc Û) (enc H)` as input halts
  -- with 1ₛ focused. Then Û evaluated with (enc H) as input loops.
  μ-yes-lemma
    : focus tp ≡ 1ₛ
    → execute H (pair (enc Û) (enc H)) ↓ tp
    → execute Û (enc H) ↑
  μ-yes-lemma ho tr with U-↓ tr
  ... | tp' , tr' , refl = μ-↑ (Δ-↑ (yes-lemma inp tp' ho tr'))

  -- Suppose H evaluated with `pair (enc Û) (enc H)` as input halts
  -- with 0ₛ focused. Then Û evaluated with (enc H) as input halts.
  μ-no-lemma
    : focus tp ≡ 0ₛ
    → execute H (pair (enc Û) (enc H)) ↓ tp
    → Σ[ tp' ∈ _ ] execute Û (enc H) ↓ tp'
  μ-no-lemma hz tr with U-↓ tr
  ... | tp₁ , tr₁ , refl with Δ-↓ (no-lemma inp tp₁ hz tr₁)
  ... | tp₂ , tr₂ , refl with μ-↓ tr₂
  ... | tp₃ , tr₃ , refl = tp₃ , tr₃

-- We can now use Û to show that no machine H can decide halting,
-- because its behavior at Û and H would be contradictory.
doesn't-decide-halting : ∀ H → ¬ Decides-Halting H
doesn't-decide-halting H dh with dh Û (enc H)
... | tp , tr , pred with focus tp in e
-- In this case, H has indicated that Û run with `enc H` as input
-- loops. But by μ-no-lemma it actually halts. So our assumption that
-- H correctly predicts looping is faulty.
... | 0ₛ = halt-loop (proj₂ (μ-no-lemma H tp e tr)) pred
-- In this case, H has indicated that Û run with `enc H` as input
-- halts. But by μ-yes-lemma it actually loops. So our assumption that
-- H correctly predicts halting is faulty.
... | 1ₛ = halt-loop (proj₂ pred) (μ-yes-lemma H tp e tr)

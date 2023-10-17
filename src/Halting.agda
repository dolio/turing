
open import Finite hiding (_×_)

open import Data.Maybe
open import Data.Product
open import Data.Sum using (_⊎_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Turing.Machine
open St

module Halting
  -- Suppose we have a scheme for representing Turing machines as
  -- inputs to machines...
  (enc : TM → Input)
  -- ... and an encoding for a pair of inputs.
  (pair : Input → Input → Input)
  -- Suppose we have a way of modifying a Turing machine to first copy
  -- input...
  (Δ : TM → TM)
  -- ... such that executing `Δ tm` on `i` is equivalent (halting-wise)
  -- to executing `tm` on `pair i i`.
  (Δ-↓ : ∀{tm s i}
       → execute tm (pair i i) ↓ s → Σ[ t ∈ _ ] execute (Δ tm) i ↓ t)
  (Δ-↑ : ∀{tm i} → execute tm (pair i i) ↑ → execute (Δ tm) i ↑)
  -- Suppose we have a hypothetical halting decider that uses the above
  -- encoding scheme.
  (H : TM)
  -- It has two Accept/reject states that indicate whether its encoded
  -- input halts.
  (y n : [ states H ])
  -- It must be the case that n and y are distinct states, so we can
  -- interpret the decision the machine has made.
  (n≠y : n ≢ y)
  where

-- H indicates halting if
--  for all Turing machines `tm`
--  and all inputs `i`
--    if executing H with input `pair (enc tm) i` halts in state `y`
--    then executing `tm` with input `i` halts (in some state)
Indicates-Halting : Set
Indicates-Halting =
  ∀{tm : TM} {i : Input}
    → execute H (pair (enc tm) i) ↓ y
    → Σ[ s ∈ _ ] execute tm i ↓ s

-- H indicates looping if...
--  for all Turing machines `tm`
--  and all inputs `i`
--    if executing H with input `pair (enc tm) i` halts in state `n`
--    then executing `tm` with input `i` loops forever
Indicates-Looping : Set
Indicates-Looping =
  ∀{tm : TM} {i : Input}
    → execute H (pair (enc tm) i) ↓ n
    → execute tm i ↑

-- H realizes a total function if
--   for all Turing machines `tm`
--   and all inputs `i`
--     executing H with input `pair (enc tm) i` always halts in either
--     state `y` or state `n`
Total : Set
Total =
  ∀(tm : TM) (i : Input)
    → execute H (pair (enc tm) i) ↓ n
    ⊎ execute H (pair (enc tm) i) ↓ y

-- For H to decide halting, it must meet all three of these criteria.
Decides-Halting : Set
Decides-Halting = Total × Indicates-Halting × Indicates-Looping

-- First we construct a new machine H' by adding one additional state to
-- H. The new state will trivially loop to itself forever. The rules for
-- the new machine on the old states will be copied from H, except the
-- rule to halt in state `y` will be changed to transition to the new
-- looping state.
--
-- Visually, you can imagine this is like:
--
--        ---> y ---> new --
--       /              ^   \
--  ... -                \__/
--       \---> n

-- This implements the translation of H's rules to the new state set.
upgrade
  : [ states H ]
  → (Symbol → Action (states H))
  → (Symbol → Action (states H + ⊤))
upgrade s f sy with f sy
... | next d sy st = next d sy (inj₁ st)
... | halt with s ≟ y -- if the halting rule is for the 'yes' state
... | yes _ = next ⇓ sy (inj₂ _) -- go to the new looping state
... | no  _ = halt
  
-- H' is the new Turing machine described above.
H' : TM
-- Adjoin a new state to H's states
H' .states = states H + ⊤
-- Use H's table for the states embedded from H's state set, except
-- with the one modification
H' .table (inj₁ s) = upgrade s (H .table s)
-- The new state should just loop to itself
H' .table (inj₂ _) sy = next ⇓ sy (inj₂ _)
-- Use H's starting state
H' .start = inj₁ (start H)

-- The above new state definitely loops (for all tapes)
loop-lemma : ∀{tp} → unfold H' tp (inj₂ _) ↑
loop-lemma .force = steps loop-lemma

-- If H executed with input `i` terminates in the `n` state, then
-- H' executed with input `i` terminates in the `inj₁ n` state
no-lemma : ∀ i → execute H i ↓ n → execute H' i ↓ (inj₁ n)
no-lemma i = sub where
  sub : ∀{tp s} → unfold H tp s ↓ n → unfold H' tp (inj₁ s) ↓ inj₁ n
  sub {tp} {s} h with table H s (tp .focus)
  sub (steps tr) | next d sy st = steps (sub tr)
  sub (finish _) | halt with n ≟ y
  sub (finish _) | halt | no _ = finish (inj₁ n)
  sub (finish _) | halt | yes n=y = ⊥-elim (n≠y n=y)

-- If H executed with input `i` terminates in the `y` state, then
-- H' executed with input `i` loops forever.
yes-lemma : ∀ i → execute H i ↓ y → execute H' i ↑
yes-lemma i = sub where
  sub : ∀{tp s} → unfold H tp s ↓ y → unfold H' tp (inj₁ s) ↑
  sub {tp} {s} h .force with table H s (tp .focus)
  sub (steps tr) .force | next d sy st = steps (sub tr)
  sub (finish .y) .force | halt with y ≟ y
  sub (finish .y) .force | halt | yes refl = steps loop-lemma
  sub (finish .y) .force | halt | no y≠y = ⊥-elim (y≠y refl)

-- Let Ĥ be the machine that first duplicates its input, then runs H'.
-- This is the problematic Turing machine that confounds H.
Ĥ = Δ H'

-- If H indicates that Ĥ executed with input `enc Ĥ` halts, then
-- Ĥ executed with input `enc Ĥ` actually loops
Δ-yes-lemma : execute H (pair (enc Ĥ) (enc Ĥ)) ↓ y → execute Ĥ (enc Ĥ) ↑
Δ-yes-lemma hy = Δ-↑ (yes-lemma (pair (enc Ĥ) (enc Ĥ)) hy)

-- If H indicates that Ĥ run with input `enc Ĥ` loops, then
-- Ĥ executed with input `enc Ĥ` actually halts in some state.
Δ-no-lemma
  : execute H (pair (enc Ĥ) (enc Ĥ)) ↓ n
  → Σ[ t ∈ _ ] execute Ĥ (enc Ĥ) ↓ t
Δ-no-lemma hn = Δ-↓ (no-lemma (pair (enc Ĥ) (enc Ĥ)) hn)

-- H fails to decide halting
doesn't-decide-halting : ¬ Decides-Halting
doesn't-decide-halting (tot , ihalt , iloop) with tot Ĥ (enc Ĥ)
-- In this case, H has indicated that Ĥ run with `enc Ĥ` as input loops.
-- But by Δ-no-lemma, it actually halts. So our assumption that H
-- correctly indicates looping is faulty.
... | inj₁ dec-loop =
  halt-loop (Δ-no-lemma dec-loop .proj₂) (iloop dec-loop)
-- In this case, H has indicated that Ĥ run with `enc Ĥ` as input halts.
-- But by Δ-yes-lemma, it actually loops. So, our assumption that H
-- correctly indicates halting is faulty.
... | inj₂ dec-halt =
  halt-loop (ihalt dec-halt .proj₂) (Δ-yes-lemma dec-halt)

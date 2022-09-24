
module Turing.Machine where

open import Data.Maybe
open import Data.Product

open import Finite

open import Relation.Nullary

variable
  S T : Finite

-- Each instruction of a Turing machine can move the head left, right
-- or leave it in place.
data Direction : Set where
  ⇐ ⇓ ⇒ : Direction

-- These Turing machines use a binary alphabet for input.
data Bit : Set where
  0ₛ 1ₛ : Bit

-- Input lists for a machine
data Input : Set where
  [] : Input
  _∷_ : Bit → Input → Input

-- The tape symbols contain an additional "blank" symbol beyond the two
-- bit symbols.
data Symbol : Set where
  0ₛ 1ₛ ∙ : Symbol

-- The actions a machine may take in each state. They may either:
--   - halt, with the final state/tape indicating some result
--   - take a sequence of actions to reach the next state
--     * first, replace the current symbol with a new symbol
--     * then shift the tape by the given direction
--     * then go to the indicated state
data Action S : Set where
  halt : Action S
  next : (d : Direction) → (sy : Symbol) → (st : [ S ]) → Action S

-- A "table" is a mapping from finite states and symbols to actions
Table : Finite → Set
Table S = [ S ] → Symbol → Action S

-- A Turing machine has ...
record TM : Set where
  field
    -- A finite set of states
    states : Finite
    -- A table of rules for the states
    table : Table states
    -- A start state
    start : [ states ]
open TM public

-- Backwards lists of symbols for representing the tape
data Pre : Set where
  [] : Pre
  _∷_ : Pre → Symbol → Pre

-- Forwards lists of symbols for representing the tape
data Post : Set where
  [] : Post
  _∷_ : Symbol → Post → Post

-- A tape is a focused symbol with lists of symbols that occur before
-- and after the focused symbol.
record Tape : Set where
  constructor _〈_〉_
  field
    pre : Pre
    focus : Symbol
    post : Post

open Tape public

-- The overall machine state for a Turing machine. Both a current
-- automaton state and a tape.
record State (S : Finite) : Set where
  constructor _,_
  field
    auto : [ S ]
    tape : Tape
open State

-- Shifts a tape in a given direction.
--
-- A tape can be extended arbitrarily in either direction. Shifting into
-- an empty pre/post list simply focuses a new "blank" symbol.
shift : Tape → Direction → Tape
shift tp                           ⇓ = tp
shift ([]        〈 f 〉 post)       ⇐ = []  〈 ∙ 〉 (f ∷ post)
shift ((pre ∷ x) 〈 f 〉 post)       ⇐ = pre 〈 x 〉 (f ∷ post)
shift (pre       〈 f 〉 [])         ⇒ = (pre ∷ f) 〈 ∙ 〉 []
shift (pre       〈 f 〉 (x ∷ post)) ⇒ = (pre ∷ f) 〈 x 〉 post

-- Initializes a tape to a given input. The tape is initially focused
-- on the first symbol of the input, if possible.
initialize : Input → Tape
initialize []       = [] 〈 ∙ 〉 []
initialize (b ∷ bs) = [] 〈 b→s b 〉 i→p bs where
  b→s : Bit → Symbol
  b→s 0ₛ = 0ₛ
  b→s 1ₛ = 1ₛ

  i→p : Input → Post
  i→p []       = []
  i→p (b ∷ bs) = b→s b ∷ i→p bs

-- Calculates the following state given a table and a machine state.
-- If the prescribed action is to halt, then `nothing` is returned.
step : Table S → Tape → [ S ] → Maybe (State S)
step tb (pre 〈 fo 〉 post) st with tb st fo
... | halt = nothing
... | next d sy nx = just (nx , shift (pre 〈 sy 〉 post) d)

-- A trace is a potentially infinite sequence of states that a machine
-- may pass through while executing.
record Trace S : Set where
  coinductive
  field
    head : [ S ]
    tail : Maybe (Trace S)
open Trace public

-- Generates the trace of a TM from a given tape and state
unfold : (tm : TM) → Tape → [ states tm ] → Trace (states tm)
unfold tm tp s .head = s
unfold tm tp s .tail with step (table tm) tp s
... | nothing = nothing
... | just (s , tp) = just (unfold tm tp s)

-- Given a Turing machine and an input, get the trace that results from
-- executing it.
execute : (tm : TM) → Input → Trace (states tm)
execute tm i = unfold tm (initialize i) (start tm)

-- Values of `tr ↓ s` are proofs that the Trace tr has a final state `s`
_↓_ : Trace S → [ S ] → Set
data Halts {S} : [ S ] → Maybe (Trace S) → [ S ] → Set where
  finish : ∀ s → Halts s nothing s
  steps : ∀{s₀ sₙ tr} → tr ↓ sₙ → Halts s₀ (just tr) sₙ

tr ↓ s = Halts (head tr) (tail tr) s

-- Values of `tr ↑` are proofs that `tr` is infinite (i.e. an execution
-- with that trace never halts).
record _↑ (tr : Trace S) : Set

data Diverges {S} : [ S ] → Maybe (Trace S) → Set where
  steps : ∀{s₀ tr} → tr ↑ → Diverges s₀ (just tr)

record _↑ tr where
  coinductive
  field
    force : Diverges (head tr) (tail tr)
open _↑ public

-- A trace cannot both halt and loop
halt-loop : ∀{tr : Trace S} {s} → tr ↓ s → ¬ tr ↑
halt-loop {tr = tr} h d with tail tr | force d
halt-loop {tr = tr} (steps hh) d | _ | steps dd = halt-loop hh dd

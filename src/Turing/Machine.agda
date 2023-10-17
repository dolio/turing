
module Turing.Machine where

open import Data.Maybe
open import Data.Nat
open import Data.Product

open import Finite

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

variable
  A B : Set
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

-- A state trace is a potentially infinite sequence of states that a
-- machine may pass through while executing.
record Trace (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Maybe (Trace A)
open Trace public

data M (R : A -> B -> Set) : Maybe A -> Maybe B -> Set where
  nothing : M R nothing nothing
  just : ∀{x y} → R x y -> M R (just x) (just y)

record □ (R : A -> B -> Set) (tl : Trace A) (tr : Trace B) : Set where
  coinductive
  field
    head : R (head tl) (head tr)
    tail : M (□ R) (tail tl) (tail tr)

-- Values of `tr ↓ a` are proofs that the Trace `tr` terminates with a final
-- head `a`
_↓_ : Trace A → A → Set
data Halts {A} : A → Maybe (Trace A) → A → Set where
  finish : ∀ a → Halts a nothing a
  steps  : ∀{a₀ aₙ tr} → tr ↓ aₙ → Halts a₀ (just tr) aₙ

tr ↓ a = Halts (head tr) (tail tr) a

∣_∣ : ∀{tr} {a : A} → tr ↓ a -> ℕ
∣_∣ {tr = tr} h with tail tr
∣_∣ {tr = tr} (finish _) | .nothing = 0
∣_∣ {tr = tr} (steps  x) | just ttr = suc (∣_∣ {tr = ttr} x)

-- Values of `tr ↑` are proofs that the Trace `tr` is infinite.
record _↑ (tr : Trace A) : Set

data Diverges {A} : A → Maybe (Trace A) → Set where
  steps : ∀{a₀ tr} → tr ↑ → Diverges a₀ (just tr)

record _↑ tr where
  coinductive
  field
    force : Diverges (head tr) (tail tr)
open _↑ public

-- A trace cannot both halt and loop
halt-loop : ∀{tr : Trace A} {a} → tr ↓ a → ¬ tr ↑
halt-loop {tr = tr} h d with tail tr | force d
halt-loop {tr = tr} (steps hh) d | _ | steps dd = halt-loop hh dd

module St where
  -- Generates the trace of a TM from a given tape and state
  unfold : (tm : TM) → Tape → [ states tm ] → Trace [ states tm ]
  unfold tm tp s .head = s
  unfold tm tp s .tail with step (table tm) tp s
  ... | nothing = nothing
  ... | just (s , tp) = just (unfold tm tp s)

  -- Given a Turing machine and an input, get the trace that results from
  -- executing it.
  execute : (tm : TM) → Input → Trace [ states tm ]
  execute tm i = unfold tm (initialize i) (start tm)

module Tp where
  -- Generates the tape trace of a TM from a given tape and state
  unfold : (tm : TM) → Tape → [ states tm ] → Trace Tape
  unfold tm tp s .head = tp
  unfold tm tp s .tail with step (table tm) tp s
  ... | nothing       = nothing
  ... | just (s , tp) = just (unfold tm tp s)

  -- Given a Turing machine and input, get the tape trace that results from
  -- executing it.
  execute : TM → Input → Trace Tape
  execute tm i = unfold tm (initialize i) (start tm)

module Total where
  -- Generates the full trace of a TM from a given tape and state
  unfold : (tm : TM) → Tape → [ states tm ] → Trace (State (states tm))
  unfold tm tp s .head .auto = s
  unfold tm tp s .head .tape = tp
  unfold tm tp s .tail with step (table tm) tp s
  ... | nothing       = nothing
  ... | just (s , tp) = just (unfold tm tp s)

  -- Given a Turing machine and input, generate the full trace that results
  -- from executing it.
  execute : (tm : TM) → Input → Trace (State (states tm))
  execute tm i = unfold tm (initialize i) (start tm)

  module _ (tm : TM) (i : Input) where
    same-st : State (states tm) -> [ states tm ] -> Set
    same-st tot s = auto tot ≡ s

    same-tp : State (states tm) -> Tape -> Set
    same-tp tot tp = tape tot ≡ tp

    unfold-st : ∀ tp t → □ same-st (unfold tm tp t) (St.unfold tm tp t)
    unfold-st tp t .□.head = refl
    unfold-st tp t .□.tail with step (table tm) tp t
    ... | nothing = nothing
    ... | just (t , tp) = just (unfold-st tp t)

    unfold-tp : ∀ tp t → □ same-tp (unfold tm tp t) (Tp.unfold tm tp t)
    unfold-tp tp t .□.head = refl
    unfold-tp tp t .□.tail with step (table tm) tp t
    ... | nothing = nothing
    ... | just (t , tp) = just (unfold-tp tp t)

    Total~St : □ same-st (execute tm i) (St.execute tm i)
    Total~St = unfold-st (initialize i) (start tm)

    Total~Tp : □ same-tp (execute tm i) (Tp.execute tm i)
    Total~Tp = unfold-tp (initialize i) (start tm)

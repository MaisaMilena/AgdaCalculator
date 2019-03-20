module Calculator where

open import Human.Humanity hiding (_==_)
open import Human.Nat public hiding (_==_)
open import Human.Char public
open import Human.Equality public

--------- Data ---------
-- Generic proof to proof "Or" operation. Proof that one of the arguments must be true
data Either (A B : Set) : Set where
  fst : A -> Either A B
  snd : B -> Either A B

-- Declaring a set of operations
data Operation : Set where
  add sub mul : Operation

-- It's used to identify which number will be updated, the one on the right or left
data Side : Set where
  right left : Side

-- Can be a number, an operation symbol or execution command
data Event : Set where
  clr : Event -- base case
  num : Side -> Nat -> Event -- a digit
  ope : Operation -> Event -- operator

data State : Set where
  state : Operation → Nat → Nat → State


--------- Auxiliar properties ---------
-- Proof of commutativity of addition. Proof by beala
x+0 : (a : Nat) → (a + 0) == a
x+0 zero    = refl
x+0 (suc a) rewrite x+0 a = refl

-- Agda knows that 0 * a == 0, now we are telling that "a * 0 == 0 * a"
a*0 : (a : Nat) -> (a * 0) == 0
a*0 zero    = refl
a*0 (suc a) rewrite (a*0 a) = refl -- does that 0 * a == 0

-- Proof that 1 is identity element of multiply over nats. Proof by beala
a*1 : (a : Nat) -> (a * 1) == a
a*1 zero    = refl
a*1 (suc a) rewrite a*1 a | a*0 a | x+0 a = refl

-- Tells Agda that 1 * a == a
1*a : (a : Nat) -> (1 * a) == a
1*a zero    = refl
1*a (suc a) rewrite 1*a a = refl

--------- Calculator ---------
-- Initial state
init : State
init = (state add 0 0)

-- Calculates the operation related to a state
result : State -> Nat
result (state add a b) = (a + b)
result (state sub a b) = (a - b)
result (state mul a b) = (a * b)

-- Get the current State, an Event and update to a new State
updateState : State -> Event -> State
-- clear
updateState s               clr          = init
-- "num operation": update the numbers values
updateState (state op m n) (num right x) = (state op m x)
updateState (state op m n) (num left x)  = (state op x n)
-- execute an operation: the second element receives the result
updateState (state op m n) (ope e) = (state e 0 (result (state e m n)))


--------- Testing Calculator ---------
testUpState0 : State -- add a number on the left
testUpState0 = (updateState init (num left 1))

testUpState1 : State -- add a number on the right
testUpState1 = (updateState testUpState0 (num right 1))

testUpState2 : State -- executes an operation on both numbers
testUpState2 = (updateState testUpState1 (ope add))


testUpState0a : State -- add a number on the left
testUpState0a = (updateState init (num left 3))

testUpState1a : State -- add a number on the right
testUpState1a = (updateState testUpState0a (num right 5))

testUpState2a : State -- executes an operation on both numbers
testUpState2a = (updateState testUpState1a (ope mul))



--------- Theorems ---------
-- Proofs that the result showing up an operation will always do that operation --
theorem-0 : (s : State) -> (a b : Nat) -> (result (state add a b)) == (a + b)
theorem-0 s a b = refl

theorem-1 : (s : State) -> (a b : Nat) -> (result (state sub a b)) == (a - b)
theorem-1 s a b = refl

theorem-2 : (s : State) -> (a b : Nat) -> (result (state mul a b)) == (a * b)
theorem-2 s a b = refl

-- Given a and b and a proof that one of them is 0, then the result of multiplicating a and b must be 0
theorem-3 : ∀ (a b : Nat) -> Either (a == 0) (b == 0) -> (a * b) == 0
theorem-3 .0 b (fst refl) = refl -- Agda knows that 0 * n == 0 (refl)
theorem-3 a .0 (snd refl) = (a*0 a) -- then we proof that n * 0 is also 0

-- if a == 1: (mul a b) == b
-- if b == 1: (mul a b) == a
-- if a == 1 OR b == 1: Either ((mul a b) == b) ((mul a b) == a)
-- Given a and b and a proof that one of them is 1,
-- then the result of multiplicating a and b must be the number that is not 1
theorem-4 : ∀ (a b : Nat) -> Either (a == 1) (b == 1) -> Either ((a * b) == b) ((a * b) == a)
theorem-4 .1 b (fst refl) = fst (1*a b) -- A proof that 1 * b == b
theorem-4 a .1 (snd refl) = snd (a*1 a) -- A proof that b * 1 == b





-- TODO --
-- -- Evaluates several expressions. E.g. (2 + 3) * 5
-- data Expression : Set where
--   num : Nat -> Expression
--   add : Expression -> Expression -> Expression
--   sub : Expression -> Expression -> Expression


----- VIEW? -----
-- main : Program
-- main _ = do
--
--   print "-- Calculator --"
--   -- Receives a number, an operation symbol and a execution command
--
--   let result = exe-operation 2 3 add
--   print (show result)

  -- let result2 = (primNatToChar (exe-operation 2 3 add))
  -- print (primShowChar result2)


  -- for i from 0 to 10 do:
  --   print ("i: " ++ show i)
  --
  -- if (2 == 2)
  --   (then: print "foo")
  --   (else: print "bar")
  --
  -- let num =
  --       init 0.0
  --       for i from 0 to 1000000 do:
  --         λ result → result f+ 1.0

  -- print (primShowFloat num)

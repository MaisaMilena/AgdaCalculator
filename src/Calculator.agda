module Calculator where

open import Human.Humanity
open import Human.Nat public hiding (_==_)
open import Human.Char public
open import Equality public

-- Declaring a set of operations
data Operation : Set where
  add sub mul : Operation

data Side : Set where
  right left : Side

-- Can be a number, and operation symbol or execution command
data Event : Set where
  clr : Event -- base case
  num : Side -> Nat -> Event -- a digit
  ope : Operation -> Event -- operator

-- data State : Set where
--   state : ℕ → ℕ → Bool → Op → State
data State : Set where
  state : Operation → Nat → Nat → State

-- -- Evaluates several expressions. E.g. (2 + 3) * 5
-- data Expression : Set where
--   num : Nat -> Expression
--   add : Expression -> Expression -> Expression
--   sub : Expression -> Expression -> Expression

result : State -> Nat
result (state add a b) = (a + b)
result (state sub a b) = (a - b)
result (state mul a b) = (a * b)

-- theorem-0 : (s : State) -> (a b : Nat) -> result (state add a b) == a + b
-- theorem-0 s a b = ?






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

module Calculator where

open import Human.Humanity
open import Human.Nat public

-- Declaring a set of operations
data Operation : Set where
  add sub mul div : Operation

-- Evaluates chained Expressions
-- data Expression : Set where
--   num : Nat -> Expression
--   add : Expression -> Expression -> Expression
--   sub : ...

-- let input = 1 -- testing Addition

-- Executes an operation
exe-operation : Nat → Nat → ∀ (op : Operation) → Nat
exe-operation m n add = (m + n)
exe-operation m n sub = (m - n)
exe-operation m n mul = (m * n)
exe-operation m n div = 0


-- TODO: Receives a number and return the corresponding operation?


testAdd : Nat
testAdd = (exe-operation 2 3 add)

testSub : Nat
testSub = (exe-operation 2 3 sub)

main : Program
main _ = do

  print "-- Calculator --"
  -- print "1- Addition"




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

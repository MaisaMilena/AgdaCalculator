module Calculator where

open import Human.Humanity
open import Human.Nat public
open import Human.Char public

-- Declaring a set of operations
data Operation : Set where
  add sub mul : Operation

-- Can be a number, and operation symbol or execution command
-- data Input : Set where
--   num ope exe: Input

-- Evaluates several expressions. E.g. (2 + 3) * 5
data Expression : Set where
  num : Nat -> Expression
  add : Expression -> Expression -> Expression
  sub : Expression -> Expression -> Expression

-- Executes an operation
exe-operation : Nat → Nat → ∀ (op : Operation) → Nat
exe-operation m n add = (m + n)
exe-operation m n sub = (m - n)
exe-operation m n mul = (m * n)

-- exe-expression : Nat → Nat → ∀ (op : Operation) → Nat
-- exe-expression m n add = (m + n)
-- exe-expression m n sub = (m - n)
-- exe-expression m n mul = (m * n)


-- TODO: Receives a number and return the corresponding operation?


testAdd : Nat
testAdd = (exe-operation 2 3 add)

testSub : Nat
testSub = (exe-operation 2 3 sub)
-------
testLength : Nat
testLength = (slength "cromovilha")

main : Program
main _ = do

  print "-- Calculator --"
  -- Receives a number, an operation symbol and a execution command

  let result = exe-operation 2 3 add
  print (show result)



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

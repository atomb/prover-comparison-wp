module Command where

open import Data.List
open import Level

open import Expr
open import Assertion

Set' = Set (suc zero)

data Command : Set' where
  skip   : Command
  assert : Assertion → Command
  assume : Assertion → Command
  _≔_    : Var → Expr → Command        -- assign
  _$_    : Command → Command → Command -- sequence
  _□_    : Command → Command → Command -- choice
  raise  : Command
  _!_    : Command → Command → Command
  _*     : Command → Command           -- loop
  {-
  call   : Var → Command
  -}

data Declaration : Set' where
  func   : Var → Assertion → Command → Assertion → Assertion → Declaration

data Program : Set' where
  prog   : List Declaration → Program

data Context : Set' where
  hole        : Context
  seqleft     : Context → Command → Context
  seqright    : Command → Context → Context
  catchleft   : Context → Command → Context
  catchright  : Command → Context → Context
  choiceleft  : Context → Command → Context
  choiceright : Command → Context → Context

data EvalContext : Set' where
  ehole  : EvalContext
  eseq   : EvalContext → Command → EvalContext
  ecatch : EvalContext → Command → EvalContext

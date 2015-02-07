module Command

import Expr
import Assertion

-- Set' = Set (suc zero)

data Command : Type where
  Skip : Command
  Assert : Assertion -> Command
  Assume : Assertion -> Command
  Assign : Var -> Expr -> Command
  Seq    : Command -> Command -> Command
  Choice : Command -> Command -> Command
  Raise  : Command
  Catch  : Command -> Command -> Command
  {-
  Loop   : Command -> Command
  Call   : Var -> Command
  -}

data Declaration : Type where
  func   : Var -> Assertion -> Command -> Assertion -> Assertion -> Declaration

data Program : Type where
  prog   : List Declaration -> Program

data Context : Type where
  hole        : Context
  seqleft     : Context -> Command -> Context
  seqright    : Command -> Context -> Context
  catchleft   : Context -> Command -> Context
  catchright  : Command -> Context -> Context
  choiceleft  : Context -> Command -> Context
  choiceright : Command -> Context -> Context

data EvalContext : Type where
  ehole  : EvalContext
  eseq   : EvalContext -> Command -> EvalContext
  ecatch : EvalContext -> Command -> EvalContext

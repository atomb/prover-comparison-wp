module Command

import Expr
import Assertion

%access public export

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
  Func   : Var -> Assertion -> Command -> Assertion -> Assertion -> Declaration

data Program : Type where
  Prog   : List Declaration -> Program

data Context : Type where
  Hole        : Context
  SeqLeft     : Context -> Command -> Context
  SeqRight    : Command -> Context -> Context
  CatchLeft   : Context -> Command -> Context
  CatchRight  : Command -> Context -> Context
  ChoiceLeft  : Context -> Command -> Context
  ChoiceRight : Command -> Context -> Context

data EvalContext : Type where
  EHole  : EvalContext
  ESeq   : EvalContext -> Command -> EvalContext
  ECatch : EvalContext -> Command -> EvalContext

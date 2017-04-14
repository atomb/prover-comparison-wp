module Expr

%access public export

data Var : Type where
  IVar : Int -> Var

data Value : Type where
  Const : Int -> Value

data Store : Type where
  Empty  : Store
  Extend : Store -> Var -> Value -> Store

data Lookup : Var -> Store -> Value -> Type where
  L_Here : (s : Store) -> (x : Var) ->  (v : Value)
        -> Lookup x (Extend s x v) v
  L_There : (s : Store)
         -> (x : Var) -> (v : Value)
         -> (x' : Var) -> (v' : Value)
         -> Lookup x s v -> Lookup x (Extend s x' v') v

Expr : Type
Expr = Store -> Value


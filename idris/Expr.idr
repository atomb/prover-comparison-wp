module Expr

data Var : Type where
  var : Int -> Var

data Value : Type where
  const : Int -> Value

data Store : Type where
  empty  : Store
  extend : Store -> Var -> Value -> Store

data Lookup : Var -> Store -> Value -> Type where
  L_Here : (s : Store) -> (x : Var) ->  (v : Value)
        -> Lookup x (extend s x v) v
  L_There : (s : Store)
         -> (x : Var) -> (v : Value)
         -> (x' : Var) -> (v' : Value)
         -> Lookup x s v -> Lookup x (extend s x' v') v

Expr : Type
Expr = Store -> Value


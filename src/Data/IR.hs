module Data.IR where

-- | Types
--   SigmaT and PiT are types if the result of their lambda is a type
data Type e
  = -- | Type of types
    TypeT
  | -- | Empty type
    VoidT
  | -- | Unit type
    UnitT
  | -- | Dependent pair, represented as a type and a lambda that take the value of the type and return another type
    SigmaT (Type e) (Lambda e)
  | -- | Dependent function, same representation as SigmaT
    PiT (Type e) (Lambda e)
  | -- | Sum type
    ChoiceT (Type e) (Type e)

-- | Unnamed function (aka lambda)
data Lambda e
  = -- | Lambda expression
    Lambda
      e
      -- ^ parameter name
      (Exp e)
      -- ^ expression of the lambda

-- | Apply an expression to a lambda
apply :: (Eq e) => Lambda e -> Exp e -> Exp e
apply (Lambda p e) v = replace cond e
  where
    cond (NameE e) | e == p = v
    cond e = e

-- | Expression
data Exp e
  = -- | Type in an expression
    TypeE (Type e)
  | -- | literal name of an existing variable
    NameE e
  | -- | Constructor of the unit type
    UnitE
  | -- | Constructor of a pair
    PairE (Exp e) (Exp e)
  | -- | Destructor for Pair, it should have a lambda of lambda (to bind both values of the pair)
    MatchPairE (Exp e) (Lambda e)
  | -- | Constructor of lambda expression
    LambdaE (Lambda e)
  | -- | Destructor for lambda
    ApplyE (Exp e) (Lambda e)
  | -- | Left constructor of a Sum Type
    InlE (Exp e)
  | -- | Rigt constructor of a Sum Type
    InrE (Exp e)
  | -- | Destructor for Sum types
    MatchChoiceE (Exp e) (Lambda e) (Lambda e)

-- | Values status
data Status
  = -- | Irreductible state with no external bindings
    Normal
  | -- | Irreductible state with external bindings
    Neutral
  | -- | Unknown status
    Unevaluated

-- | A value is an expression with a type and a status
data Value e = Value Status (Type e) (Exp e)

-- | Type class to replace names bounded by lambda by the value provided. Needed for lambda application.
class HasReplace r where
  replace :: (Exp e -> Exp e) -> r e -> r e

instance HasReplace Lambda where
  replace re (Lambda e exp) = Lambda e (replace re exp)

instance HasReplace Type where
  replace re (SigmaT t l) = SigmaT (replace re t) (replace re l)
  replace re (PiT t l) = SigmaT (replace re t) (replace re l)
  replace _ t = t

instance HasReplace Exp where
  replace re (TypeE t) = TypeE (replace re t)
  replace re (PairE e1 e2) = PairE (replace re e1) (replace re e2)
  replace re (MatchPairE e l) = MatchPairE (replace re e) (replace re l)
  replace re (LambdaE l) = LambdaE (replace re l)
  replace re (InlE e) = InlE (replace re e)
  replace re (InrE e) = InrE (replace re e)
  replace re (MatchChoiceE e l1 l2) = MatchChoiceE (replace re e) (replace re l1) (replace re l2)
  replace _ e = e

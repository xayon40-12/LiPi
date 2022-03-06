module Data.IR where

-- | Types
data Type e
  = -- | Type of types
    TypeT
  | -- | Empty type
    VoidT
  | -- | Unit type
    UnitT
  | -- | Dependent pair, represented as a type and a lambda that take the value of the type and return another type
    SigmaT (Type e) (Lambda Type e)
  | -- | Dependent function, same representation as SigmaT
    PiT (Type e) (Lambda Type e)
  | -- | Sum type
    ChoiceT (Type e) (Type e)

-- | Unnamed function (aka lambda)
data Lambda f e
  = -- | Lambda expression
    Lambda
      e
      -- ^ parameter name
      (f e)
      -- ^ expression of the lambda

-- | Apply an expression to a lambda
apply :: (Eq e, HasReplace f, IsSame f) => Lambda f e -> f e -> f e
apply (Lambda p e) v = replace cond e
  where
    cond e | isSame e p = v
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
  | -- | Destructor for Pair
    MatchPairE (Exp e) (Lambda (Lambda Exp) e)
  | -- | Constructor of lambda expression
    LambdaE (Lambda Exp e)
  | -- | Left constructor of a Sum Type
    InlE (Exp e)
  | -- | Rigt constructor of a Sum Type
    InrE (Exp e)
  | -- | Destructor for Sum types
    MatchChoiceE (Exp e) (Lambda Exp e) (Lambda Exp e)

-- | Values status
data Value e
  = -- | A value in its normal form (irreductidle with no external binding)
    Normal (Exp e)
  | -- | An irreductible value that has extrnal bindings
    Neutral (Exp e)
  | -- | A value which as not yet been evaluated
    Unevaluated (Exp e)

-- | Type class to verify if a token as the same value as a variable name
class IsSame f where
  isSame :: (Eq e) => f e -> e -> Bool

instance IsSame Exp where
  isSame (NameE e1) e2 = e1 == e2
  isSame _ _ = False

instance IsSame Type where isSame _ _ = False

instance IsSame (Lambda f) where isSame _ _ = False

-- | Type class to replace names bounded by lambda by the value provided. Needed for lambda application.
class HasReplace r where
  replace :: HasReplace f => (f e -> f e) -> r e -> r e

instance (HasReplace f) => HasReplace (Lambda f) where
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

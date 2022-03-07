{-# LANGUAGE LambdaCase #-}

module Data.IR () where

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
  deriving (Eq)

isType :: Type e -> Bool
isType (SigmaT t1 (Lambda _ _ (Value _ t2 _))) = isType t1 && isType t2
isType (PiT t1 (Lambda _ _ (Value _ t2 _))) = isType t1 && isType t2
isType (ChoiceT t1 t2) = isType t1 && isType t2
isType _ = True

-- | Unnamed function (aka lambda)
data Lambda e
  = -- | Lambda expression
    Lambda
      e
      -- ^ parameter name
      (Type e)
      -- ^ parameter type
      (Value e)
      -- ^ expression of the lambda
  deriving (Eq)

-- | Apply a value to a lambda. The value must have the same
apply :: (Eq e) => Lambda e -> Value e -> Maybe (Value e)
apply (Lambda p t r) v@(Value _ vt e) = if t == vt then Just $ replace cond r else Nothing
  where
    cond (Value _ _ (NameE e _)) | e == p = v
    cond e = e

-- | Expression
data Exp e
  = -- | Type in an expression
    TypeE (Type e)
  | -- | literal name of an existing variable
    NameE e (Type e)
  | -- | Constructor of the unit type
    UnitE
  | -- | Constructor of a pair
    PairE (Value e) (Value e)
  | -- | Destructor for Pair, it should have a lambda of lambda (to bind both values of the pair) and the value should be a pair
    MatchPairE (Value e) (Lambda e)
  | -- | Constructor of lambda expression
    LambdaE (Lambda e)
  | -- | Destructor for lambda
    ApplyE (Value e) (Lambda e)
  | -- | Left constructor of a Sum Type
    InlE (Value e)
  | -- | Rigt constructor of a Sum Type
    InrE (Value e)
  | -- | Destructor for Sum types, the value should be a choice
    MatchChoiceE (Value e) (Lambda e) (Lambda e)
  deriving (Eq)

type Error = String

unless :: Bool -> Error -> Maybe Error
unless True _ = Nothing
unless False err = Just err

typeCheck :: Eq e => Exp e -> Type e -> Maybe Error
typeCheck (TypeE t1) t2 = unless (t1 == t2) ""
typeCheck (NameE _ t1) t2 = unless (t1 == t2) ""
typeCheck UnitE UnitT = Nothing
typeCheck UnitE _ = Just ""
typeCheck (PairE v1 v2) (SigmaT t l) = unless (valueType v1 == t && case apply l v1 of Just (Value _ TypeT (TypeE t2)) -> valueType v2 == t2; _ -> False) ""
typeCheck (PairE _ _) _ = Just ""

-- | Values status
data Status
  = -- | Irreductible state with no external bindings
    Normal
  | -- | Irreductible state with external bindings
    Neutral
  | -- | Unknown status
    Unevaluated
  deriving (Eq)

-- | A value is an expression with a type and a status
data Value e = Value Status (Type e) (Exp e) deriving (Eq)

newValue :: (Eq e) => Status -> Type e -> Exp e -> Either Error (Value e)
newValue s t e = case typeCheck e t of
  Nothing -> Right $ Value s t e
  Just err -> Left err

valueType :: Value e -> Type e
valueType (Value _ t _) = t

sameType :: (Eq e) => Value e -> Value e -> Bool
sameType v1 v2 = valueType v1 == valueType v2

-- | Type class to replace names bounded by lambda by the value provided. Needed for lambda application.
class HasReplace r where
  replace :: (Value e -> Value e) -> r e -> r e

instance HasReplace Value where
  replace re (Value s t e) = Value Unevaluated t (replace re e)

instance HasReplace Lambda where
  replace re (Lambda e t v) = Lambda e t (replace re v)

instance HasReplace Type where
  replace re (SigmaT t l) = SigmaT (replace re t) (replace re l)
  replace re (PiT t l) = SigmaT (replace re t) (replace re l)
  replace _ t = t

instance HasReplace Exp where
  replace re (TypeE t) = TypeE (replace re t)
  replace re (PairE v1 v2) = PairE (replace re v1) (replace re v2)
  replace re (MatchPairE v l) = MatchPairE (replace re v) (replace re l)
  replace re (LambdaE l) = LambdaE (replace re l)
  replace re (InlE v) = InlE (replace re v)
  replace re (InrE v) = InrE (replace re v)
  replace re (MatchChoiceE v l1 l2) = MatchChoiceE (replace re v) (replace re l1) (replace re l2)
  replace _ v = v

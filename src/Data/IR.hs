module Data.IR (Type (TypeT, VoidT, UnitT), sigmaT, piT, choiceT, Lambda (), withLambda, Name (..), Exp (TypeE, UnitE, PairE, LambdaE, InlE, InrE), applyE, matchE, Value (), newValue) where

import Data.Set (Set, delete, empty, singleton)

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
  | -- | Dependent function, same representation as SigmaT. The boolean represent the linearity of the function
    PiT (Type e) (Lambda e) Bool
  | -- | Sum type
    ChoiceT (Type e) (Type e)
  deriving (Eq, Ord, Show)

isSigmaT, isChoiceT :: Type e -> Bool
isSigmaT (SigmaT _ _) = True
isSigmaT _ = False
isChoiceT (ChoiceT _ _) = True
isChoiceT _ = False

sigmaT :: (Show e) => Type e -> Lambda e -> Either Error (Type e)
sigmaT t l@(Lambda (Name e tl) (Value _ tv _)) =
  if isType tv
    then Right $ SigmaT t l
    else Left $ "The return type of the lambda in a SigmaT must be a valid Type, found: (" <> show tv <> ")."

piT :: (Show e) => Type e -> Lambda e -> Either Error (Type e)
piT t l@(Lambda (Name e tl) (Value _ tv _)) =
  if isType tv
    then Right $ SigmaT t l
    else Left $ "The return type of the lambda in a PiT must be a valid Type, found: (" <> show tv <> ")."

choiceT :: (Show e) => Type e -> Type e -> Either Error (Type e)
choiceT t1 t2 = case (isType t1, isType t2) of
  (True, True) -> Right $ ChoiceT t1 t2
  (False, True) -> Left $ "Both types in a ChoiceT must be valid types but the first is not: (" <> show t1 <> ")."
  (True, False) -> Left $ "Both types in a ChoiceT must be valid types but the second is not: (" <> show t2 <> ")."
  (False, False) -> Left $ "Both types in a ChoiceT must be valid types but both are not: first (" <> show t1 <> "), second (" <> show t2 <> ")."

isType :: Type e -> Bool
isType TypeT = False -- The type of types is not an element of itself
isType VoidT = True
isType UnitT = True
isType (SigmaT t1 (Lambda (Name _ _) (Value _ t2 _))) = isType t1 && isType t2
isType (PiT t1 (Lambda (Name _ _) (Value _ t2 _)) _) = isType t1 && isType t2
isType (ChoiceT t1 t2) = isType t1 && isType t2

-- | Unnamed function (aka lambda)
data Lambda e
  = -- | Lambda expression
    Lambda
      (Name e)
      -- ^ typed parameter
      (Value e)
      -- ^ expression of the lambda
  deriving (Eq, Ord, Show)

-- | Lambda smart constructor that take a name and a callback as input. It provide the name as an expression to the callmack to use it to produce the value that the lambda would return by replacing this name with a value during application.
withLambda :: (Eq e, Ord e) => Name e -> (Exp e -> Value e) -> Lambda e
withLambda n f = Lambda n (f (NameE n))

-- | lambda application
apply :: (Eq e, Ord e) => Lambda e -> Value e -> Value e
apply (Lambda (Name p _) r) (Value _ _ v) = replace (p, v) r

-- | Literal name refering to a top level binder (name a of lambda parameter)
data Name e = Name e (Type e) deriving (Eq, Ord, Show)

-- | Expression
data Exp e
  = -- | Type in an expression
    TypeE (Type e)
  | -- | literal name refering to a top level lambda parameter
    NameE (Name e)
  | -- | Constructor of the unit type
    UnitE
  | -- | Constructor of a pair
    PairE (Value e) (Value e)
  | -- | Constructor of lambda expression
    LambdaE (Lambda e)
  | -- | Destructor for lambda
    ApplyE (Lambda e) (Value e)
  | -- | Left constructor of a Sum Type
    InlE (Value e)
  | -- | Rigt constructor of a Sum Type
    InrE (Value e)
  | -- | Destructor for Pair and Sum types, the first value should be a pair or a choice and the second a lambda of lambda to extract both values of the pair and respectively a pair of lambda to extract both possibility of a choice
    MatchE (Value e) (Value e)
  --  | -- |
  -- RecE (Name e) (Value e) (Value e)
  deriving (Eq, Ord, Show)

applyE :: (Show e, Eq e) => Lambda e -> Value e -> Either Error (Exp e)
applyE l@(Lambda (Name _ tl) _) v@(Value _ tv _) =
  if tv == tl
    then Right $ ApplyE l v
    else Left $ "The input type of the lambda in a ApplyE must be the same as the value, expected (" <> show tv <> "), provided (" <> show tl <> ")."

matchE :: (Show e, Eq e) => Value e -> Value e -> Either Error (Exp e)
matchE v@(Value _ _ (PairE p1@(Value _ tp1 _) p2@(Value _ tp2 _))) l@(Value _ _ (LambdaE (Lambda (Name _ tl) (Value _ tll _)))) = case (tp1 == tl, tp2 == tll) of
  (True, True) -> Right $ MatchE v l
  (False, True) -> Left $ "In a match expression for a pair, The input type of the lambda must be the same as the type of the first value of the pair, expected (" <> show tp1 <> "), provided (" <> show tl <> ")."
  (True, False) -> Left $ "In a match expression for a pair, the output of the lambda must be a lambda that takes as input the same type as the second value of the pair, expected (" <> show tp2 <> "), provided (" <> show tll <> ")."
  (False, False) -> Left $ "In a match expression for a pair, The input type of the lambda must be the same as the type of the first value of the pair, expected (" <> show tp1 <> "), provided (" <> show tl <> "), and the output of the lambda must be a lambda that takes as input the same type as the second value of the pair, expected (" <> show tp2 <> "), provided (" <> show tll <> ")."
matchE v1@(Value _ (ChoiceT t1 t2) _) v2@(Value _ _ (PairE (Value _ _ (LambdaE (Lambda (Name _ tl1) _))) (Value _ _ (LambdaE (Lambda (Name _ tl2) _))))) = case (t1 == tl1, t2 == tl2) of
  (True, True) -> Right $ MatchE v1 v2
  (False, True) -> Left $ "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but the first is not: expected (" <> show t1 <> "), provided (" <> show tl1 <> ")."
  (True, False) -> Left $ "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but the second is not: expected (" <> show t2 <> "), provided (" <> show tl2 <> ")."
  (False, False) -> Left $ "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but both are not: first expected (" <> show t1 <> ") and provided (" <> show tl1 <> "), second expected (" <> show t2 <> ") and provided (" <> show tl2 <> ")."
matchE (Value _ t1 _) (Value _ t2 _) = Left $ "The values provided to a MatchE must be either a pair or a choice and respectively a lambda or a pair of lambda, provided (" <> show t1 <> ") and (" <> show t2 <> ")."

type Error = String

unless :: Bool -> Error -> Maybe Error
unless True _ = Nothing
unless False err = Just err

-- | Verify that the expression as the given type. If not, an information about the difference is returned.
typeCheck :: (Show e, Eq e, Ord e) => Exp e -> Type e -> Maybe Error
typeCheck e t =
  if isType t
    then typeCheck' e t
    else Just $ "The type (" <> show t <> ") is not actually a type."
  where
    typeCheck' :: (Eq e, Ord e) => Exp e -> Type e -> Maybe Error
    typeCheck' (TypeE _) TypeT = Nothing
    typeCheck' (TypeE _) _ = Just ""
    typeCheck' (NameE (Name _ t1)) t2 = unless (t1 == t2) ""
    typeCheck' UnitE UnitT = Nothing
    typeCheck' UnitE _ = Just ""
    typeCheck' (PairE v1 v2) (SigmaT t l) = unless (valueType v1 == t && case apply l v1 of (Value _ TypeT (TypeE t2)) -> valueType v2 == t2; _ -> False) ""
    typeCheck' (PairE _ _) _ = Just ""
    typeCheck' (LambdaE l) _ = undefined -- TODO: forbid nested name shadowing
    typeCheck' (ApplyE l v) _ = undefined
    typeCheck' (InlE (Value _ t _)) (ChoiceT tl _) = unless (t == tl) ""
    typeCheck' (InlE (Value _ t _)) _ = Just ""
    typeCheck' (InrE (Value _ t _)) (ChoiceT _ tr) = unless (t == tr) ""
    typeCheck' (InrE (Value _ t _)) _ = Just ""
    typeCheck' (MatchE v l) _ = undefined

-- | Values status
data Status e
  = -- | Irreductible state with no external bindings
    Normal
  | -- | Reductible state with no external bindings
    Neutral (Set (Name e))
  | -- | Reductible state with external bindings
    Reductible
  | -- | Irreductible state with external bindings
    NeutralR (Set (Name e))
  deriving (Eq, Ord, Show)

instance (Ord e) => Semigroup (Status e) where
  NeutralR s1 <> NeutralR s2 = NeutralR (s1 <> s2)
  NeutralR s1 <> Neutral s2 = NeutralR (s1 <> s2)
  NeutralR s1 <> Reductible = NeutralR s1
  NeutralR s1 <> Normal = NeutralR s1
  Reductible <> Reductible = Reductible
  Reductible <> Neutral s = NeutralR s
  Reductible <> Normal = Reductible
  Neutral s1 <> Neutral s2 = Neutral (s1 <> s2)
  Neutral s <> Normal = Neutral s
  Normal <> Normal = Normal
  a <> b = b <> a

instance (Ord e) => Monoid (Status e) where
  mempty = Normal

-- | A value is an expression with a type and a status
data Value e = Value (Status e) (Type e) (Exp e) deriving (Eq, Ord, Show)

-- | Create a value from a type and an expression if it typechecks
newValue :: (Eq e, Ord e, Show e) => Type e -> Exp e -> Either Error (Value e)
newValue t e = case typeCheck e t of
  Nothing -> Right $ Value (status e) t e
  Just err -> Left err

valueType :: Value e -> Type e
valueType (Value _ t _) = t

-- | Type class to replace names bounded by lambda by the value provided. Needed for lambda application.
class HasReplace r where
  replace :: (Eq e, Ord e) => (e, Exp e) -> r e -> r e

instance HasReplace Value where
  replace re (Value s t e) = let ne = replace re e in Value (status ne) t ne

instance HasReplace Lambda where
  replace re (Lambda n v) = Lambda n (replace re v)

instance HasReplace Type where
  replace _ TypeT = TypeT
  replace _ VoidT = VoidT
  replace _ UnitT = UnitT
  replace re (SigmaT t l) = SigmaT (replace re t) (replace re l)
  replace re (PiT t l lin) = PiT (replace re t) (replace re l) lin
  replace re (ChoiceT t1 t2) = ChoiceT (replace re t1) (replace re t2)

instance HasReplace Exp where
  replace re (TypeE t) = TypeE (replace re t)
  replace (p, e) ne@(NameE (Name n _)) = if p == n then e else ne
  replace _ UnitE = UnitE
  replace re (PairE v1 v2) = PairE (replace re v1) (replace re v2)
  replace re (LambdaE l) = LambdaE (replace re l)
  replace re (ApplyE l n) = ApplyE (replace re l) (replace re n)
  replace re (InlE v) = InlE (replace re v)
  replace re (InrE v) = InrE (replace re v)
  replace re (MatchE v1 v2) = MatchE (replace re v1) (replace re v2)

-- | Type class to search the number of binding names present
class HasStatus r where
  status :: (Ord e) => r e -> Status e

instance HasStatus Value where
  status (Value s _ _) = s

instance HasStatus Lambda where
  status (Lambda n v) = case status v of
    Neutral ns -> let nns = delete n ns in if null nns then Normal else Neutral nns
    NeutralR ns -> let nns = delete n ns in if null nns then Reductible else NeutralR nns
    unbounded -> unbounded

instance HasStatus Type where
  status TypeT = mempty
  status VoidT = mempty
  status UnitT = mempty
  status (SigmaT t l) = status t <> status l
  status (PiT t l _) = status t <> status l
  status (ChoiceT t1 t2) = status t1 <> status t2

instance HasStatus Exp where
  status (TypeE t) = status t
  status (NameE n) = Neutral $ singleton n
  status UnitE = mempty
  status (PairE v1 v2) = status v1 <> status v2
  status (LambdaE l) = status l
  status (ApplyE l n) = Reductible <> status l <> status n
  status (InlE v) = status v
  status (InrE v) = status v
  status (MatchE v1 v2) = case status v1 <> status v2 of
    Normal -> Reductible -- In this case the match can be computed
    s -> s

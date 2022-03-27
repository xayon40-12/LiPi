module LiPi.IR.Internals where

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
  | -- | Dependent pair, represented as a type and a lambda that take the value of the type and return another type. The boolean represent the linearity
    SigmaT (Type e) (Lambda e) Bool
  | -- | Dependent function, same representation as SigmaT.
    PiT (Type e) (Lambda e) Bool
  | -- | Sum type
    ChoiceT (Type e) (Type e)
  | -- | Tagged type
    TaggedT e (Type e)
  | -- | Used for inductive types in conjonction with  TaggedT
    InductiveT e
  deriving (Eq, Ord, Show)

-- | Unnamed function (aka lambda)
data Lambda e
  = -- | Lambda expression
    Lambda
      (Maybe e)
      -- ^ parameter name
      (Type e)
      -- ^ parameter type
      (Value e)
      -- ^ expression of the lambda
      Bool
      -- ^ Linearity of the lambda
  deriving (Eq, Ord, Show)

-- | lambda application
apply :: (Eq e, Ord e) => Lambda e -> Value e -> Value e
apply (Lambda (Just p) _ r _) (Value _ _ v) = replace (p, v) r
apply (Lambda Nothing _ r _) _ = r

-- | Literal name refering to a top level binder (name a of lambda parameter), the Bool is for linearity
data Name e = Name e (Type e) Bool deriving (Eq, Ord, Show)

-- | Expression
data Exp e
  = -- | Type in an expression
    TypeE (Type e)
  | -- | literal name refering to a top level lambda parameter
    NameE (Name e)
  | -- | Constructor of the unit type
    UnitE
  | -- | Constructor of a pair where the (Maybe e) is for a potential binding name, useful for linear pair
    PairE (Maybe e) (Value e) (Value e) Bool
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
  | -- |
    RecE e (Value e) (Value e)
  deriving (Eq, Ord, Show)

type Error = String

-- | Values status
data Status e
  = -- | Irreductible state with no external bindings
    Normal
  | -- | Reductible state with no external bindings
    Neutral (Set e)
  | -- | Reductible state with external bindings
    Reductible
  | -- | Irreductible state with external bindings
    NeutralR (Set e)
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

-- | A definition is a 'Normal' top level binding
data Definition e
  = Definition
      e
      -- ^ name of the definition
      (Type e)
      (Exp e)
  deriving (Eq, Ord, Show)

-- | Type class to replace names bounded by lambda by the value provided. Needed for lambda application.
class HasReplace r where
  replace :: (Eq e, Ord e) => (e, Exp e) -> r e -> r e

instance HasReplace Value where
  replace re (Value s t e) = let ne = replace re e in Value (status ne) t ne

instance HasReplace Lambda where
  replace re (Lambda n t v lin) = Lambda n t (replace re v) lin

instance HasReplace Type where
  replace _ TypeT = TypeT
  replace _ VoidT = VoidT
  replace _ UnitT = UnitT
  replace re (SigmaT t l lin) = SigmaT (replace re t) (replace re l) lin
  replace re (PiT t l lin) = PiT (replace re t) (replace re l) lin
  replace re (ChoiceT t1 t2) = ChoiceT (replace re t1) (replace re t2)
  replace re (TaggedT n t) = TaggedT n (replace re t)
  replace _ i@(InductiveT _) = i

instance HasReplace Exp where
  replace re (TypeE t) = TypeE (replace re t)
  replace (p, e) ne@(NameE (Name n _ _)) = if p == n then e else ne
  replace _ UnitE = UnitE
  replace re (PairE n v1 v2 lin) = PairE n (replace re v1) (replace re v2) lin
  replace re (LambdaE l) = LambdaE (replace re l)
  replace re (ApplyE l n) = ApplyE (replace re l) (replace re n)
  replace re (InlE v) = InlE (replace re v)
  replace re (InrE v) = InrE (replace re v)
  replace re (MatchE v1 v2) = MatchE (replace re v1) (replace re v2)
  replace re (RecE n v1 v2) = RecE n (replace re v1) (replace re v2)

-- | Type class to search the number of binding names present
class HasStatus r where
  status :: (Ord e) => r e -> Status e

instance HasStatus Value where
  status (Value s _ _) = s

instance HasStatus Lambda where
  status (Lambda n t v _) = boundedStatus n t v

boundedStatus :: (Ord e) => Maybe e -> Type e -> Value e -> Status e
boundedStatus n t v = case status v of
  Neutral ns -> let nns = maybe ns (`delete` ns) n in if null nns then Normal else Neutral nns
  NeutralR ns -> let nns = maybe ns (`delete` ns) n in if null nns then Reductible else NeutralR nns
  unbounded -> unbounded

instance HasStatus Type where
  status TypeT = mempty
  status VoidT = mempty
  status UnitT = mempty
  status (SigmaT t l _) = status t <> status l
  status (PiT t l _) = status t <> status l
  status (ChoiceT t1 t2) = status t1 <> status t2
  status (TaggedT _ t) = status t
  status (InductiveT _) = mempty -- WARING: is it neutral or Reductible due to induction? Maybe always Reductible as it can expand indefinitly

instance HasStatus Exp where
  status (TypeE t) = status t
  status (NameE (Name n _ _)) = Neutral $ singleton n
  status UnitE = mempty
  status (PairE n v1@(Value _ t _) v2 _) = status v1 <> boundedStatus n t v2
  status (LambdaE l) = status l
  status (ApplyE l v) = Reductible <> status l <> status v
  status (InlE v) = status v
  status (InrE v) = status v
  status (MatchE v1 v2) = case status v1 <> status v2 of
    Normal -> Reductible -- In this case the match can be computed
    s -> s
  status (RecE _ v1 v2) = status v1 <> status v2 -- the name of the function use in the recursion is not a lambda binder, thus it does not count

-- | Type class to count the number of occurences of a nome
class HasOccurences o where
  occurences :: (Eq e, Ord e) => e -> o e -> Int

instance HasOccurences Value where
  occurences n (Value _ _ e) = occurences n e

instance HasOccurences Lambda where
  occurences n (Lambda _ _ v _) = occurences n v

instance HasOccurences Type where
  occurences _ TypeT = 0
  occurences _ VoidT = 0
  occurences _ UnitT = 0
  occurences n (SigmaT t l _) = occurences n t + occurences n l
  occurences n (PiT t l _) = occurences n t + occurences n l
  occurences n (ChoiceT t1 t2) = occurences n t1 + occurences n t2
  occurences n (TaggedT _ t) = occurences n t
  occurences n (InductiveT _) = 0

instance HasOccurences Exp where
  occurences n (TypeE t) = occurences n t
  occurences n (NameE (Name n2 _ _)) = if n == n2 then 1 else 0
  occurences _ UnitE = 0
  occurences n (PairE _ v1 v2 _) = undefined
  occurences n (LambdaE l) = occurences n l
  occurences n (ApplyE l v) = undefined
  occurences n (InlE v) = occurences n v
  occurences n (InrE v) = occurences n v
  occurences n (MatchE v1 v2) = undefined
  occurences n (RecE _ v1 v2) = undefined

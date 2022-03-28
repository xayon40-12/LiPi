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
  | -- | An value that is guaranteed to evaluate as a type
    ValueT (Value e)
  | -- | Dependent pair, represented as a binding name for the following type, and the expression of the second type that may contains the binding name. The boolean represent the linearity
    SigmaT e (Type e) (Type e) Bool
  | -- | Dependent function, same representation as SigmaT.
    PiT e (Type e) (Type e) Bool
  | -- | Sum type
    ChoiceT (Type e) (Type e)
  | -- | Tagged type
    TaggedT e (Type e)
  | -- | Used for inductive types in conjonction with  TaggedT
    InductiveT e
  deriving (Eq, Ord, Show)

-- | Expression
data Exp e
  = -- | Type in an expression
    TypeE (Type e)
  | -- | literal name refering to a top level lambda parameter
    NameE e (Type e) Bool
  | -- | Constructor of the unit type
    UnitE
  | -- | Constructor of a pair where the (e) is o binding name, useful for linear pair
    PairE e (Value e) (Value e) Bool
  | -- | Constructor of lambda expression that have a binding name correspoding to the following type, and has a return value and a linearity
    LambdaE e (Type e) (Value e) Bool
  | -- | Destructor for lambda
    ApplyE (Value e) (Value e)
  | -- | Left constructor of a Sum Type
    InlE (Value e)
  | -- | Rigt constructor of a Sum Type
    InrE (Value e)
  | -- | Destructor for Sum types, the first value should be a choice and the second and third one lambda for each case. The output type might be deffirent.
    MatchChoiceE (Value e) (Value e) (Value e)
  | -- | Destructor for Pair , the first value should be a pair and the second a lambda that takes the first element of the pair as input which return value should evaluate ta a lambda that takes the second element as input. As in dependent pair the second type might depend on the first, thus the second lambda might depend on the first element as well
    MatchPairE (Value e) (Value e)
  | -- | Destructor for recursive call on Sum types. Takes the name and type af the function, and a matchE for each deconstructed values 'd' that matches over the pairs (d , f d)
    RecMatchE e (Type e) (Value e) (Value e)
  deriving (Eq, Ord, Show)

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

instance HasReplace Type where
  replace _ TypeT = TypeT
  replace _ VoidT = VoidT
  replace _ UnitT = UnitT
  replace re (ValueT e) = ValueT (replace re e)
  replace re (SigmaT n t e lin) = SigmaT n (replace re t) (replace re e) lin
  replace re (PiT n t e lin) = PiT n (replace re t) (replace re e) lin
  replace re (ChoiceT t1 t2) = ChoiceT (replace re t1) (replace re t2)
  replace re (TaggedT n t) = TaggedT n (replace re t)
  replace _ i@(InductiveT _) = i

instance HasReplace Exp where
  replace re (TypeE t) = TypeE (replace re t)
  replace (p, e) ne@(NameE n _ _) = if p == n then e else ne
  replace _ UnitE = UnitE
  replace re (PairE n v1 v2 lin) = PairE n (replace re v1) (replace re v2) lin
  replace re (LambdaE n t v lin) = LambdaE n t (replace re v) lin
  replace re (ApplyE l n) = ApplyE (replace re l) (replace re n)
  replace re (InlE v) = InlE (replace re v)
  replace re (InrE v) = InrE (replace re v)
  replace re (MatchChoiceE v1 v2 v3) = MatchChoiceE (replace re v1) (replace re v2) (replace re v3)
  replace re (MatchPairE v1 v2) = MatchPairE (replace re v1) (replace re v2)
  replace re (RecMatchE n t v1 v2) = RecMatchE n t (replace re v1) (replace re v2)

-- | Type class to search the number of binding names present
class HasStatus r where
  status :: (Ord e) => r e -> Status e

instance HasStatus Value where
  status (Value s _ _) = s

boundedStatus :: (Ord e, HasStatus s) => e -> s e -> Status e
boundedStatus n v = case status v of
  Neutral ns -> let nns = delete n ns in if null nns then Normal else Neutral nns
  NeutralR ns -> let nns = delete n ns in if null nns then Reductible else NeutralR nns
  unbounded -> unbounded

instance HasStatus Type where
  status TypeT = mempty
  status VoidT = mempty
  status UnitT = mempty
  status (ValueT e) = status e
  status (SigmaT n t e _) = status t <> boundedStatus n e
  status (PiT n t e _) = status t <> boundedStatus n e
  status (ChoiceT t1 t2) = status t1 <> status t2
  status (TaggedT _ t) = status t
  status (InductiveT _) = mempty -- WARING: is it neutral or Reductible due to induction? Maybe always Reductible as it can expand indefinitly

instance HasStatus Exp where
  status (TypeE t) = status t
  status (NameE n _ _) = Neutral $ singleton n
  status UnitE = mempty
  status (PairE n v1 v2 _) = status v1 <> boundedStatus n v2
  status (LambdaE n _ v _) = boundedStatus n v
  status (ApplyE l v) = Reductible <> status l <> status v
  status (InlE v) = status v
  status (InrE v) = status v
  status (MatchChoiceE v1 v2 v3) = case status v1 <> status v2 <> status v3 of -- WARNING status might depend on v1 as it might be dependent
    Normal -> Reductible -- In this case the match can be computed
    s -> s
  status (MatchPairE v1 v2) = case status v1 <> status v2 of -- WARNING status might depend on v1 as it might be dependent
    Normal -> Reductible -- In this case the match can be computed
    s -> s
  status (RecMatchE _ _ v1 v2) = status v1 <> status v2 -- the name of the function use in the recursion is not a lambda binder, thus it does not count

-- | Type class to count the number of occurences of a nome
class HasOccurences o where
  occurences :: (Eq e) => e -> o e -> Int

instance HasOccurences Value where
  occurences n (Value _ _ e) = occurences n e

instance HasOccurences Type where
  occurences _ TypeT = 0
  occurences _ VoidT = 0
  occurences _ UnitT = 0
  occurences n (ValueT e) = occurences n e
  occurences n (SigmaT _ t e _) = occurences n t + occurences n e
  occurences n (PiT _ t e _) = occurences n t + occurences n e
  occurences n (ChoiceT t1 t2) = occurences n t1 + occurences n t2
  occurences n (TaggedT _ t) = occurences n t
  occurences n (InductiveT _) = 0

instance HasOccurences Exp where
  occurences n (TypeE t) = occurences n t
  occurences n (NameE n2 _ _) = if n == n2 then 1 else 0
  occurences _ UnitE = 0
  occurences n (PairE _ v1 v2 _) = occurences n v1 + occurences n v2
  occurences n (LambdaE _ _ v _) = occurences n v
  occurences n (ApplyE l v) = occurences n l + occurences n v
  occurences n (InlE v) = occurences n v
  occurences n (InrE v) = occurences n v
  occurences n (MatchChoiceE v1 v2 v3) = occurences n v1 + occurences n v2 + occurences n v3 -- WARNING occurentces might depend on v1 as it might be dependent
  occurences n (MatchPairE v1 v2) = occurences n v1 + occurences n v2 -- WARNING occurences might depend on v1 as it might be dependent
  occurences n (RecMatchE _ _ v1 v2) = occurences n v1 + occurences n v2

isLinear :: Value e -> Bool
isLinear = undefined

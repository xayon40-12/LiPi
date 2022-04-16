{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LiPi.IR.SmartConstructors where

import Control.Monad (ap)
import LiPi.IR.Internals

data Error e s
  = Success s
  | TypeError (TypeError e)
  | ExpError (ExpError e)
  | TypeCheckError (TypeCheckError e)
  | DefinitionError (DefinitionError e)
  deriving (Show, Functor)

instance Applicative (Error e) where
  pure = Success
  (<*>) = ap

instance Monad (Error e) where
  (Success f) >>= a = a f
  (TypeError e) >>= _ = TypeError e
  (ExpError e) >>= _ = ExpError e
  (TypeCheckError e) >>= _ = TypeCheckError e
  (DefinitionError e) >>= _ = DefinitionError e

data TypeError e
  = ValueTValueNotType (Value e)
  | SigmaTSecondTypeError (Error e ())
  | PiTSecondTypeError (Error e ())
  deriving (Show)

-- | smart constractor for ValueT, takes an value that should evaluate as a type
valueT :: Value e -> Error e (Type e)
valueT v@(Value _ TypeT _ _) = Success $ ValueT v
valueT v = TypeError $ ValueTValueNotType v

-- | smart constructor for inductive types.
withInductiveType ::
  -- | Name of the type
  e ->
  -- | callback that provide the inductive type as an expression and should return the resulting type
  (Value e -> Type e) ->
  Type e
withInductiveType n f = TaggedT (n, f (neutralName n (InductiveT n) False))

-- | create a value that contains a name with neutral status
neutralName :: e -> Type e -> Bool -> Value e
neutralName n t = Value (neutral n) t (NameE n)

-- | SigmaT smart constructor that takes a binding name, the first type, a callback that produces the second type with the binding name, the linearity
sigmaT :: (Eq e) => e -> Type e -> (Value e -> Error e (Type e)) -> Bool -> Error e (Type e)
sigmaT n t1 f lin = case f (neutralName n t1 lin) of
  (Success t2) -> Success $ SigmaT (n, t1) t2 lin
  failure -> TypeError $ SigmaTSecondTypeError (() <$ failure)

-- | PiT smart constructor that takes a binding name, the input type, a callback that produces the output type with the binding name, the linearity
piT :: (Eq e) => e -> Type e -> (Value e -> Error e (Type e)) -> Bool -> Error e (Type e)
piT n t1 f lin = case f (neutralName n t1 lin) of
  (Success t2) -> Success $ PiT (n, t1) t2 lin
  failure -> TypeError $ PiTSecondTypeError (() <$ failure)

data ExpError e
  = ApplyEValueTypeInputTypeNotSame (Type e) (Type e)
  | ApplyEFirstValueNotSigmaT (Value e)
  | MatchEPairFirstValueTypeFirstInputTypeNotSame (Type e) (Type e)
  | MatchEPairSecondValueTypeSecondInputTypeNotSame (Type e) (Type e)
  | MatchEPairValuesTypesInputTypesNotSame (Type e) (Type e) (Type e) (Type e)
  | MatchEPairENotLambdaInLambda (Value e)
  | MatchEChoiceFirstValueTypeFirstInputTypeNotSame (Type e) (Type e)
  | MatchEChoiceSecondValueTypeSecondInputTypeNotSame (Type e) (Type e)
  | MatchEChoiceValuesTypesInputTypesNotSame (Type e) (Type e) (Type e) (Type e)
  | MatchEChoiceOutputTypesNotSame (Type e) (Type e)
  | MatchEChoicePairENotTwoLambdas (Value e)
  | MatchEValueNeitherPairNorChoice (Type e) (Type e)
  | LambdaLinearNotOneOccurence e Int (Value e)
  | LambdaRecNotSigmaTChoiceT e (Type e)
  | PairELinearNotOneOccurence e Int (Value e)
  | PairENotLinearForLinearValue (Value e)
  | ApplyELambdaNotLinearForLinearValue (Value e) (Value e)

instance (Show e) => Show (ExpError e) where
  show (ApplyEValueTypeInputTypeNotSame tv tl) = "The input type of the lambda in a ApplyE must be the same as the value, expected (" <> show tv <> "), provided (" <> show tl <> ")."
  show (MatchEPairFirstValueTypeFirstInputTypeNotSame tp1 tl) = "In a match expression for a pair, The input type of the lambda must be the same as the type of the first value of the pair, expected (" <> show tp1 <> "), provided (" <> show tl <> ")."
  show (MatchEPairSecondValueTypeSecondInputTypeNotSame tp2 tll) = "In a match expression for a pair, the output of the lambda must be a lambda that takes as input the same type as the second value of the pair, expected (" <> show tp2 <> "), provided (" <> show tll <> ")."
  show (MatchEPairValuesTypesInputTypesNotSame tp1 tl tp2 tll) = "In a match expression for a pair, The input type of the lambda must be the same as the type of the first value of the pair, expected (" <> show tp1 <> "), provided (" <> show tl <> "), and the output of the lambda must be a lambda that takes as input the same type as the second value of the pair, expected (" <> show tp2 <> "), provided (" <> show tll <> ")."
  show (MatchEChoiceFirstValueTypeFirstInputTypeNotSame t1 tl1) = "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but the first is not: expected (" <> show t1 <> "), provided (" <> show tl1 <> ")."
  show (MatchEChoiceSecondValueTypeSecondInputTypeNotSame t2 tl2) = "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but the second is not: expected (" <> show t2 <> "), provided (" <> show tl2 <> ")."
  show (MatchEChoiceValuesTypesInputTypesNotSame t1 tl1 t2 tl2) = "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but both are not: first expected (" <> show t1 <> ") and provided (" <> show tl1 <> "), second expected (" <> show t2 <> ") and provided (" <> show tl2 <> ")."
  show (MatchEChoiceOutputTypesNotSame t1 t2) = "The output types of the two lambdas in a match for a ChoiceT must be the same, provided (" <> show t1 <> ") and (" <> show t2 <> ")."
  show (MatchEValueNeitherPairNorChoice t1 t2) = "The values provided to a MatchE must be either a pair or a choice and respectively a lambda or a pair of lambda, provided (" <> show t1 <> ") and (" <> show t2 <> ")."

-- | Lambda smart constructor that takes a name, its type and linearity, and a callback as input. It provide the name as an expression to the callmack to use it to produce the value that the lambda would return by replacing this name with a value during application.
withLambda :: (Eq e) => e -> Type e -> (Value e -> Error e (Value e)) -> Bool -> Error e (Exp e)
withLambda n t f lin = do
  res <- f (neutralName n t lin)
  let occ = occurences n res
  if occ /= 1
    then ExpError $ LambdaLinearNotOneOccurence n occ res
    else Success $ LambdaE (n, t) res lin -- WARNING check occurences of n in f depending on lin

-- | Lambda smart constructor with recursion.
withLambdaRec ::
  forall e.
  -- | Name of the function to recurse on
  e ->
  -- | Type of the function to recurse on
  Type e ->
  -- | Name of the lambda parameter
  e ->
  -- | Type of the lambda parameter
  Type e ->
  -- | Linearity of the lambda
  Bool ->
  -- | callback that provide the name of the lambda itself as on expression and the parameter as an expression, that should return the return value of the lambda
  (Value e -> Value e -> Error e (Value e)) ->
  Error e (Exp e)
withLambdaRec recName recType@(SigmaT (_, ChoiceT _ _) sl slin) n t lin f = undefined -- TODO
  where
    recMatchE :: e -> Type e -> Value e -> (e, Value e -> Value e -> Error e (Value e)) -> (e, Value e -> Value e -> Error e (Value e)) -> Error e (Value e)
    recMatchE nr tr v (a, fara) (b, fbrb) = undefined
withLambdaRec recName recType _ _ _ _ = ExpError $ LambdaRecNotSigmaTChoiceT recName recType

-- | Pair smart constructor that take a name, its linearity and its corresponding first value, and a callback as input. It provide the name as an expression to the callback to use it to produce the value that the lambda would return by replacing this name with a value during application.
withPair :: (Eq e) => e -> Bool -> Value e -> (Value e -> Error e (Value e)) -> Error e (Exp e)
withPair n l1 v@(Value _ t _ l2) f | l2 && not l1 = ExpError $ PairENotLinearForLinearValue v
withPair n lin v@(Value _ t _ _) f = do
  res <- f (neutralName n t lin)
  let occ = occurences n res
  if occ /= 1
    then ExpError $ PairELinearNotOneOccurence n occ res
    else Success $ PairE (n, v) res lin -- WARNING check occurences of n in f depending on lin

applyE :: (Eq e) => Value e -> Value e -> Error e (Exp e)
applyE l@(Value _ (SigmaT _ _ l1) _ _) v@(Value _ _ _ l2) | l2 && not l1 = ExpError $ ApplyELambdaNotLinearForLinearValue l v
applyE l@(Value _ (SigmaT (n, t) e lin) _ _) v@(Value _ tv _ _) =
  if t == tv
    then Success $ ApplyE l v
    else ExpError $ ApplyEValueTypeInputTypeNotSame tv t
applyE l _ = ExpError $ ApplyEFirstValueNotSigmaT l

-- WARNING it should check if the value is linear (or contains itself linear values), if so the lambda should be linear accordingly
matchChoiceE :: Value e -> (e, Value e -> Error e (Value e)) -> (e, Value e -> Error e (Value e)) -> Error e (Exp e)
matchChoiceE v (a, fa) (b, fb) = undefined

-- WARNING it should check if the value is linear (or contains itself linear values), if so the lambda should be linear accordingly
matchPairE :: Value e -> (e, e) -> (Value e -> Value e -> Error e (Value e)) -> Error e (Exp e)
matchPairE v (a, b) fab = undefined

data TypeCheckError e
  = TypeENotTypeT (Type e)
  | NameEWrongType e (Type e) (Type e)
  | UnitENotUnitT (Type e)
  | PairEFirstValueTypeFirstSigmaTTypeNotSame (Type e) (Type e)
  | PairESecondValueTypeOutputSigmaTLambdaNotSame (Type e) (Type e)
  | PairENotSigmaT (Type e)
  | InlETypeLeftChoiceTTypeNotSame (Type e) (Type e)
  | InlENotChoiceT (Type e)
  | InrETypeSuccessChoiceTTypeNotSame (Type e) (Type e)
  | InrENotChoiceT (Type e)
  | PairELinearNoBinding
  | PairELinearNotOne Int e (Value e)
  | PairENotSameLinearity Bool Bool
  | LambdaENotSigmaT (Type e)
  | ApplyEResultTypeNotSame (Type e) (Type e)
  | MatchEPairResultTypeNotSame (Type e) (Type e)
  | MatchEChoiceResultTypeNotSame (Type e) (Type e)

instance (Show e) => Show (TypeCheckError e) where
  show (TypeENotTypeT t) = "Type check error: found a TypeE expression of type TypeT where a value of type (" <> show t <> ") was expected."

unless :: Bool -> TypeCheckError e -> Maybe (TypeCheckError e)
unless True _ = Nothing
unless False err = Just err

-- | Verify that the expression as the given type. If not, an information about the difference is returned.
typeCheck :: (Show e, Eq e, Ord e) => Exp e -> Type e -> Bool -> Maybe (TypeCheckError e)
typeCheck e t l = typeCheck' e t
  where
    ok = Nothing
    typeCheck' :: (Show e, Eq e, Ord e) => Exp e -> Type e -> Maybe (TypeCheckError e)
    typeCheck' (TypeE _) TypeT = ok
    typeCheck' (TypeE _) t = Just $ TypeENotTypeT t
    typeCheck' (NameE _) _ = error "The impossible happend, during type checking a NameE was provided although it should only be provided directly wrapped in a value from smart constructors, this is a bug."
    typeCheck' UnitE UnitT = ok
    typeCheck' UnitE t = Just (UnitENotUnitT t)
    typeCheck' (PairE (n, v1) v2 plin) (SigmaT (nt, t1) t2 lin) =
      if tv1 == t1
        then undefined
        else Just $ PairEFirstValueTypeFirstSigmaTTypeNotSame tv1 t1
      where
        tv2 = valueType v2
        tv1 = valueType v1
    typeCheck' PairE {} t = Just $ PairENotSigmaT t
    typeCheck' (LambdaE (n, lt) le llin) (PiT (nt, t) lp lin) = undefined -- TODO: Forbid nested name shadowing
    typeCheck' LambdaE {} t = Just $ LambdaENotSigmaT t
    typeCheck' (ApplyE (Value _ (SigmaT (_, _) o _) _ _) _) t = undefined -- the o
    typeCheck' (ApplyE (Value _ t _ _) _) _ = error $ "The impossible happened, during type checking an ApplyE with a non SigmaT first value was provided (" <> show t <> "), this i a bug."
    typeCheck' (InlE (Value _ t _ _)) (ChoiceT tl _) = unless (t == tl) $ InlETypeLeftChoiceTTypeNotSame t tl
    typeCheck' (InlE _) t = Just $ InlENotChoiceT t
    typeCheck' (InrE (Value _ t _ _)) (ChoiceT _ tr) = unless (t == tr) $ InrETypeSuccessChoiceTTypeNotSame t tr
    typeCheck' (InrE _) t = Just $ InrENotChoiceT t
    typeCheck' (RecMatchE n rt v lr) t = undefined

-- | Create a value from a type and an expression if it typechecks
newValue :: (Eq e, Ord e, Show e) => Exp e -> Type e -> Bool -> Error e (Value e)
newValue e t l = case typeCheck e t l of
  -- WARNING: every constructed expressions that contains linear values must be linear as well
  Nothing -> Success $ Value (status e) t e l
  Just err -> TypeCheckError err

valueType :: Value e -> Type e
valueType (Value _ t _ _) = t

isLinear :: Value e -> Bool
isLinear (Value _ _ _ l) = l

data DefinitionError e = DefinitionValueNotNormalNonLinear e (Value e)

instance Show e => Show (DefinitionError e) where
  show (DefinitionValueNotNormalNonLinear name v) = "In the definition of \"" <> show name <> ", the value (" <> show v <> ") should be in normal form and not linear. Only top level values can be definitions."

-- | Create a definition from a name and a Value
newDefinition :: (Show e) => e -> Value e -> Error e (Definition e)
newDefinition name (Value Normal t e False) = Success $ Definition name t e
newDefinition name v = DefinitionError $ DefinitionValueNotNormalNonLinear name v

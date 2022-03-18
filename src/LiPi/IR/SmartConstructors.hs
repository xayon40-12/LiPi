module LiPi.IR.SmartConstructors where

import LiPi.IR.Internals

data TypeError e
  = SigmaTLambdaReturnTypeNotType (Type e)
  | SigmaTLambdaInputTypeNotSame (Type e) (Type e)
  | SigmaTLambdaInputTypeNotSameReturnTypeNotType (Type e) (Type e) (Type e)
  | PiTLambdaReturnTypeNotType (Type e)
  | PiTLambdaInputTypeNotSame (Type e) (Type e)
  | PiTLambdaInputTypeNotSameReturnTypeNotType (Type e) (Type e) (Type e)
  | ChoiceTFirstTypeNotType (Type e)
  | ChoiceTSecondTypeNotType (Type e)
  | ChoiceTBothTypesNotTypes (Type e) (Type e)

instance (Show e) => Show (TypeError e) where
  show (SigmaTLambdaReturnTypeNotType t) = "The return type of the lambda in a SigmaT must be a valid Type, found: (" <> show t <> ")."
  show (SigmaTLambdaInputTypeNotSame t tl) = "The input type of the lambda in a SigmaT must be the same type a the first type of this SigmaT, expected: (" <> show t <> "), provided (" <> show tl <> ")."
  show (SigmaTLambdaInputTypeNotSameReturnTypeNotType t tl tv) = "The input type of the lambda in a SigmaT must be the same type a the first type of this SigmaT, expected: (" <> show t <> "), provided (" <> show tl <> "). The return type of the lambda in a SigmaT must be a valid Type, found: (" <> show t <> ")."
  show (PiTLambdaReturnTypeNotType t) = "The return type of the lambda in a PiT must be a valid Type, found: (" <> show t <> ")."
  show (PiTLambdaInputTypeNotSame t tl) = "The input type of the lambda in a PiT must be the same type a the first type of this PiT, expected: (" <> show t <> "), provided (" <> show tl <> ")."
  show (PiTLambdaInputTypeNotSameReturnTypeNotType t tl tv) = "The input type of the lambda in a PiT must be the same type a the first type of this PiT, expected: (" <> show t <> "), provided (" <> show tl <> "). The return type of the lambda in a PiT must be a valid Type, found: (" <> show t <> ")."
  show (ChoiceTFirstTypeNotType t) = "Both types in a ChoiceT must be valid types but the first is not: (" <> show t <> ")."
  show (ChoiceTSecondTypeNotType t) = "Both types in a ChoiceT must be valid types but the second is not: (" <> show t <> ")."
  show (ChoiceTBothTypesNotTypes t1 t2) = "Both types in a ChoiceT must be valid types but both are not: first (" <> show t1 <> "), second (" <> show t2 <> ")."

-- | smart constructor for inductive types.
withInductiveType ::
  -- | Name of the type
  e ->
  -- | callback that provide the inductive type as an expression and should return the resulting type
  (Exp e -> Type e) ->
  Type e
withInductiveType n f = TaggedT n (f (NameE (Name n (InductiveT n))))

isSigmaT, isChoiceT :: Type e -> Bool
isSigmaT (SigmaT _ _) = True
isSigmaT _ = False
isChoiceT (ChoiceT _ _) = True
isChoiceT _ = False

sigmaT :: (Eq e, Show e) => Type e -> Lambda e -> Either (TypeError e) (Type e)
sigmaT t l@(Lambda _ tl (Value _ tv _)) = case (t == tl, isType tv) of
  (True, True) -> Right $ SigmaT t l
  (False, True) -> Left $ SigmaTLambdaInputTypeNotSame t tl
  (True, False) -> Left $ SigmaTLambdaReturnTypeNotType tv
  (False, False) -> Left $ SigmaTLambdaInputTypeNotSameReturnTypeNotType t tl tv

piT :: (Eq e, Show e) => Type e -> Lambda e -> Bool -> Either (TypeError e) (Type e)
piT t l@(Lambda _ tl (Value _ tv _)) linear = case (t == tl, isType tv) of
  (True, True) -> Right $ PiT t l linear
  (False, True) -> Left $ PiTLambdaInputTypeNotSame t tl
  (True, False) -> Left $ PiTLambdaReturnTypeNotType tv
  (False, False) -> Left $ PiTLambdaInputTypeNotSameReturnTypeNotType t tl tv

choiceT :: (Show e) => Type e -> Type e -> Either (TypeError e) (Type e)
choiceT t1 t2 = case (isType t1, isType t2) of
  (True, True) -> Right $ ChoiceT t1 t2
  (False, True) -> Left $ ChoiceTFirstTypeNotType t1
  (True, False) -> Left $ ChoiceTSecondTypeNotType t2
  (False, False) -> Left $ ChoiceTBothTypesNotTypes t1 t2

isType :: Type e -> Bool
isType TypeT = False -- The type of types is not an element of itself
isType VoidT = True
isType UnitT = True
isType (SigmaT t1 (Lambda _ _ (Value _ t2 _))) = isType t1 && isType t2
isType (PiT t1 (Lambda _ _ (Value _ t2 _)) _) = isType t1 && isType t2
isType (ChoiceT t1 t2) = isType t1 && isType t2
isType (TaggedT _ t) = isType t
isType (InductiveT _) = True

-- | Lambda smart constructor that take a name and a callback as input. It provide the name as an expression to the callmack to use it to produce the value that the lambda would return by replacing this name with a value during application.
withLambda :: (Eq e, Ord e) => Name e -> (Exp e -> Value e) -> Lambda e
withLambda n@(Name name t) f = Lambda (Just name) t (f (NameE n))

-- | Lambo smart constructor for lambdas that do not depend on their parameter (the input type is still needed)
constantLambda :: Type e -> Value e -> Lambda e
constantLambda = Lambda Nothing

-- | Lambda smart constructor with recursion.
withLambdaRec ::
  (Eq e, Ord e) =>
  -- | Name of the function to recurse on
  Name e ->
  -- | Name of the lambda parameter
  Name e ->
  -- | callback that provide a lambda to create a 'RecE' with the name already provided and the parameter as an expression, that should return the return value of the lambda
  ((Value e -> Value e -> Exp e) -> Exp e -> Value e) ->
  Lambda e
withLambdaRec recName n@(Name name t) f = Lambda (Just name) t (f (RecE recName) (NameE n))

data ExpError e
  = ApplyEValueTypeInputTypeNotSame (Type e) (Type e)
  | MatchEPairFirstValueTypeFirstInputTypeNotSame (Type e) (Type e)
  | MatchEPairSecondValueTypeSecondInputTypeNotSame (Type e) (Type e)
  | MatchEPairValuesTypesInputTypesNotSame (Type e) (Type e) (Type e) (Type e)
  | MatchEChoiceFirstValueTypeFirstInputTypeNotSame (Type e) (Type e)
  | MatchEChoiceSecondValueTypeSecondInputTypeNotSame (Type e) (Type e)
  | MatchEChoiceValuesTypesInputTypesNotSame (Type e) (Type e) (Type e) (Type e)
  | MatchEValueNeitherPairNorChoice (Type e) (Type e)

instance (Show e) => Show (ExpError e) where
  show (ApplyEValueTypeInputTypeNotSame tv tl) = "The input type of the lambda in a ApplyE must be the same as the value, expected (" <> show tv <> "), provided (" <> show tl <> ")."
  show (MatchEPairFirstValueTypeFirstInputTypeNotSame tp1 tl) = "In a match expression for a pair, The input type of the lambda must be the same as the type of the first value of the pair, expected (" <> show tp1 <> "), provided (" <> show tl <> ")."
  show (MatchEPairSecondValueTypeSecondInputTypeNotSame tp2 tll) = "In a match expression for a pair, the output of the lambda must be a lambda that takes as input the same type as the second value of the pair, expected (" <> show tp2 <> "), provided (" <> show tll <> ")."
  show (MatchEPairValuesTypesInputTypesNotSame tp1 tl tp2 tll) = "In a match expression for a pair, The input type of the lambda must be the same as the type of the first value of the pair, expected (" <> show tp1 <> "), provided (" <> show tl <> "), and the output of the lambda must be a lambda that takes as input the same type as the second value of the pair, expected (" <> show tp2 <> "), provided (" <> show tll <> ")."
  show (MatchEChoiceFirstValueTypeFirstInputTypeNotSame t1 tl1) = "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but the first is not: expected (" <> show t1 <> "), provided (" <> show tl1 <> ")."
  show (MatchEChoiceSecondValueTypeSecondInputTypeNotSame t2 tl2) = "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but the second is not: expected (" <> show t2 <> "), provided (" <> show tl2 <> ")."
  show (MatchEChoiceValuesTypesInputTypesNotSame t1 tl1 t2 tl2) = "In a match expression for a choice, Both types of the ChoiceT must be the same as types taken by the lambda to extract it, but both are not: first expected (" <> show t1 <> ") and provided (" <> show tl1 <> "), second expected (" <> show t2 <> ") and provided (" <> show tl2 <> ")."
  show (MatchEValueNeitherPairNorChoice t1 t2) = "The values provided to a MatchE must be either a pair or a choice and respectively a lambda or a pair of lambda, provided (" <> show t1 <> ") and (" <> show t2 <> ")."

applyE :: (Show e, Eq e) => Lambda e -> Value e -> Either (ExpError e) (Exp e)
applyE l@(Lambda Nothing _ _) v = Right $ ApplyE l v
applyE l@(Lambda _ tl _) v@(Value _ tv _) =
  if tv == tl
    then Right $ ApplyE l v
    else Left $ ApplyEValueTypeInputTypeNotSame tv tl

matchE :: (Show e, Eq e) => Value e -> Value e -> Either (ExpError e) (Exp e)
matchE v@(Value _ _ (PairE p1@(Value _ tp1 _) p2@(Value _ tp2 _))) l@(Value _ _ (LambdaE (Lambda _ tl (Value _ tll _)))) = case (tp1 == tl, tp2 == tll) of
  (True, True) -> Right $ MatchE v l
  (False, True) -> Left $ MatchEPairFirstValueTypeFirstInputTypeNotSame tp1 tl
  (True, False) -> Left $ MatchEPairSecondValueTypeSecondInputTypeNotSame tp2 tll
  (False, False) -> Left $ MatchEPairValuesTypesInputTypesNotSame tp1 tl tp2 tll
matchE v1@(Value _ (ChoiceT t1 t2) _) v2@(Value _ _ (PairE (Value _ _ (LambdaE (Lambda _ tl1 _))) (Value _ _ (LambdaE (Lambda _ tl2 _))))) = case (t1 == tl1, t2 == tl2) of
  (True, True) -> Right $ MatchE v1 v2
  (False, True) -> Left $ MatchEChoiceFirstValueTypeFirstInputTypeNotSame t1 tl1
  (True, False) -> Left $ MatchEChoiceSecondValueTypeSecondInputTypeNotSame t2 tl2
  (False, False) -> Left $ MatchEChoiceValuesTypesInputTypesNotSame t1 tl1 t2 tl2
matchE (Value _ t1 _) (Value _ t2 _) = Left $ MatchEValueNeitherPairNorChoice t1 t2

data TypeCheckError e
  = TypeNotType (Type e)
  | TypeENotTypeT (Type e)

instance (Show e) => Show (TypeCheckError e) where
  show (TypeNotType t) = "The type (" <> show t <> ") is not actually a type."
  show (TypeENotTypeT t) = "Type check error: found a TypeE expression of type TypeT where a type (" <> show t <> ") was expected."

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
    ok = Nothing
    typeCheck' :: (Eq e, Ord e) => Exp e -> Type e -> Maybe Error
    typeCheck' (TypeE _) TypeT = ok
    typeCheck' (TypeE _) t = Just "" -- TypeENotTypeT t
    typeCheck' (NameE (Name _ t1)) t2 = unless (t1 == t2) ""
    typeCheck' UnitE UnitT = ok
    typeCheck' UnitE _ = Just ""
    typeCheck' (PairE v1 v2) (SigmaT t l) = unless (valueType v1 == t && case apply l v1 of (Value _ TypeT (TypeE t2)) -> valueType v2 == t2; _ -> False) ""
    typeCheck' (PairE _ _) _ = Just ""
    typeCheck' (LambdaE l) _ = undefined -- TODO: Forbid nested name shadowing
    typeCheck' (ApplyE l v) _ = undefined -- TODO If the value 'l' is linear, the lambda must have a binding name
    typeCheck' (InlE (Value _ t _)) (ChoiceT tl _) = unless (t == tl) ""
    typeCheck' (InlE (Value _ t _)) _ = Just ""
    typeCheck' (InrE (Value _ t _)) (ChoiceT _ tr) = unless (t == tr) ""
    typeCheck' (InrE (Value _ t _)) _ = Just ""
    typeCheck' (MatchE v l) _ = undefined
    typeCheck' (RecE n v l) _ = undefined

-- | Create a value from a type and an expression if it typechecks
newValue :: (Eq e, Ord e, Show e) => Type e -> Exp e -> Either Error (Value e)
newValue t e = case typeCheck e t of
  Nothing -> Right $ Value (status e) t e
  Just err -> Left err

valueType :: Value e -> Type e
valueType (Value _ t _) = t

data DefinitionError e = DefinitionValueNotNormal e (Value e)

instance Show e => Show (DefinitionError e) where
  show (DefinitionValueNotNormal name v) = "In the definition of \"" <> show name <> ", the value (" <> show v <> ") is not in normal form. Only top level values can be definitions."

-- | Create a definition from a name and a Value
newDefinition :: (Show e) => e -> Value e -> Either (DefinitionError e) (Definition e)
newDefinition name (Value Normal t e) = Right $ Definition name t e
newDefinition name v = Left $ DefinitionValueNotNormal name v

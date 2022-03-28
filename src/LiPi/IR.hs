module LiPi.IR (Type (TypeT, VoidT, UnitT, ChoiceT, TaggedT), withInductiveType, sigmaT, piT, withLambda, withLambdaRec, Exp (TypeE, UnitE, InlE, InrE), withPair, applyE, matchChoiceE, matchPairE, Value (), newValue, newDefinition) where

import LiPi.IR.Internals
import LiPi.IR.SmartConstructors

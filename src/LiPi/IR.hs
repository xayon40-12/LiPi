module LiPi.IR (Type (TypeT, VoidT, UnitT, TaggedT), withInductiveType, sigmaT, piT, choiceT, Lambda (), withLambda, withLambdaRec, Name (..), Exp (TypeE, UnitE, PairE, LambdaE, InlE, InrE), applyE, matchE, Value (), newValue) where

import LiPi.IR.Internals
import LiPi.IR.SmartConstructors

module LiPi.IR (Type (TypeT, VoidT, UnitT, TaggedT), withInductiveType, sigmaT, piT, choiceT, Lambda (), withLambda, constantLambda, withLambdaRec, Name (Name), Exp (TypeE, UnitE, PairE, LambdaE, InlE, InrE), applyE, matchE, Value (), newValue, newDefinition) where

import LiPi.IR.Internals
import LiPi.IR.SmartConstructors

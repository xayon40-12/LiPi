module LiPi.IR (Type (TypeT, VoidT, UnitT, TaggedT), withInductiveType, sigmaT, piT, choiceT, Lambda (), withLambda, constantLambda, withLambdaRec, Exp (TypeE, UnitE, LambdaE, InlE, InrE), newPair, withPair, applyE, matchE, Value (), newValue, newDefinition) where

import LiPi.IR.Internals
import LiPi.IR.SmartConstructors

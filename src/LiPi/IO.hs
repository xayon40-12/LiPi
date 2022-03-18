module LiPi.IO (withIO) where

import LiPi.IR (Exp (LambdaE), Type (TaggedT, VoidT))
import LiPi.IR.Internals (Definition (Definition), Lambda (Lambda), Status (Normal), Type (PiT), Value (Value), apply)

data VIOError e = IODefinitionNotVIO2VIO e e (Type e)

vio :: e -> Type e
vio name = TaggedT name VoidT

ioaction :: e -> Type e
ioaction name = PiT vioType cvioType True
  where
    vioType = vio name
    vioValue = Value Normal vioType undefined
    cvioType = Lambda Nothing vioType vioValue

instance Show e => Show (VIOError e) where
  show (IODefinitionNotVIO2VIO io name t) = "In a definition of an IO action \"" <> show name <> "\": an IO action (as what is unsually called \"main\") must be of type (" <> show (ioaction io) <> "), provided (" <> show t <> ")."

interpretIO = undefined

withIO :: (Eq e, Ord e) => e -> Definition e -> Either (VIOError e) (IO ())
withIO io (Definition name t (LambdaE l)) | t == ioaction io = Right $ interpretIO $ apply l vioValue
  where
    vioValue = Value Normal (vio io) undefined
withIO io (Definition name t _) = Left $ IODefinitionNotVIO2VIO io name t

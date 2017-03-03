module linear.Data.ByteString where

open import Data.String.Base
open import IO.Primitive

{-# FOREIGN GHC import qualified Data.ByteString #-}
{-# FOREIGN GHC import qualified Data.Text       #-}

postulate
  RByteString : Set
  RreadFileBS : String → IO RByteString

{-# COMPILE GHC RByteString = type Data.ByteString.ByteString             #-}
{-# COMPILE GHC RreadFileBS = Data.ByteString.readFile . Data.Text.unpack #-}

ByteString = RByteString

readFileBS : String → IO ByteString
readFileBS = RreadFileBS

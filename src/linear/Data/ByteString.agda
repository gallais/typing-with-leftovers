module linear.Data.ByteString where

open import Data.String.Base
open import IO.Primitive

{-# IMPORT Data.ByteString #-}
{-# IMPORT Data.Text       #-}

postulate
  ByteString : Set
  readFileBS : String → IO ByteString

{-# COMPILED_TYPE ByteString Data.ByteString.ByteString               #-}
{-# COMPILED readFileBS (Data.ByteString.readFile . Data.Text.unpack) #-}

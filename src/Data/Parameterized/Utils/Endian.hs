{-|
Description: A common location for defining multi-byte value ordering.
Copyright        : (c) Galois, Inc 2019
-}

module Data.Parameterized.Utils.Endian where

-- | Determines the composition of smaller numeric values into larger values.
--
--  BigEndian = most significant values in the lowest index location / first
--  LittleEndian = least significant values in the lowest index location / first
--
--  Value: 0x01020304
--  BigEndian    = [ 0x01, 0x02, 0x03, 0x04 ]
--  LittleEndian = [ 0x04, 0x03, 0x02, 0x01 ]
data Endian = LittleEndian | BigEndian deriving (Eq,Show,Ord)

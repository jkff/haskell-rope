{-# LANGUAGE TypeFamilies, FlexibleInstances #-}
module Data.Rope (
        Rope, 
        StringLike(..),
        pack,
        unpack
) where

import Prelude hiding (splitAt)

import Test.QuickCheck

import Data.Word
import qualified Data.ByteString.Char8 as BC

class StringLike a where
    type Elem a :: *

    size :: a -> Int
    empty :: a
    (.<) :: Elem a -> a -> a
    (>.) :: a -> Elem a -> a
    (<>) :: a -> a -> a
    splitAt :: Int -> a -> (a,a)
    decomposeAt :: Int -> a -> (a,Elem a,a)

instance StringLike BC.ByteString where
  type Elem BC.ByteString = Char

  size = BC.length
  empty = BC.empty
  (.<) = BC.cons
  (>.) = BC.snoc
  (<>) = BC.append
  splitAt = BC.splitAt
  decomposeAt i b = (BC.take i b, b `BC.index` i, BC.drop (i+1) b)

data Rope a = Leaf  { chunkSize :: Int, block :: a }
            | Two   { chunkSize :: Int, h :: Int, totalSize :: Int, childA :: Rope a, childB :: Rope a }
            | Three { chunkSize :: Int, h :: Int, totalSize :: Int, childA :: Rope a, childB :: Rope a, childC :: Rope a }
    deriving (Show)

height :: Rope a -> Int
height Leaf {}    = 0
height Two  {h=h} = h
height Three{h=h} = h

defaultChunkSize :: Int
defaultChunkSize = 64

pack :: (StringLike a) => Int -> a -> Rope a
pack cs s | size s < 2*cs = Leaf cs s
               | otherwise = let (a,b) = splitAt cs s in pack cs a <> pack cs b

unpack :: (StringLike a) => Rope a -> a
unpack (Leaf  _   a)     = a
unpack (Two   _ _ _ a b)   = unpack a <> unpack b
unpack (Three _ _ _ a b c) = unpack a <> unpack b <> unpack c

two :: (StringLike a) => Rope a -> Rope a -> Rope a
two ra rb 
    | height ra /= height rb = error $ "non-equal heights in two: " ++ show (height ra, height rb)
    | chunkSize ra /= chunkSize rb = error $ "non-equal chunk sizes in two: " ++ show (chunkSize ra, chunkSize rb)
    | otherwise              = Two { chunkSize = chunkSize ra, h = height ra + 1, totalSize = size ra + size rb, childA = ra, childB = rb } 

three :: (StringLike a) => Rope a -> Rope a -> Rope a -> Rope a
three ra rb rc 
    | height ra /= height rb || height rb /= height rc = error $ "non-equal heights in three: " ++ show (height ra, height rb, height rc)
    | chunkSize ra /= chunkSize rb || chunkSize rb /= chunkSize rc = error $ "non-equal chunk sizes in three: " ++ show (chunkSize ra, chunkSize rb, chunkSize rc)
    | otherwise = Three { chunkSize = chunkSize ra, h = height ra + 1, totalSize = size ra + size rb + size rc, childA = ra, childB = rb, childC = rc } 

isUnderflownBlock :: (StringLike a) => Rope a -> Bool
isUnderflownBlock (Leaf cs a) = size a < cs
isUnderflownBlock _           = False

reblock :: (StringLike a) => Rope a -> Rope a -> Rope a
reblock (Leaf cs a) (Leaf _ b) = pack cs (a <> b)

instance (StringLike a) => StringLike (Rope a) where
    type Elem (Rope a) = Elem a

    size (Leaf _ a) = size a
    size r          = totalSize r

    empty = Leaf defaultChunkSize empty

    c .< r = pack (chunkSize r) (c .< empty) <> r   
    r >. c = r <> pack (chunkSize r) (empty >. c)

    ra <> rb = case (height ra - height rb) of
      0 -> if (isUnderflownBlock ra || isUnderflownBlock rb) 
           then reblock ra rb 
           else two ra rb
      1 -> case ra of
        Two   _ _ _ aa ab    -> three aa ab rb
        Three _ _ _ aa ab ac -> two (two aa ab) (two ac rb)
      -1 -> case rb of
        Two   _ _ _ ba bb    -> three ra ba bb
        Three _ _ _ ba bb bc -> two (two ra ba) (two bb bc)
      x | x > 0 -> case ra of
        Two   _ _ _  aa ab    -> aa <> (ab <> rb)
        Three _ _ _ aa ab ac -> (two aa ab) <> (ac <> rb)
        | x < 0 -> case rb of
        Two   _ _ _ ba bb    -> (ra <> ba) <> bb
        Three _ _ _ ba bb bc -> (ra <> ba) <> (two bb bc)

    splitAt i (Leaf cs c) = let (ca,cb) = splitAt i c in (pack cs ca, pack cs cb)
    splitAt i (Two _ _ _ a b) 
        | i < sa      = let (aa,ab) = splitAt i      a in (aa, ab <> b)
        | otherwise   = let (ba,bb) = splitAt (i-sa) b in (a <> ba, bb)
      where sa = size a
    splitAt i (Three _ _ _ a b c)
        | i < sa      = let (aa,ab) = splitAt i         a in (aa, ab <> b <> c)
        | i < sa + sb = let (ba,bb) = splitAt (i-sa)    b in (a <> ba, bb <> c)
        | otherwise   = let (ca,cb) = splitAt (i-sa-sb) c in (a <> b <> ca, cb)
      where (sa,sb) = (size a,size b)

    decomposeAt i r 
        | i >= size r || i < 0 = error $ "Index " ++ show i ++ " out of bounds [0," ++ show (size r) ++ ")"
    decomposeAt i (Leaf cs a) = let (aa,c,ab) = decomposeAt i a in (pack cs aa, c, pack cs ab)
    decomposeAt i (Two _ _ _ a b)
        | i < sa    = let (aa,x,ab) = decomposeAt i      a in (aa, x, ab <> b)
        | otherwise = let (ba,x,bb) = decomposeAt (i-sa) b in (a <> ba, x, bb)
      where sa = size a
    decomposeAt i (Three _ _ _ a b c)
        | i < sa    = let (aa,x,ab) = decomposeAt i         a in (aa, x, ab <> b <> c)
        | i < sa+sb = let (ba,x,bb) = decomposeAt (i-sa)    b in (a <> ba, x, bb <> c)
        | otherwise = let (ca,x,cb) = decomposeAt (i-sa-sb) c in (a <> b <> ca, x, cb)
      where (sa,sb) = (size a,size b)

instance Arbitrary (Rope BC.ByteString) where
  arbitrary = (pack 4 . BC.pack) `fmap` listOf (elements "abc")
  shrink a = []

prop_size :: Rope BC.ByteString -> Rope BC.ByteString -> Bool
prop_size a b = size (a <> b) == size a + size b

prop_appendAssoc :: Rope BC.ByteString -> Rope BC.ByteString -> Rope BC.ByteString -> Bool
prop_appendAssoc a b c = unpack (a <> (b <> c)) == unpack ((a <> b) <> c)

prop_splitAt :: Int -> Rope BC.ByteString -> Bool
prop_splitAt i r = let (a,b) = splitAt i r in (unpack r == unpack (a <> b))

prop_decomposeAt :: Rope BC.ByteString -> Property
prop_decomposeAt r = (size r > 0) ==> forAll (elements [0..size r-1]) $ \i -> let (a,x,b) = decomposeAt i r in (unpack r == unpack (a <> (x .< empty) <> b))

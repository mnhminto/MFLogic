{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./MFLogic/MFLogicSign.hs
Description :  Signatures for MFLogic, as extension of CASL signatures
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

Signatures for MFLogic, as extension of CASL signatures.
Signatures also serve as local environments for the basic static analysis

-}

module MFLogic.MFLogicSign where
import MFLogic.AS_MFLogic
import CASL.Sign
import CASL.AS_Basic_CASL (SORT)
import qualified CASL.Morphism as Mor

import Common.Doc (Doc, sepByCommas)
import Common.DocUtils (Pretty(..), printMap, pairElems)
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Data.Data
import qualified Data.Map as Map

{- |
   MFMap| is going to be used as the |m| parameter.
   We follow the convention used (apparently) in |CASL.Morphism| that
   symbols outside the domain of these |Map|s are considered as mapped
 to themselves.
-}

data MFMap = MFMap
  {
    attr_MapMor :: Mor.Op_map
  , actn_MapMor :: Mor.Pred_map
  } deriving (Eq, Ord, Show)

instance Pretty MFMap where pretty = prettyMFMap

-- | pretty print of MFlogic extended morphism map

prettyMFMap :: MFMap -> Doc
prettyMFMap = printMap id sepByCommas pairElems . mfMapToSymbMapAux

-- | convert MFLogic map to auxilary symbol map

mfMapToSymbMapAux :: MFMap -> Mor.SymbolMap
mfMapToSymbMapAux mor = let
    attrSymMap = Map.foldWithKey
      ( \ (i, t) (i', _k) -> Map.insert (idToOpSymbol i t) (idToOpSymbol i' t)
      )
      Map.empty $ attr_MapMor mor
    actnSymMap = Map.foldWithKey
      ( \ (i, t) i' -> Map.insert (idToPredSymbol i t) (idToPredSymbol i' t)
      )
      Map.empty $ actn_MapMor mor
  in Map.union attrSymMap actnSymMap

{-|
MFsign is defined in StatAna.hs
SignExtMF is the extended part of the signature only
-}

data SignExtMF = SignExtMF
  { attrSig :: OpMap   -- attrSig
  , actnSig :: PredMap
  } deriving (Show, Eq, Ord, Typeable, Data)

-- | Empty MFLogic extended signature

emptyMFLogicSign :: SignExtMF
emptyMFLogicSign = SignExtMF MapSet.empty MapSet.empty

-- | Add two extended MFLogic signatures

addMFLogicSign :: SignExtMF -> SignExtMF -> SignExtMF
addMFLogicSign a b = SignExtMF
  { attrSig = addOpMapSet (attrSig a) $ attrSig b
  , actnSig = addMapSet (actnSig a) $ actnSig b }

-- | Intersaction of two extended MFLogic signatures

interMFLogicSign :: SignExtMF -> SignExtMF -> SignExtMF
interMFLogicSign a b = a
  { attrSig = interOpMapSet (attrSig a) $ attrSig b
  , actnSig = interMapSet (actnSig a) $ actnSig b }

-- | Difference between two extended MFLogic signatures
diffMFLogicSign :: SignExtMF -> SignExtMF -> SignExtMF
diffMFLogicSign a b = a
  { attrSig = diffOpMapSet (attrSig a) $ attrSig b
  , actnSig = diffMapSet (actnSig a) $ actnSig b }

{- | Returns true is Extended MF Signature a is a sub signature of
Extended MF Signature of b (b contains a)
-}

isSubMFLogicSign :: SignExtMF -> SignExtMF -> Bool
isSubMFLogicSign a b =
    isSubOpMap (attrSig a) (attrSig b)
    && isSubMap (actnSig a) (actnSig b)

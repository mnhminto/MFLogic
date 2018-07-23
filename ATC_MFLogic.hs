{-# OPTIONS -w -O0 #-}
{- |
Module      :  MFLogic/ATC_MFLogic.der.hs
Description :  generated ShATermConvertible instances
Copyright   :  (c) DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(derive Typeable instances)

Automatic derivation of instances via DrIFT-rule ShATermConvertible
  for the type(s):
'MFLogic.AS_MFLogic.MF_BASIC_ITEM'
'MFLogic.AS_MFLogic.MF_SIG_ITEM'
'MFLogic.AS_MFLogic.MF_FORMULA'
'MFLogic.MFLogicSign.MFMap'
'MFLogic.MFLogicSign.SignExtMF'
'MFLogic.MFSymbol.MFSymbType'
'MFLogic.MFSymbol.MFSymbol'
-}

{-
Generated by 'genRules' (automatic rule generation for DrIFT). Don't touch!!
  dependency files:
MFLogic/AS_MFLogic.hs
MFLogic/MFLogicSign.hs
MFLogic/MFSymbol.hs
-}

module MFLogic.ATC_MFLogic () where

import ATerm.Lib
import CASL.AS_Basic_CASL
import CASL.AS_Basic_CASL (SORT)
import CASL.ATC_CASL
import CASL.Sign
import Common.AS_Annotation
import Common.Doc
import Common.Doc (Doc, sepByCommas)
import Common.DocUtils
import Common.DocUtils (Pretty(..), printMap, pairElems)
import Common.Id
import Common.Keywords
import Data.Data
import Data.Either (partitionEithers)
import MFLogic.AS_MFLogic
import MFLogic.MFLogicSign
import MFLogic.MFSymbol
import qualified CASL.Morphism as Mor
import qualified CASL.Sign as CASLSign
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set

{-! for MFLogic.AS_MFLogic.MF_BASIC_ITEM derive : ShATermConvertible !-}
{-! for MFLogic.AS_MFLogic.MF_SIG_ITEM derive : ShATermConvertible !-}
{-! for MFLogic.AS_MFLogic.MF_FORMULA derive : ShATermConvertible !-}
{-! for MFLogic.MFLogicSign.MFMap derive : ShATermConvertible !-}
{-! for MFLogic.MFLogicSign.SignExtMF derive : ShATermConvertible !-}
{-! for MFLogic.MFSymbol.MFSymbType derive : ShATermConvertible !-}
{-! for MFLogic.MFSymbol.MFSymbol derive : ShATermConvertible !-}

-- Generated by DrIFT, look but don't touch!

instance ShATermConvertible MF_FORMULA where
  toShATermAux att0 xv = case xv of
    FormX a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "FormX" [a', b'] []) att2
    FormF a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "FormF" [a', b'] []) att2
    Action a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "Action" [a', b', c'] []) att3
    BEG a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "BEG" [a'] []) att1
    AttrSel a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "AttrSel" [a', b', c'] []) att3
    TermX a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "TermX" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "FormX" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, FormX a' b') }}
    ShAAppl "FormF" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, FormF a' b') }}
    ShAAppl "Action" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, Action a' b' c') }}}
    ShAAppl "BEG" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, BEG a') }
    ShAAppl "AttrSel" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, AttrSel a' b' c') }}}
    ShAAppl "TermX" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, TermX a' b') }}
    u -> fromShATermError "MF_FORMULA" u

instance ShATermConvertible MF_SIG_ITEM where
  toShATermAux att0 xv = case xv of
    Att_items a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Att_items" [a', b'] []) att2
    Actn_items a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Actn_items" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Att_items" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Att_items a' b') }}
    ShAAppl "Actn_items" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Actn_items a' b') }}
    u -> fromShATermError "MF_SIG_ITEM" u

instance ShATermConvertible MF_BASIC_ITEM where
  toShATermAux att0 xv = case xv of
    Unused_MF_BASIC_ITEM a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "Unused_MF_BASIC_ITEM" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Unused_MF_BASIC_ITEM" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, Unused_MF_BASIC_ITEM a') }
    u -> fromShATermError "MF_BASIC_ITEM" u

instance ShATermConvertible MFMap where
  toShATermAux att0 xv = case xv of
    MFMap a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "MFMap" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "MFMap" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, MFMap a' b') }}
    u -> fromShATermError "MFMap" u

instance ShATermConvertible SignExtMF where
  toShATermAux att0 xv = case xv of
    SignExtMF a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "SignExtMF" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "SignExtMF" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, SignExtMF a' b') }}
    u -> fromShATermError "SignExtMF" u

instance ShATermConvertible MFSymbol where
  toShATermAux att0 xv = case xv of
    GenSymbol a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "GenSymbol" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "GenSymbol" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, GenSymbol a' b') }}
    u -> fromShATermError "MFSymbol" u

instance ShATermConvertible MFSymbType where
  toShATermAux att0 xv = case xv of
    CASLSymbType a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "CASLSymbType" [a'] []) att1
    AttrAsItemType a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "AttrAsItemType" [a'] []) att1
    ActnAsItemType a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "ActnAsItemType" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "CASLSymbType" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, CASLSymbType a') }
    ShAAppl "AttrAsItemType" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, AttrAsItemType a') }
    ShAAppl "ActnAsItemType" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, ActnAsItemType a') }
    u -> fromShATermError "MFSymbType" u

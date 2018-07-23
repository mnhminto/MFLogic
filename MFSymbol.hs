{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  ./MFLogic/MFSymbol.hs
Description :  symbols for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

MFLogic Symbols is extension of CASL Symbols
added Attr and Actn symbols
-}

module MFLogic.MFSymbol where
import MFLogic.MFLogicSign
import Common.Keywords
import Common.Id
import Common.DocUtils
import Common.Doc
-- import qualified CASL.Morphism as Mor
import qualified CASL.Sign as CASLSign
import CASL.AS_Basic_CASL
import qualified Common.Lib.MapSet as MapSet
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Data
import Data.Either (partitionEithers)

{-
data GenSymbol symbType = GenSymbol
   { symName :: Id
   , symbType :: symbType
   }
   deriving (Show, Eq, Ord, Typeable, Data)
-}

instance GetRange MFSymbol where
    getRange = getRange . symName

data MFSymbType
  = CASLSymbType CASLSign.SymbType
   | AttrAsItemType CASLSign.OpType
  {- since symbols do not speak about totality, the totality
     information in OpType has to be ignored -}
   | ActnAsItemType CASLSign.PredType
   deriving (Show, Eq, Ord, Typeable, Data)

--type CASLSymbType = CASLSymbol.SymbType

data MFSymbol  = GenSymbol
   { symName :: Id
   , symbType :: MFSymbType
   }
   deriving (Show, Eq, Ord, Typeable, Data)


-- type MFSymbol = GenSymbol MFSymbType

instance Pretty MFSymbol where
  pretty sy@(GenSymbol sN sT) = let n = pretty sN in
    case sT of
       CASLSymbType sT' -> pretty (CASLSign.Symbol sN sT')
       ActnAsItemType pt -> keyword actnS <+> n <+> colon <+> pretty pt
       AttrAsItemType ot -> keyword attS <+> n <+> colon <> pretty ot

symbolForgetMF :: MFSymbol -> CASLSign.Symbol
symbolForgetMF (GenSymbol sN sT) = case sT of
       CASLSymbType sT' -> CASLSign.Symbol sN sT'
       ActnAsItemType pt -> CASLSign.idToPredSymbol sN pt
       AttrAsItemType ot -> CASLSign.idToOpSymbol sN ot

symbolUnMF :: MFSymbol -> Either CASLSign.Symbol CASLSign.Symbol
  -- |Left| ``real'' CASL symbol
  -- |Right| ``fake'' CASL symbol from attr or actn
symbolUnMF (GenSymbol sN sT) = case sT of
  CASLSymbType sT' -> Left $ CASLSign.Symbol sN sT'
  ActnAsItemType pt -> Right $ CASLSign.idToPredSymbol sN pt
  AttrAsItemType ot -> Right $ CASLSign.idToOpSymbol sN ot

splitMFSymbols :: Set.Set MFSymbol -> (Set.Set CASLSign.Symbol, Set.Set CASLSign.Symbol)
splitMFSymbols sys = let
            (sysCASLlist, sysMFlist) = partitionEithers . map symbolUnMF $ Set.toList sys
            sysCASL = Set.fromList sysCASLlist 
            sysMF   = Set.fromList  sysMFlist
            in (sysCASL,sysMF)

--instance Data MFSymbol where 

attrMFSymbol :: Id -> CASLSign.OpType -> MFSymbol
attrMFSymbol ident opTy = GenSymbol
   { symName   = ident
   , symbType  = AttrAsItemType opTy
   }

actnMFSymbol :: Id -> CASLSign.PredType -> MFSymbol
actnMFSymbol ident predTy = GenSymbol
   { symName   = ident
   , symbType  = ActnAsItemType predTy
   }

caslSymbolToMF :: CASLSign.Symbol -> MFSymbol
caslSymbolToMF sy = GenSymbol
  { symName = CASLSign.symName sy
  , symbType = CASLSymbType $ CASLSign.symbType sy
  }
-- | CASL/Sign: idToOpSymbol :: Id -> OpType -> Symbol
-- CASL/Sign: opMap :: OpMap
-- CASL/Sign mapSetToList :: Mapset.Mapset a b -> []
attrSyms :: CASLSign.Sign f SignExtMF -> [MFSymbol]
attrSyms = map (uncurry attrMFSymbol) . CASLSign.mapSetToList . attrSig . CASLSign.extendedInfo

actnSyms :: CASLSign.Sign f SignExtMF -> [MFSymbol]
actnSyms = map (uncurry actnMFSymbol) . CASLSign.mapSetToList . actnSig . CASLSign.extendedInfo

toMFSymbol :: CASLSign.OpMap -> CASLSign.PredMap -> CASLSign.Symbol -> MFSymbol
toMFSymbol attrs actns sy@(CASLSign.Symbol symNm symTy) = case symTy of
  CASLSign.OpAsItemType opTy -> let opId = symNm
    in case Map.lookup opId $ MapSet.toMap attrs of
        Nothing -> caslSymbolToMF sy
        Just types -> if Set.size types == 1
          then attrMFSymbol opId $ Set.elemAt 0 types -- ^  instead symNm
          else error $ "Ambiguous attr symbol " ++ show symNm
  CASLSign.PredAsItemType predTy -> let predId =  symNm -- ^ predSymbName
    in case Map.lookup predId $ MapSet.toMap actns of
        Nothing -> caslSymbolToMF sy
        Just types -> if Set.size types == 1
          then actnMFSymbol predId $ Set.elemAt 0 types  -- ^ $ Set.any
          else error $ "Ambiguous action symbol " ++ show symNm
  _ -> caslSymbolToMF sy


{-
data MFSYMB_KIND = CASL_SYMB_KIND SYMB_KIND
                 | Attrs_kind | Actns_kind
                 deriving (Show, Eq, Ord, Typeable, Data)
data MFRawSymbol = MFASymbol MFSymbol | MFAKindedSymb MFSYMB_KIND Id
                 deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange MFRawSymbol where
    getRange rs = case rs of
        MFASymbol s -> getRange s
        MFAKindedSymb _ i -> getRange i

type MFRawSymbolMap = Map.Map MFRawSymbol MFRawSymbol

data MFSYMB_MAP_ITEMS = MFSymb_map_items MFSYMB_KIND [SYMB_OR_MAP] Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq, Ord, Typeable, Data)


data GEN_SYMB ty = Symb_id Id
                 | Qual_id Id ty Range
            -- pos: colon
                 deriving (Show, Eq, Ord, Typeable, Data)

data GEN_SYMB_OR_MAP ty = Symb (GEN_SYMB ty)
                        | Symb_map (GEN_SYMB ty) (GEN_SYMB ty) Range
                   -- pos: "|->"
                   deriving (Show, Eq, Ord, Typeable, Data)

data MFSYMBTYPE = O_type OP_TYPE
                | P_type PRED_TYPE
                | A_type SORT -- ambiguous pred or (constant total) op
                | T_type OP_TYPE -- attr
                | C_type PRED_TYPE -- actn
            deriving (Show, Eq, Ord, Typeable, Data)

type MFSYMB_OR_MAP = GEN_SYMB_OR_MAP MFS
-}

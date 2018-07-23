{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./MFLogic/Logic_MFLogic.hs
Description :  Instance of class Logic for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017-18
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

Instance of class Logic for MFLogic.
-} 

module MFLogic.Logic_MFLogic where

import MFLogic.AS_MFLogic 
import MFLogic.ATC_MFLogic ()
import MFLogic.MFLogicSign
import MFLogic.Parse_AS
import MFLogic.StatAna
import MFLogic.Sublogic
import MFLogic.MFSymbol

import Common.Id
import CASL.AS_Basic_CASL
import CASL.Logic_CASL
import CASL.ToItem (bsToItem)
import CASL.MapSentence
import CASL.Morphism (Morphism
                     , morphismToSymbMap
                     , matches
                     , plainMorphismUnion
                     , MorphismExtension (..)
                     )
import qualified CASL.Morphism as Mor
import CASL.Sign (Symbol
                 , Sign
                 , mapSetToList
                 , emptySign
                 , addSig
                 , interSig
                 , isSubSig
                 , SignExtension
                 )
import qualified CASL.Sign as Sign
import CASL.Sublogic
import CASL.ColimSign
import CASL.SymbolMapAnalysis as SMA
import CASL.SymbolParser
import Common.Result (Result)
import Common.SetColimit 
import Common.Utils (composeMap)
import Common.ExtSign (plainSign, ExtSign(..))
import Common.DocUtils (pretty)
import Common.Doc ( (<+>), text, vcat )
import Common.Lib.Graph
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import Data.Graph.Inductive.Graph as Graph
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List
import Data.Either (partitionEithers)

import Logic.Logic
import Control.Monad
import Debug.Trace

-- | Empty Datatype MFLogic Declaration

data MFLogic = MFLogic deriving Show

-- | Making MFLogic an instance of Language class defined in Logic/Logic.hs

instance Language MFLogic where
  description _ = "MFLogic is a modal dynamic logic and an extension of CASL."

{- |  MorphismMF is the morphism for MFLogic (CASL + MF Extention). It is a type 
synonym of Morphism defined in CASL/Morphism.hs. Morphism is a 
record with msource, mtarget, sort_map, op_map, pred_map and extended_map

-}
  
type MorphismMF = Morphism MF_FORMULA SignExtMF MFMap

-- | MFLogicFORMULA is the formula for MFLogic (CASL + Extended). It is a type
-- Synonym of FORMULA defined in CASL/AS_Basic_CAS
 
type MFLogicFORMULA = FORMULA MF_FORMULA

-- | Making SignExtMF an instance of SignExtension class defined in CASL/Sign.hs
-- SignExtMF is a record consisting of attrMapSign :: OpMap and actnMapSign :: PredMap
-- isSubSignExtension checks where the signature a is a sub signature of b or not,
-- i.e., (b contains a).
-- isSubMFLogicSign is defined in MFLogicSign.hs

instance SignExtension SignExtMF where
  isSubSignExtension a b = trace "isSubMFLogicSign" $ isSubMFLogicSign a b  


{- Making an instance of Syntax class defined in Logic/Logic.hs
   Symbol is defined is CASL.Sign.hs
   SYMB_ITEMS, SYMB_MAP_ITEMS  are defined in CASL/AS_Basic_CASL.hs
   parser for basic specifications
   parse_basic_spec :: lid -> Maybe (PrefixMap -> AParser st basic_spec)
   basicSpecMF::  PrefixMap -> AParser st MF_BASIC_SPEC

   parser for a single symbol returned as list
   parseSingleSymbItem :: lid -> Maybe (AParser st symb_items)
   symbItems :: [String] -> AParser st SYMB_ITEMS

    parser for symbol lists
    parse_symb_items :: lid -> Maybe (AParser st symb_items)
    
    symbMapItems :: [String] -> AParser st SYMB_MAP_ITEMS

    toItem :: lid -> basic_spec -> Item

    symb_items_name :: lid -> symb_items -> [String]

    None of the function is used in any other place
-}
instance Syntax MFLogic MF_BASIC_SPEC
                MFSymbol SYMB_ITEMS SYMB_MAP_ITEMS
      where
{-       -- Syntax member:
         parsersAndPrinters :: lid -> Map.Map String
            (PrefixMap -> AParser st basic_spec, basic_spec -> Doc)
         -- Syntax default definition:
         parsersAndPrinters li = case parse_basic_spec li of
            Nothing -> Map.empty
            Just p -> makeDefault (p, pretty)
         -- KIF definition:
         parsersAndPrinters MFLogic = {- addSyntax "KIF"
           (const $ fmap kif2CASL kifBasic, pretty)
           $ -} makeDefault (basicSpec [], pretty)  -- ^ what to do
-}
         parse_basic_spec MFLogic = Just basicSpecMF --  Defined in MFLogic.Parse_AS.hs
         parseSingleSymbItem MFLogic = Just $ symbItem mf_reserved_words --  Defined in CASL/SymbolParser.hs

         -- symbItems :: [String] -> AParser st SYMB_ITEMS
         parse_symb_items MFLogic = Just $ do
           r <- symbItems mf_reserved_words
           trace ("symbItems " ++ show r) $ return r -- Defined in CASL/SymbolParser.hs
         parse_symb_map_items MFLogic = Just $ do
           r <- symbMapItems mf_reserved_words -- Defined in CASL/SymbolParser.hs
           trace ("symbMapItems " ++ show r) $ return r
         -- |toItem| seems to be only used in |Syntax/ToXml.hs:gBasicSpec|; probably ot urgent.
         toItem MFLogic = bsToItem                    --  bsToItem is defined in CASL/ToItem.hs
         -- should the fourth parameter of |Syntax| in ths instance really be |SYMB_ITEMS|?
         symb_items_name MFLogic = symbItemsName   --  is defined in /CASL/AS_Basic_CASL.hs

{-Making an instance of Sentences class defined in Logic/Logic.hs
  
  -- sentence translation along a signature morphism
     map_sen:: lid -> morphism -> sentence -> Result sentence
     map_MF_FORMULA :: MapSen MF_FORMULA SignExtMF MFMap

  -- dependency ordered list of symbol sets for a signature
     sym_of :: lid -> sign -> [Set.Set symbol]
     symOf :: Sign f e -> [SymbolSet]

  -- symbol map for a signature morphism
     symmap_of :: lid -> morphism -> EndoMap symbol
     morphismToSymbMap :: Morphism f e m -> SymbolMap

  -- symbols have a name, see CASL RefMan p. 192
      sym_name :: lid -> symbol -> Id
      data Symbol = Symbol {symName :: Id, symbType :: SymbType}

-}
instance Sentences MFLogic MFLogicFORMULA MFSign MorphismMF MFSymbol where
      map_sen MFLogic m  = return . mapSen map_MF_FORMULA m --  is defined here
      -- map_sen MFLogic mor frm  = trace ("map_sen_MF: " ++ show frm ++ "\n" ++ show (text "    " <+> pretty mor))
      --   . return $ mapSen map_MF_FORMULA mor frm
      -- sym_of MFLogic = Mor.symOf     -- ^ defined in CASL/Morphism.hs
      sym_of MFLogic sign = let
          [sorts, predOps] = Mor.symOf sign
        in  [ Set.map caslSymbolToMF sorts
            , foldr  Set.insert (Set.map caslSymbolToMF predOps)
                     $ attrSyms sign ++ actnSyms sign
            ]
      symmap_of MFLogic = morphismToMFSymbMap -- Aux False
      sym_name MFLogic = symName -- defined in MFSymbol

      -- | a logic dependent kind of a symbol
      -- |symKind :: lid -> symbol -> String|
      -- |symKind _ _ = ""| -- WK: Does thes need to discern ActnSymbs and AttrSymbs?
     
morphismToMFSymbMap :: MorphismMF -> EndoMap MFSymbol
morphismToMFSymbMap mor = let
    symbMap  = Map.foldWithKey sToMF Map.empty
             $ Mor.morphismToSymbMap mor
      where sToMF sy1 sy2 = Map.insert (caslSymbolToMF sy1) (caslSymbolToMF sy2)
    src = Mor.msource mor
    sorts = Mor.sort_map mor
    attrs = attr_MapMor $ Mor.extended_map mor
    actns = actn_MapMor $ Mor.extended_map mor
    attrSymMap = MapSet.foldWithKey
      ( \ i t -> let (j, k) = Mor.mapOpSym sorts attrs (i, t) in
                 -- if b && i == j && opKind k == opKind t then id else
                     Map.insert (attrMFSymbol i t) $ attrMFSymbol j k)
      Map.empty $ attrSig $ Sign.extendedInfo src
    actnSymMap = MapSet.foldWithKey
      ( \ i t -> let (j, k) = Mor.mapPredSym sorts actns (i, t) in
                 -- if b && i == j then id else
                     Map.insert (actnMFSymbol i t) $ actnMFSymbol j k)
      Map.empty $ actnSig $ Sign.extendedInfo src
    result = foldr Map.union symbMap [attrSymMap, actnSymMap]
  in trace (show $ text "MF.symmap_of:" <+> pretty result) result

{- Making an instance of StaticAnalysis defines in Logic/Logic.hs
   basic_analysis :: lid
           -> Maybe ((basic_spec, sign, GlobalAnnos)
             -> Result (basic_spec, ExtSign sign symbol, [Named sentence]))

-}

type ExtSignMF = ExtSign MFSign MFSymbol

instance StaticAnalysis MFLogic MF_BASIC_SPEC MFLogicFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               MFSign
               MorphismMF
               MFSymbol Mor.RawSymbol where
         basic_analysis MFLogic = Just basicMFLogicAnalysis    --  defined in MFLogic/StatAna.hs need work
         -- |extBasicAnalysis|: For a start, default definition plus tracing.
         extBasicAnalysis l _IRI _LibName b s g = trace "MFLogic.extBasicAnalysis"
             $ basicMFLogicAnalysis (b, s, g)
         sen_analysis MFLogic = Just mf_sen_analysis

         -- | static analysis of symbol maps, see CASL RefMan p. 222f.
         -- Mor.statSymbMapItems :: Sign f e -> Maybe (Sign f e)
         --        -> [SYMB_MAP_ITEMS] -> Result RawSymbolMap
         stat_symb_map_items MFLogic sig msig smis = do
            r <-  Mor.statSymbMapItems sig msig smis
            trace ("stat_symb_map_items\n==== sig:" ++ shows (pretty sig)
                   "\n==== msig = " ++ maybe "Nothing" (show . pretty) msig
                   ++ "\n==== argument:\n"
                   ++ unlines (map (("        " ++) . show) smis)
                   ++ "==== result RawSymbolMap: "
                   ++ concatMap (\ s -> "\n      " ++ show s) (Map.toList r)) $ return r

         -- statSymbItems :: Sign f e -> [SYMB_ITEMS] -> Result [RawSymbol]
         stat_symb_items MFLogic sig sis = do
            r <- Mor.statSymbItems sig sis
            trace ("stat_symb_items" ++ shows sis " -> " ++ show r) $
              return r
         signature_colimit MFLogic diag = let
              diag' = emap (\ (i, phi) -> trace (show (text ("signature_colimit: edge " ++ shows i " op_map:") <+> (vcat (map (text . show) (Map.toList $ Mor.op_map phi))))) (i, phi)) diag
            in return $ signColimit diag' extMFLogicColimit         


         symbol_to_raw MFLogic = Mor.symbolToRaw . symbolForgetMF
  
         id_to_raw MFLogic = Mor.idToRaw

         -- matches :: lid -> symbol -> raw_symbol -> Bool
         {- | Check whether a symbol matches a raw symbol, for
            example, f:s->t matches f. See CASL RefMan p. 192 -}
         matches MFLogic sy rsy = Mor.matches (symbolForgetMF sy) rsy

         empty_signature MFLogic =  trace " empty_signature call" $ emptySign emptyMFLogicSign
         signature_union MFLogic s = return . addSig addMFLogicSign s
         intersection MFLogic s = return . interSig interMFLogicSign s
         morphism_union MFLogic m1 m2 = trace "morphism_union_MF" $ plainMorphismUnion addMFLogicSign m1 m2
         final_union MFLogic = finalUnion addMFLogicSign
         is_subsig MFLogic = isSubSig isSubMFLogicSign

         -- Any and/or all of the |emptyMFMap| below might be wrong.
         subsig_inclusion MFLogic sign1 sign2 = let
             mfm = identityMFMap $ Sign.extendedInfo sign1
           in trace (show (text " subsig_inclusion: " <+> pretty mfm)) $ Mor.sigInclusion mfm sign1 sign2
         -- The largest sub-signature of |sig| excluding |sys|
         cogenerated_sign MFLogic sys sig = trace " cogenerated_sign" $ cogeneratedSign emptyMFMap (error s) (error s)
            where s = "cogenerated_sign MFLogic not yet implemented"
         -- The smallest sub-signature of |sig| inxcluding |sys|
         -- make sure that our sigExtMF is findig its way into the msource of the returned morphism
         generated_sign MFLogic sys sig = let
            (sysCASLlist, sysMFlist) = partitionEithers . map symbolUnMF $ Set.toList sys
            sysCASL = Set.fromList sysCASLlist 
            sysMF   = Set.fromList  sysMFlist
            (mfSortSys, signExtMF) = Set.fold f (Set.empty, emptyMFLogicSign) sysMF
              where
                f sy (sortSys1, sigExtMF1) = case Sign.symbType sy of
                    Sign.OpAsItemType ot ->     -- 4.1.2./4.1.3.
                      ( foldr (Set.insert . Sign.idToSortSymbol) sortSys1 $ Sign.opSorts ot
                      , sigExtMF1 { attrSig = MapSet.insert n ot $ attrSig sigExtMF1 }
                      )
                    Sign.PredAsItemType pt ->   -- 4.1.4.
                      ( foldr (Set.insert . Sign.idToSortSymbol) sortSys1 $ Sign.predArgs pt
                      , sigExtMF1 { actnSig = MapSet.insert n pt $ actnSig sigExtMF1 } 
                      )
                    _ -> error "MFLogic.generated_sign: IMPOSSIBLE: symbolUnMF"
                  where n = Sign.symName sy
            mfMap1 = -- inclusionMFMap signExtMF $ extendedInfo sig
                      identityMFMap signExtMF
           in generatedSign mfMap1 (Set.union mfSortSys sysCASL)
                -- make sure that our sigExtMF is findig its way into the msource of the returned morphism:
                $ sig { Sign.extendedInfo = signExtMF }

         induced_from_morphism MFLogic rawSymbMap sign
             = trace ("MFLogic.induced_from_morphism:\n  rawSymbMap = " ++ show rawSymbMap)
             $ inducedFromMorphism emptyMFMap rawSymbMap sign
         induced_from_to_morphism MFLogic rawSymbMap srcExtSign trgExtSign
             = let 
             srcSign = plainSign srcExtSign
             srcAttrMapSig :: Sign.OpMap
             srcAttrMapSig = attrSig (Sign.extendedInfo srcSign)
             srcActnMapSig :: Sign.PredMap
             srcActnMapSig = actnSig (Sign.extendedInfo srcSign)
             isSrcAttr :: OP_NAME -> Bool
             isSrcAttr op = op `Map.member` MapSet.toMap srcAttrMapSig
             isSrcActn :: PRED_NAME -> Bool
             isSrcActn pred = pred `Map.member` MapSet.toMap srcActnMapSig
             srcSign' = srcSign
               { Sign.opMap = Sign.opMap srcSign `MapSet.union` srcAttrMapSig
               , Sign.predMap = Sign.predMap srcSign `MapSet.union` srcActnMapSig
               , Sign.extendedInfo = emptyMFLogicSign
               }
             srcExtSign'@(ExtSign srcsig srcsym)= srcExtSign
               { plainSign = srcSign'
               , nonImportedSymbols = srcsym
               }
             trgSign = plainSign trgExtSign
             trgAttrMapSig = attrSig (Sign.extendedInfo trgSign)
             trgActnMapSig = actnSig (Sign.extendedInfo trgSign)
             isTrgAttr op = op `Map.member` MapSet.toMap trgAttrMapSig
             isTrgActn pred = pred `Map.member` MapSet.toMap trgActnMapSig
             trgSign' = trgSign
               { Sign.opMap = Sign.opMap trgSign `MapSet.union` trgAttrMapSig
               , Sign.predMap = Sign.predMap trgSign `MapSet.union` trgActnMapSig
               , Sign.extendedInfo = emptyMFLogicSign
               }
             trgExtSign'@(ExtSign trgsig trgsym) = trgExtSign
               {plainSign = trgSign'
               , nonImportedSymbols = trgsym
               }
           in do
             mor0 <- inducedFromToMorphism emptyMFMap isSubMFLogicSign diffMFLogicSign
                rawSymbMap srcExtSign' trgExtSign'
             let
               srcSign'', srcSign''' :: Sign.Sign MF_FORMULA SignExtMF
               srcSign'' = Mor.msource mor0
               srcSign''' = srcSign''
                    { Sign.opMap = MapSet.filterWithKey (\ op _ -> not $ isSrcAttr op) $ Sign.opMap srcSign''
                 , Sign.predMap = MapSet.filterWithKey (\ prd _ -> not $ isSrcActn prd) $ Sign.predMap srcSign''
                 , Sign.extendedInfo = SignExtMF
                    { attrSig = MapSet.filterWithKey (\ op _ -> isSrcAttr op) $ Sign.opMap srcSign''
                    , actnSig = MapSet.filterWithKey (\ prd _ -> isSrcActn prd) $ Sign.predMap srcSign''
                    }
                 }
               trgSign'', trgSign''' :: Sign.Sign MF_FORMULA SignExtMF
               trgSign'' = Mor.mtarget mor0
               trgSign''' = trgSign''  -- does this need looking up attrs in source and follow via op_map?
                 { Sign.opMap = MapSet.filterWithKey (\ op _ -> not $ isTrgAttr op) $ Sign.opMap trgSign''
                 , Sign.predMap = MapSet.filterWithKey (\ pred _ -> not $ isTrgActn pred) $ Sign.predMap trgSign''
                 , Sign.extendedInfo = SignExtMF
                    { attrSig = MapSet.filterWithKey (\ op _ -> isTrgAttr op) $ Sign.opMap trgSign''
                    , actnSig = MapSet.filterWithKey (\ pred _ -> isTrgActn pred) $ Sign.predMap trgSign''
                    }
                 }
               mfMap1 = MFMap
                { attr_MapMor = Map.filterWithKey (\ (op, _) _ -> isSrcAttr op) $ Mor.op_map mor0
                , actn_MapMor = Map.filterWithKey (\ (prd, _) _ -> isSrcActn prd) $ Mor.pred_map mor0
                }
               opMap1 = Map.filterWithKey (\ (op, _) _ -> not $ isSrcAttr op) $ Mor.op_map mor0
             trace (unlines
                 ["MFLogic.induced_from_to_morphism:"
                 ,show $ text "   rawSymbMap:  " <+> pretty rawSymbMap
                 ,show $ text "   srcExtSign:  " <+> pretty srcExtSign
                 ,show $ text "   trgExtSign:  " <+> pretty trgExtSign
                 ,show $ text "   opMap1:      " <+> text (show opMap1)
                 ,show $ text "   mfMap1:      " <+> pretty mfMap1
                 ])
              $ return $ mor0
              { Mor.msource = srcSign'''
              , Mor.mtarget = trgSign'''
              , Mor.op_map = opMap1
              , Mor.pred_map = Map.filterWithKey (\ (prd, _) _ -> not $ isSrcActn prd) $ Mor.pred_map mor0
              , Mor.extended_map = mfMap1
              }




instance NameSL Bool where
    nameSL b = if b then "MF" else ""             



instance MinSL Bool MF_FORMULA where
    minSL = minFormSublogicMF

instance MinSL Bool MF_SIG_ITEM where
    minSL = minMFSigItem


instance MinSL Bool MF_BASIC_ITEM where
    minSL = const bottom


instance MinSL Bool SignExtMF where
    minSL = const bottom

 
instance ProjForm Bool MF_FORMULA where
    projForm _ = Just . ExtFORMULA
 
instance ProjSigItem Bool MF_SIG_ITEM MF_FORMULA where
    projSigItems _ s = (Just $ Ext_SIG_ITEMS s, [])
    
instance ProjBasic Bool MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA where
    projBasicItems _ b = (Just $ Ext_BASIC_ITEMS b, [])

instance MinSublogic MFLogic_Sublogics MFSymbol where
    minSublogic sy = case symbolUnMF sy of
      Left csy -> minSublogic csy
      Right _ -> caslTop

-- | Trying to instantiate ProjectSublogicM for MFSymbol
-- | class providing a partial projection of an item to a sublogic

instance ProjectSublogicM MFLogic_Sublogics MFSymbol where
    projectSublogicM _ = either (Just . caslSymbolToMF) (const Nothing) . symbolUnMF
 
-- | Making an instance of Logic class defined in Logic/Logic.hs
-- | The central type class of Hets.

instance Logic MFLogic MFLogic_Sublogics
               MF_BASIC_SPEC MFLogicFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MFSign
               MorphismMF
               MFSymbol Mor.RawSymbol () where
         parse_basic_sen MFLogic = Just $ const parseSenMF
         stability MFLogic = Unstable

         -- |emptyMFMap| here might be wrong:
         proj_sublogic_epsilon MFLogic = pr_epsilon emptyMFMap

         all_sublogics MFLogic = sublogics_all [True]
         sublogicDimensions MFLogic = sDims [[True]]
         parseSublogic MFLogic = parseSL parseMF
         empty_proof_tree MFLogic = ()

parseMF :: String -> Maybe (Bool, String)
parseMF s = case stripPrefix "MF" s of
  Just r -> Just (True, r)
  _ -> Just (False, s)


-- | Function related to calculate colimit and static ana

identityMFMap :: SignExtMF -> MFMap
identityMFMap _mfSig = MFMap
  { attr_MapMor = Map.empty -- MapSet.fold insertAttr Map.empty attrSig
  , actn_MapMor = Map.empty -- MapSet.fold insertActn Map.empty actnSig
  }
  -- where
  --   insertAttr = _
  --   insertActn = _
-- | 

map_MF_FORMULA :: MapSen MF_FORMULA SignExtMF MFMap
map_MF_FORMULA mor frm = trace (unlines ["map_MF_FORMULA: " ++ show frm
                                        , show (text "    " <+> pretty mor)
                                        , show mor
                                        ,replicate 50 '-'
                                        ])
  $ let mfMap = Mor.extended_map mor
        mor' = mor { Mor.op_map   = Map.union (attr_MapMor mfMap) (Mor.op_map mor)
                   , Mor.pred_map = Map.union (actn_MapMor mfMap) (Mor.pred_map mor)
                   }
    in case frm of
            FormX f ps        -> let 
               newF = mapSen map_MF_FORMULA mor' f  
               in FormX newF ps
            FormF f ps        -> let 
                newF = mapSen map_MF_FORMULA mor' f  
              in FormF newF ps     
            Action sym tsOld ps -> case mapSen map_MF_FORMULA mor' $ Predication sym tsOld ps of
                Predication sym' tsNew ps' -> Action sym' tsNew ps'
                _ -> error "Unexpected mapSen result for Action"
            BEG _ps -> frm 
            AttrSel opNam tsOld ps -> case mapTerm map_MF_FORMULA mor' $ Application opNam tsOld ps of
                Application opNam' tsNew ps' -> AttrSel opNam' tsNew ps'
                _ -> error "Unexpected mapTerm result for AttrSel"  
            TermX t ps -> let 
                newT = mapTerm map_MF_FORMULA mor' t 
              in TermX newT ps 

composeMorMFMap :: Morphism f SignExtMF MFMap -> Morphism f SignExtMF MFMap -> Result MFMap
composeMorMFMap mor1 mor2 = 
  let sMap1 = Mor.sort_map mor1
      src = Mor.msource mor1
      -- tar = Mor.mtarget mor2
      mfMap1 = Mor.extended_map mor1
      oMap1 = attr_MapMor mfMap1
      pMap1 = actn_MapMor mfMap1
      sMap2 = Mor.sort_map mor2
      mfMap2 = Mor.extended_map mor2
      oMap2 = attr_MapMor mfMap2
      pMap2 = actn_MapMor mfMap2
      -- sMap = composeMap (MapSet.setToMap $ Sign.sortSet src) sMap1 sMap2
      oMap = if Map.null oMap2 then oMap1
        else MapSet.foldWithKey ( \ i ot ->
               let (ni, nt) = Mor.mapOpSym sMap2 oMap2
                     $ Mor.mapOpSym sMap1 oMap1 (i, ot)
                   k = Sign.opKind nt
               in trace ("composeMorMFMap.oMap (i, ni): " ++ show (i, ni))
                 $ if i == ni && Sign.opKind ot == k then id else
                  Map.insert (i, Sign.mkPartial ot) (ni, k))  -- what |mkPartial| ???
                     Map.empty . attrSig $ Sign.extendedInfo src
      pMap = if Map.null pMap2 then pMap1 else
                 MapSet.foldWithKey ( \ i pt ->
                       let ni = fst $ Mor.mapPredSym sMap2 pMap2
                             $ Mor.mapPredSym sMap1 pMap1 (i, pt)
                       in if i == ni then id else Map.insert (i, pt) ni)
                      Map.empty . actnSig $ Sign.extendedInfo src
      result = MFMap
          { attr_MapMor = Map.filterWithKey
                (\ (i, ot) (j, k) -> i /= j || k == Total && Set.member ot
                 (MapSet.lookup i $ Sign.opMap src)) oMap
          , actn_MapMor = Map.filterWithKey ((/=) . fst) pMap
          }
  in trace (unlines
       ["composeMorMFMap.: oMap: " ++ show oMap
       ,"composeMorMFMap.: pMap: " ++ show pMap
       ,"composeMorMFMap.: mfMap1" ++ show mfMap1
       ,"composeMorMFMap.: mfMap2" ++ show mfMap2
       ,"composeMorMFMap.: result" ++ show result
       ])
       $ return result

-- m1 m2 = composeMFMap (Mor.extended_map m1) (Mor.extended_map m2)

isInclusionMFMap :: MFMap -> Bool
isInclusionMFMap m = Map.null (attr_MapMor m) && Map.null (actn_MapMor m)

instance MorphismExtension SignExtMF MFMap where
   ideMorphismExtension = identityMFMap -- :: MFLogicSign -> MFMap
   composeMorphismExtension = composeMorMFMap -- :: Morphism f e m -> Morphism f e m -> Result m
   -- inverseMorphismExtension :: Morphism f e m -> Result m
   inverseMorphismExtension m = let
           src = Mor.msource m
           attrs = attrSig $ Sign.extendedInfo src
           actns = actnSig $ Sign.extendedInfo src
           sm = Mor.sort_map m
           attrm = attr_MapMor $ Mor.extended_map m
           actnm = actn_MapMor $ Mor.extended_map m
           ism = Map.fromList $ map (\ (s1, s2) -> (s2, s1)) $ Map.toList sm
           iattrm = Map.fromList $ map (\ ((i, t), (j, k)) ->
                       ((j,Mor.mapOpType sm t), (i, k))) $ Map.toList attrm
           iactnm = Map.fromList $ map (\ ((i, t), j) ->
                       ((j, Mor.mapPredType sm t), i)) $ Map.toList actnm
     in do
       unless (attrs == Mor.inducedOpMap ism iattrm (Mor.inducedOpMap sm attrm attrs))
         $ fail "no injective MF attribute mapping"
       unless (actns == Mor.inducedPredMap ism iactnm (Mor.inducedPredMap sm actnm actns))
         $ fail "no injective MF action mapping"
       return $ MFMap
         { attr_MapMor = iattrm
         , actn_MapMor = iactnm
         }
   isInclusionMorphismExtension = isInclusionMFMap -- :: m -> Bool
   -- prettyMorphismExtension :: Morphism f e m -> Doc
   -- prettyMorphismExtension = pretty . extended_map
   -- legalMorphismExtension :: Morphism f e m -> Result ()
   -- legalMorphismExtension _ = return ()

attrIdMap :: MFMap -> Map Id Id
attrIdMap = Map.foldWithKey (\ (aId, _aType) (aId', _aKind) -> Map.insert aId aId') Map.empty . attr_MapMor

actnIdMap :: MFMap -> Map Id Id
actnIdMap = Map.foldWithKey (\ (aId, _aType) aId' -> Map.insert aId aId') Map.empty . actn_MapMor

emptyMFMap ::  MFMap
emptyMFMap =  MFMap
  { attr_MapMor = Map.empty
  , actn_MapMor = Map.empty
  }

--  Extended MFLogic colimit ???? move it to a single file

extMFLogicColimit :: Gr SignExtMF (Int, MFMap) ->
                  Map.Map Int MorphismMF ->
                  (SignExtMF, Map.Map Int MFMap)
extMFLogicColimit mfgraph phiSRel = let
   (attrMap, attrCoCone) = computeColimitAttr mfgraph phiSRel
   (actnMap, actnCoCone) = computeColimitActn mfgraph phiSRel
   mfSig = SignExtMF
     { attrSig = attrMap
     , actnSig = actnMap
     }
   mfCoCone = Map.foldWithKey h Map.empty attrCoCone
     where h n atMap = Map.insert n . MFMap atMap $ actnCoCone Map.! n
 in trace
    (unlines $ "extMFLogicColimit: phiSRel:" : map (\ (i, m) -> show (text ("   " ++ shows i ".op_map: ") <+> text (show (Mor.op_map m)))) (Map.toList phiSRel))
    (mfSig, mfCoCone)

computeColimitAttr  :: Gr SignExtMF (Int, MFMap)
                    -> Map Node MorphismMF  -- NB |Morphism|s from  original specs to CASL-colimit-so-far
                    ->  ( Sign.OpMap           -- NB |attMapSig| of colimit spec
                        , Map Node Mor.Op_map  -- for each |Node|, the |attr_MapMor| of the cocone morphism
                        )
computeColimitAttr mfgraph phiSRel = let
  graph' = buildAttrGraph mfgraph
  (colim, morMap') = computeColimitSet graph' -- Help: |colim| is the set of attr. IDs of the colimit
  colim' = Set.fold addTypedAttr MapSet.empty colim
  getOrigType :: (Id, Node) -> Sign.OpType
  getOrigType (attrId, n) = srcTy
    where
      mor_n = phiSRel Map.! n
      srcSig :: Sign MF_FORMULA SignExtMF
      srcSig = Mor.msource mor_n
      srcTy :: Sign.OpType
      srcTy = case Set.toList . MapSet.lookup attrId . attrSig $ Sign.extendedInfo srcSig of
        [] -> error $ "computeColimitAttr: No type for " ++ shows attrId " in sig. " ++ show n
        ty : _ -> ty  -- no overloaded attribute names!
  addTypedAttr :: (Id, Node) -> Sign.OpMap -> Sign.OpMap
  addTypedAttr newAttrIdPair@(attrId, n) = MapSet.insert attrId ty
    where
      mor_n = phiSRel Map.! n
      ty = Mor.mapOpType (Mor.sort_map mor_n) $ getOrigType newAttrIdPair
  convertMap :: Map.Map Id (Id, Node) -> Mor.Op_map
  convertMap = Map.foldWithKey addOpPair Map.empty
    where
      addOpPair :: Id -> (Id, Node) -> Mor.Op_map -> Mor.Op_map
      addOpPair oldAttrId newAttrIdPair@(newAttrId, _n) = Map.insert (oldAttrId, getOrigType newAttrIdPair) (newAttrId, Total)
  morMap'' = Map.map convertMap morMap'
{-
 (ovrl, names, totalOps) = buildColimOvrl graph graph' colim morMap'
 (colim1, morMap1) = nameSymbols graph' morMap' phiSRel names ovrl totalOps
 morMap2 = Map.map (Map.map (\ ((i, o), _) -> (i, opKind o))) morMap1
 morMap3 = Map.map (Map.fromAscList . map
            (\ ((i, o), y) -> ((i, mkPartial o), y)) . Map.toList) morMap2
 in (colim1, morMap3)
-}
 in trace (unlines $ "computeColimitAttr" :
      [show $ text "   colim:  " <+> vcat (map (text . show) (Set.toList colim))
      ,show $ text "   morMap'  " <+> vcat (map (text . show) (Map.toList morMap'))
      ,show $ text "   colim':  " <+> vcat (map (text . show) (MapSet.toList colim'))
      ,show $ text "   morMap''  " <+> vcat (map (text . show) (Map.toList morMap''))
      ] )
   (colim', morMap'')

buildAttrGraph  :: Gr SignExtMF (Int, MFMap)
                -> Gr  (Set Id)
                       (Int -- arbitrary
                       , Map  Id -- attr. ID in orig spec.
                              Id -- colimit attr. ID
                       ) 
buildAttrGraph graph = let
  getAttrs :: SignExtMF -> [(Id, Sign.OpType)]
  getAttrs = mapSetToList . attrSig
 in nmap (Set.fromList . map fst . getAttrs)
  $ emap  (\ (i, mfMap) ->
            trace (unlines $ ("buildAttrGraph.emap " ++ show i)
                           : map (("   " ++) . show) (Map.toList $ attr_MapMor mfMap)) 
            (i, attrIdMap mfMap)
          ) graph

{-
-- Not easy to get the sort mappings from the edge labels only.
buildAttrGraph  :: Gr MFLogicSign (Int, MFMap)
                -> Map Node MFLogicMor  -- |Morphism|s from  original specs to CASL-colimit-so-far
                -> Gr  (Set (Id, Sign.OpType))
                       (Int -- arbitrary
                       , Map  (Id, Sign.OpType) -- attr. ID and type in orig spec.
                              (Id, Sign.OpType) -- colimit attr. ID; type uses renamed sorts
                       ) 
buildAttrGraph graph phiSRel = let
  getAttrs :: MFLogicSign -> [(Id, Sign.OpType)]
  getAttrs = mapSetToList . attrSig
  getAttrFun src trg e  = let
       mor = phiSRel Map.! 
       ssign = Mor.msource mor  -- ^ couldn't math expected type
       -- smap = Mor.sort_map mor  -- ^ couldn't math expected type
       amap = attr_MapMor mor
     in foldl (\ f x -> let y = Mor.mapOpSym smap amap x
                       in if x == y then f else Map.insert x y f)
       Map.empty $ getAttrs ssign  -- ^ couldn't math expected type
 in nmap (Set.fromList . getAttrs) $ emap (\ (i, m) -> (i, getAttrFun m)) graph
-}


computeColimitActn  :: Gr SignExtMF (Int, MFMap)
                    -> Map Node MorphismMF  -- NB |Morphism|s from  original specs to CASL-colimit-so-far
                    ->  ( Sign.PredMap           -- Help: |actnMapSig| of colimit spec
                        , Map Node Mor.Pred_map  -- for each |Node|, the |actn_MapMor| of the cocone morphism
                        )


computeColimitActn mfgraph phiSRel = let
  graph' = buildActnGraph mfgraph
  (colim, morMap') = computeColimitSet graph' -- Help: |colim| is the set of attr. IDs of the colimit
  colim' = Set.fold addTypedActn MapSet.empty colim
  getOrigTypeActn :: (Id, Node) -> Sign.PredType
  getOrigTypeActn (actnId, n) = srcTy
    where
      mor_n = phiSRel Map.! n
      srcSig :: Sign MF_FORMULA SignExtMF
      srcSig = Mor.msource mor_n
      srcTy :: Sign.PredType
      srcTy = case Set.toList . MapSet.lookup actnId . actnSig $ Sign.extendedInfo srcSig of
        [] -> error $ "computeColimitActn: No type for " ++ shows actnId " in sig. " ++ show n
        ty : _ -> ty  -- no overloaded attribute names!
  addTypedActn :: (Id, Node) -> Sign.PredMap -> Sign.PredMap
  addTypedActn newActnIdPair@(actnId, n) = MapSet.insert actnId ty
    where
      mor_n = phiSRel Map.! n
      ty = Mor.mapPredType (Mor.sort_map mor_n) $ getOrigTypeActn newActnIdPair
  convertMap :: Map.Map Id (Id, Node) -> Mor.Pred_map
  convertMap = Map.foldWithKey addPredPair Map.empty
    where
      addPredPair :: Id -> (Id, Node) -> Mor.Pred_map -> Mor.Pred_map
      addPredPair oldActnId newActnIdPair@(newActnId, _n) = Map.insert (oldActnId, getOrigTypeActn newActnIdPair) newActnId
{-
 (ovrl, names, totalOps) = buildColimOvrl graph graph' colim morMap'
 (colim1, morMap1) = nameSymbols graph' morMap' phiSRel names ovrl totalOps
 morMap2 = Map.map (Map.map (\ ((i, o), _) -> (i, opKind o))) morMap1
 morMap3 = Map.map (Map.fromAscList . map
            (\ ((i, o), y) -> ((i, mkPartial o), y)) . Map.toList) morMap2
 in (colim1, morMap3)
-}
 in (colim', Map.map convertMap morMap')

buildActnGraph  :: Gr SignExtMF (Int, MFMap)
                -> Gr  (Set Id)
                       (Int -- arbitrary
                       , Map  Id -- attr. ID in orig spec.
                              Id -- colimit attr. ID
                       ) 
buildActnGraph graph = let
  getActns :: SignExtMF -> [(Id, Sign.PredType)]
  getActns = mapSetToList . actnSig
 in nmap (Set.fromList . map fst . getActns) $ emap (\ (i, mfMap) -> (i, actnIdMap mfMap)) graph

{-
-- Not easy to get the sort mappings from the edge labels only.
buildAttrGraph  :: Gr MFLogicSign (Int, MFMap)
                -> Map Node MFLogicMor  -- |Morphism|s from  original specs to CASL-colimit-so-far
                -> Gr  (Set (Id, Sign.OpType))
                       (Int -- arbitrary
                       , Map  (Id, Sign.OpType) -- attr. ID and type in orig spec.
                              (Id, Sign.OpType) -- colimit attr. ID; type uses renamed sorts
                       ) 
buildAttrGraph graph phiSRel = let
  getAttrs :: MFLogicSign -> [(Id, Sign.OpType)]
  getAttrs = mapSetToList . attrSig
  getAttrFun src trg e  = let
       mor = phiSRel Map.! 
       ssign = Mor.msource mor  -- ^ couldn't math expected type
       -- smap = Mor.sort_map mor  -- ^ couldn't math expected type
       amap = attr_MapMor mor
     in foldl (\ f x -> let y = Mor.mapOpSym smap amap x
                       in if x == y then f else Map.insert x y f)
       Map.empty $ getAttrs ssign  -- ^ couldn't math expected type
 in nmap (Set.fromList . getAttrs) $ emap (\ (i, m) -> (i, getAttrFun m)) graph
-}

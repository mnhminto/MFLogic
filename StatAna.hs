{- |
Module      :  ./MFLogic/StatAna.hs
Description :  static analysis for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

static analysis for MFLogic
-}

module MFLogic.StatAna where

import MFLogic.AS_MFLogic
import MFLogic.Print_AS ()
import MFLogic.MFLogicSign

import CASL.Sign
import CASL.MixfixParser
import CASL.ShowMixfix
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.Quantification
import CASL.Fold

import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.Id
import Common.Result
import Common.DocUtils
import Common.Doc ( text, (<+>), vcat )
import Common.ExtSign
import qualified Data.Map as Map
import qualified CASL.Morphism as Mor
import qualified Common.Lib.MapSet as MapSet
import MFLogic.MFSymbol
import Control.Monad

import Data.Maybe
import Data.List (partition)

import Debug.Trace

type MFSign = Sign MF_FORMULA SignExtMF


instance TermExtension MF_FORMULA where
    freeVarsOfExt sign cf = case cf of
       _ -> Set.empty

convertFormula :: OpMap -> PredMap -> FORMULA MF_FORMULA -> FORMULA MF_FORMULA
convertFormula attrs actns x = hf x
  where
    hf (Quantification q vs f rng) = Quantification q vs (hf f) rng
    hf (Junction j f rng) = let f' = map hf f
                            in Junction j f' rng
    hf (Relation f1 rel f2 rng) = Relation (hf f1) rel (hf f2) rng
    hf (Negation f rng) = Negation (hf f) rng
    hf (Atom bool rng) = Atom bool rng
    hf (Predication pred ts rng) = let ts' = map ht ts in
      case Map.lookup (predSymbName pred) $ MapSet.toMap actns of
        Nothing -> Predication pred ts' rng
        Just _types ->  trace (show (vcat
            [text "convertFormula " <+> pretty x, text " Action: " <+> pretty pred])) $
           ExtFORMULA $ Action pred ts' rng

    hf (Definedness t rng) =  Definedness (ht t) rng
    hf (Equation t1 eql t2 rng) =  let t1' = ht t1
                                       t2' = ht t2
                                   in  Equation t1' eql t2' rng
    hf (Membership t srt rng) =  let t' = ht t in Membership t' srt rng
    hf (Mixfix_formula t) =  let t' = ht t in Mixfix_formula t'
    hf (Unparsed_formula str rng) = Unparsed_formula str rng
    hf (Sort_gen_ax con bool) = Sort_gen_ax con bool
    hf (QuantOp opn opt f) = QuantOp opn opt (hf f)
    hf (QuantPred predn predt f) = QuantPred predn predt (hf f)
    hf (ExtFORMULA f) = ExtFORMULA $ hMF f

    hMF (FormX f rng) = FormX (hf f) rng
    hMF (FormF f rng) = FormF (hf f) rng
    hMF (Action pred ts rng) = Action pred (map ht ts) rng
    hMF f@(BEG rng) = f
    hMF (AttrSel attr ts rng) = AttrSel attr (map ht ts) rng
    hMF (TermX t rng) = TermX (ht t) rng
    
    ht (Qual_var var srt rng)  = Qual_var var srt rng
    ht (Application op ts rng) =  let ts' = map ht ts in
      case Map.lookup (opSymbName op) $ MapSet.toMap attrs of
        Nothing -> Application op ts' rng
        Just _types ->  trace (show (vcat
               [text "convertFormula " <+> pretty x, text " Attr: " <+> pretty op])) $
           ExtTERM $ AttrSel op ts' rng
    ht (Sorted_term ts srt rng) = let ts' = ht ts
                                  in Sorted_term ts' srt rng
    ht (Cast ts srt rng) = let ts' = ht ts
                                  in Cast ts' srt rng
    ht (Conditional ts1 f ts2 rng) = let ts1' = ht ts1
                                         ts2' = ht ts2
                                     in Conditional ts1' (hf f) ts2' rng
    ht (Unparsed_term str rng) = Unparsed_term str rng
    ht (Mixfix_qual_pred prds) = Mixfix_qual_pred prds
    ht (Mixfix_term ts)        = let ts' = map ht ts
                                 in Mixfix_term  ts'
    ht ( Mixfix_token tkn)     =  Mixfix_token tkn
    ht (Mixfix_sorted_term srt rng) = Mixfix_sorted_term srt rng
    ht (Mixfix_cast srt rng)     = Mixfix_cast srt rng
    ht (Mixfix_parenthesized ts rng) = let ts' = map ht ts
                                       in  Mixfix_parenthesized ts' rng
    ht (Mixfix_bracketed ts rng) = let ts' = map ht ts
                                   in Mixfix_bracketed ts' rng
    ht (Mixfix_braced ts rng)    = let ts' = map ht ts
                                   in Mixfix_braced ts' rng
    ht (ExtTERM f) = ExtTERM $ hMF f

basicMFLogicAnalysis
  :: (BASIC_SPEC MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA,
      Sign MF_FORMULA SignExtMF, GlobalAnnos)
  -> Result (BASIC_SPEC MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA,
             ExtSign (Sign MF_FORMULA SignExtMF) MFSymbol,
             [Named (FORMULA MF_FORMULA)])
basicMFLogicAnalysis arg = do
  r@(spec, extSig, axioms) <-
    basicAnalysis minExpForm ana_MF_BASIC_ITEM ana_MF_SIG_ITEMS ana_MFMix arg
  let  sig = plainSign extSig
       attrs = attrSig $ extendedInfo sig
       actns = actnSig $ extendedInfo sig 
       extSig' :: ExtSign (Sign MF_FORMULA SignExtMF) MFSymbol
       extSig' = extSig
         { plainSign = sig
             { opMap = opMap sig `MapSet.difference` attrs
             , predMap = predMap sig `MapSet.difference` actns
             -- , extendedInfo = 
             }
         , nonImportedSymbols = Set.map (toMFSymbol attrs actns) $ nonImportedSymbols extSig
         }
       -- \edcomm{WK}{The |axioms| still need conversion of attributes and actions!}
       axioms' :: [Named (FORMULA MF_FORMULA)]
       axioms' = map (mapNamed (convertFormula attrs actns)) axioms
  trace (unlines $
    ["basicMFLogicAnalysis before: extSig:"
    , show (text "   " <+> pretty extSig)
    ,"basicMFLogicAnalysis after: extSig':"
    , show (text "   " <+> pretty extSig')
    , "basicMFLogicAnalysis: axioms':"
    ] ++ map (\ a -> show . (text ("   " ++ senAttr a ++ ":" ) <+>) . pretty $ sentence a) axioms'
    ++ ["END basicMFLogicAnalysis"]
    ) $ return (spec, extSig', axioms')

-- | analyses MFLogic sentences only

mf_sen_analysis ::
        ( BASIC_SPEC MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA
        , MFSign
        , FORMULA MF_FORMULA
        ) -> Result (FORMULA MF_FORMULA)
mf_sen_analysis (bs, s, f) = let
    mix :: Mix MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA SignExtMF
    mix = ana_MFMix
    allIds = unite $
           ids_BASIC_SPEC (getBaseIds mix)
                          (getSigIds mix) bs
           : getExtIds mix (extendedInfo s) :
           [mkIdSets (allConstIds s) (allOpIds s)
           $ allPredIds s]
    mix' = mix { mixRules = makeRules emptyGlobalAnnos
                                      allIds }
  in trace ("mf_sen_analysis " ++ show f)
   $ liftM fst $ anaForm minExpForm mix' s f

-- | for mixfix analysis

ana_MFMix :: Mix MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA SignExtMF
ana_MFMix = emptyMix
    { getBaseIds = ids_MF_BASIC_ITEM
    , getSigIds = ids_MF_SIG_ITEM
    , getExtIds = \ mfsig -> {- let c = constructors e in
                                mkIdSets (opMapConsts c) (nonConsts c) Set.empty -}
        mkIdSets  (opMapConsts $ attrSig mfsig)
                  (nonConsts $ attrSig mfsig)
                  (MapSet.keysSet $ actnSig mfsig)
          -- ^ will have to change this line
    , putParen = mapMF_FORMULA
    , mixResolve = resolveMF_FORMULA             -- ^ will have to address 
    }

    
ids_MF_BASIC_ITEM :: MF_BASIC_ITEM -> IdSets
ids_MF_BASIC_ITEM ci = case ci of
                _ -> emptyIdSets
                
ids_MF_SIG_ITEM :: {- (s -> IdSets) -> -} MF_SIG_ITEM -> IdSets
ids_MF_SIG_ITEM {- f -} si = let e = Set.empty in case si of
    Att_items al _ -> (unite2 $ map (ids_OP_ITEM . item) al, e)
    Actn_items al _ -> ((e, e), Set.unions $ map (ids_PRED_ITEM . item) al)

resolveMF_FORMULA :: MixResolve MF_FORMULA  
resolveMF_FORMULA ga ids cf = case cf of
    FormX f ps -> do
       nf <- resolveMixFrm mapMF_FORMULA resolveMF_FORMULA ga ids f
       return $ FormX nf ps
    FormF f ps -> do
       nf <- resolveMixFrm mapMF_FORMULA resolveMF_FORMULA ga ids f
       return $ FormF nf ps
    Action sym tsOld ps-> do
       nf <- resolveMixFrm mapMF_FORMULA resolveMF_FORMULA ga ids $ Predication sym tsOld ps
       case nf of
            Predication sym' tsNew ps' -> return $ Action sym' tsNew ps'
            _ -> fail "unexpected resolveMixFrm for Action"
    BEG ps -> return cf 
    AttrSel opNam tsOld ps -> do
       nt <- resolveMixTrm mapMF_FORMULA resolveMF_FORMULA ga ids $ Application opNam tsOld ps
       case nt of
            Application opNam' tsNew ps' -> return $ AttrSel opNam' tsNew ps'
            _ -> fail "unexpected resolveMixTrm for AttrSel"
     
    TermX t ps -> do
       nt <- resolveMixTrm mapMF_FORMULA resolveMF_FORMULA ga ids t
       return $ TermX nt ps
    -- _ -> error "resolveMF_FORMULA"  
   
mapMF_FORMULA :: MF_FORMULA -> MF_FORMULA
mapMF_FORMULA = foldMF_Formula (mkMixfixRecord mapMF_FORMULA) mapMFRecord

foldMF_Formula :: Record MF_FORMULA a b -> MFRecord a b c -> MF_FORMULA -> c
foldMF_Formula r cr c = case c of
    FormX f ps -> foldFormX cr c (foldFormula r f) ps  
    FormF f ps -> foldFormF cr c (foldFormula r f) ps
    Action p ts ps -> foldAction cr c p (map (foldTerm r) ts) ps
    BEG ps         -> foldBEG cr c ps   -- ^ ??????????
    AttrSel o ts ps -> foldAttrSel cr c o (map (foldTerm r) ts) ps  -- ^ ??????
    TermX t ps      -> foldTermX cr c (foldTerm r t) ps
    

mapMFRecord :: MFRecord (FORMULA MF_FORMULA) (TERM MF_FORMULA) MF_FORMULA 
mapMFRecord = MFRecord
    { foldFormX   = const FormX
    , foldFormF   = const FormF
    , foldAction  = const Action
    , foldBEG     = const BEG    
    , foldAttrSel = const AttrSel
    , foldTermX   = const TermX
    }
    
data MFRecord a b c = MFRecord
    { foldFormX    :: MF_FORMULA -> a -> Range -> c
    , foldFormF    :: MF_FORMULA -> a -> Range -> c
    , foldAction   :: MF_FORMULA -> PRED_SYMB -> [b] -> Range -> c
    , foldBEG      :: MF_FORMULA -> Range -> c
    , foldAttrSel  :: MF_FORMULA -> OP_SYMB -> [b] -> Range -> c
    , foldTermX    :: MF_FORMULA -> b -> Range -> c
    }
    
    
     
minExpForm :: Min MF_FORMULA SignExtMF
minExpForm s form =
    let ops = formulaIds s
    in case form of
        FormX phi rng -> do
          phi' <- minExpFORMULA minExpForm s phi
          return $ FormX phi' rng
        FormF phi rng -> do
          phi' <- minExpFORMULA minExpForm s phi
          return $ FormF phi' rng
        Action  act terms pos -> do
            phi <- minExpFORMULA minExpForm s $  Predication act terms pos 
            case phi of
                 Predication act' terms' pos' -> return $ Action act' terms' pos'
                 _ -> fail "unexpected result of minExpForm for Action"
        BEG  rng -> return $ BEG  rng
        TermX phi rng -> do
          phi' <- oneExpTerm minExpForm s phi
          return $ TermX phi' rng
        AttrSel op terms pos -> do 
             phi <- oneExpTerm minExpForm s $ Application op terms pos 
             case phi of 
                  Application op' terms' pos' -> return $  AttrSel op' terms' pos'
                  _ -> fail "unexpected result of oneExpTerm for AttrSel"
        -- phi -> return phi

-- | static analysis of signature item s
    
ana_MF_SIG_ITEMS :: Ana MF_SIG_ITEM MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA SignExtMF
ana_MF_SIG_ITEMS mix si = let mef = minExpForm in
    case si of
    Att_items al ps ->
        do
           sign0 <- get
           ul <- mapM (ana_OP_ITEM mef mix) al
           sign1 <- get
           let opMapDiff = opMap sign1 `MapSet.difference` opMap sign0
               mfSig0 = extendedInfo sign0
               attMap0 = attrSig mfSig0
               attMap1 = attMap0 `MapSet.union` opMapDiff
           trace ("ana_MF_SIG_ITEMS: opMapDiff = " ++ show (pretty $ MapSet.toMap opMapDiff))
             $ put $ sign1 { extendedInfo = mfSig0 { attrSig = attMap1 }}
           return $ Att_items ul ps
    Actn_items al ps ->
        do sign0 <- get
           ul <- mapM (ana_PRED_ITEM mef mix) al
           sign1 <- get
           let predMapDiff = predMap sign1 `MapSet.difference` predMap sign0
               mfSig0 = extendedInfo sign0
               actnMap0 = actnSig mfSig0
               actnMap1 = actnMap0 `MapSet.union` predMapDiff
           trace ("ana_MF_SIG_ITEMS: predMapDiff = " ++ show (pretty $ MapSet.toMap predMapDiff))
             $ put $ sign1 { extendedInfo = mfSig0 { actnSig = actnMap1 }}
           return $ Actn_items ul ps

-- | static analysis of basic item b

ana_MF_BASIC_ITEM :: Ana MF_BASIC_ITEM MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA SignExtMF
ana_MF_BASIC_ITEM mix bi = fail "No basic item for analysis StatAna.hs"


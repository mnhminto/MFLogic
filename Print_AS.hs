{- |
Module      :  ./MFLogic/Print_AS.hs
Description :  pretty print abstract syntax of MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

printing AS_MFLogic and MFLogicSign data types
-}
 
module MFLogic.Print_AS where

import Common.Keywords
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import CASL.AS_Basic_CASL
import CASL.ToDoc
import qualified Common.Lib.MapSet as MapSet

import MFLogic.AS_MFLogic
import MFLogic.MFLogicSign

import Debug.Trace

instance Pretty MF_BASIC_ITEM where
    pretty = printMF_BASIC_ITEM
    
printMF_BASIC_ITEM :: MF_BASIC_ITEM -> Doc
printMF_BASIC_ITEM _ = plainText "printMF_BASIC_ITEM"

instance Pretty MF_SIG_ITEM where
    pretty = printMF_SIG_ITEM

printMF_SIG_ITEM :: MF_SIG_ITEM -> Doc
printMF_SIG_ITEM sis = case sis of
    Att_items l _ -> let
      d = topSigKey (attS ++ pluralS l) <+>
        let pp = printOpItem in
        if null l then empty else if case item $ last l of
            Op_decl _ _ a@(_ : _) _ -> case last a of
                Unit_op_attr {} -> False  -- use True for HasCASL
                _ -> False
            Op_defn {} -> False  -- use True for HasCASL
            _ -> False
        then vcat $ map (printSemiAnno pp True) l else semiAnnos pp l
      in trace ("printMF_SIG_ITEM.Attr: " ++ shows d "\n=====\n") d
    Actn_items l _ -> let
      d = topSigKey (actnS ++ pluralS l) <+>
        let pp = printPredItem in
        if null l then empty else if case item $ last l of
            Pred_defn {} -> True
            _ -> False
        then vcat $ map (printSemiAnno pp True) l else semiAnnos pp l
      in trace ("printMF_SIG_ITEM.Attr: " ++ shows d "\n=====\n") d


instance FormExtension MF_FORMULA where  

instance Pretty MF_FORMULA where
    pretty = printMF_FORMULA
    
printMF_FORMULA :: MF_FORMULA -> Doc
printMF_FORMULA cf = case cf of
    FormX f _ ->
      let fd = printFormula f
      in  text nextsS <+> parens fd  
    FormF f _ ->
      let fd = printFormula f
      in text futureS <+> parens fd 
    BEG _ ->
      text begS 
    Action act args rng -> 
      printFormula $ Predication act args rng
    AttrSel f as rng ->
      printTerm (Application f as rng)
    TermX f _ ->
      let fd = printTerm f
      in  text nextsS <+> parens fd  
    
    
instance Pretty SignExtMF where
    pretty = printMFLogicSign

printMFLogicSign :: SignExtMF -> Doc
printMFLogicSign s = printSetMap (text attS) empty (MapSet.toMap $ attrSig s)
                    $+$ printSetMap (text actnS) space (MapSet.toMap $ actnSig s)

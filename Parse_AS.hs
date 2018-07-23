{- |
Module      :  ./MFLogic/Parse_AS.hs
Description :  Parser for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

Parser for MFLogic
-}
{-# LANGUAGE ScopedTypeVariables #-}
module MFLogic.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations (PrefixMap)
import Common.Id
import Common.DocUtils
import Common.Keywords
import Common.Lexer
-- import Common.Parsec (reserved)
import Common.Token
import MFLogic.Print_AS ()
import MFLogic.AS_MFLogic
import Text.ParserCombinators.Parsec
import CASL.Formula
import CASL.Parse_AS_Basic (sigItems, basicSpec)
import CASL.OpItem (opItem, predItem)
import CASL.AS_Basic_CASL

import Debug.Trace


-- | signature items

-- attItems, actnItems, mfSigItems
--     :: (AParsable s, TermParser f) => [String] -> AParser st (SIG_ITEMS s f)

-- The purpose of these reserved words is probably to prevent them being picked up by the general parsers.
mf_reserved_words :: [String]
mf_reserved_words = [begS, nextsS, futureS, attS, attS ++ sS, actnS, actnS ++ sS]

attItems, actnItems :: [String] -> AParser st MF_SIG_ITEM
attItems ks = do
  x <- itemList ks attS opItem Att_items
  trace ("Parse.attItems: " ++ show (pretty x)) $ return x
actnItems ks = do
  x <- itemList ks actnS predItem Actn_items
  trace ("Parse.actnItems: " ++ show (pretty x)) $ return x

instance TermParser MF_FORMULA where
  termParser True = do
    pos0 <- getPos
    trace ("termParserMF True " ++ show pos0) $
      (do  -- parsing terms
        x <- asKey nextsS
        form <- term mf_reserved_words
        return . TermX form . Range $ tokenRange x
      )
{-
      <|>
      (do
      -- fail "parse attrSel application"
        w :: Token <- varId  mf_reserved_words
        trace ("MF.termParser " ++ show (tokStr w)) $ do
          let rng = Range $ tokenRange w
          return $ AttrSel (Op_name $ Id [w] [] rng) [] rng
          -- [] means no arguments yet.
      )
-}
  
  termParser False =   -- parsing formulae
    trace "termParserMF False" $
    (do
       b <- asKey begS
       return . BEG . Range $ tokenRange b)
    <|>
    (do
       x <- asKey nextsS
       form <- formula mf_reserved_words
       return . FormX form . Range $ tokenRange x
    )<|>
    (do
       x <- asKey futureS
       form <- formula mf_reserved_words
       return . FormF form . Range $ tokenRange x
    )
{-
    <|>
    (do
      -- parse Action application
        w :: Token <- varId mf_reserved_words
        trace ("MF.formulaParser " ++ show (tokStr w)) $ do
          let rng = Range $ tokenRange w
          -- args <- parseParenthesizedTerms (term mf_reserved_words)
          return $ AttrSel (Op_name $ Id [w] [] rng) [] rng
          -- to be converted to Action by extR argument to resolveMixFrm
          -- return $ Action (Pred_name $ Id [w] [] rng) [] rng
    )
-}

mfSigItems :: AParser st MF_SIG_ITEM
mfSigItems = attItems mf_reserved_words <|> actnItems mf_reserved_words

{-
mfSigItems ks = fmap Ext_SIG_ITEMS aparser <|>
           sortItems ks <|> opItems ks <|> predItems ks <|> typeItems ks
-}

instance AParsable MF_BASIC_ITEM where
  aparser = fail "No MF_BASIC_ITEM can be parsed."

instance AParsable MF_SIG_ITEM where
  aparser = mfSigItems

parseSenMF :: AParser st (FORMULA MF_FORMULA)
parseSenMF = formula mf_reserved_words

-- | MF_BASIC_SPEC:: (BASIC_SPEC MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA)

basicSpecMF :: PrefixMap -> AParser st MF_BASIC_SPEC
basicSpecMF pm = trace ("basicSpecMF") $ do
  sp0 <- basicSpec mf_reserved_words pm
  return $ {- let sig0 = sign sp0 in -} sp0
{-
    { sign = sig0
       {opMap = opMap sig0 `MapSet.difference` attrMapSig (extededInfo sig0)
       ,predMap = ...
       }
    , axioms = mapFormula (opToAttr and predToAction) $ axioms sp0
    }
-}

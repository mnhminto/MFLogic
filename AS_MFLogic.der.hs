{-# LANGUAGE GADTs, EmptyDataDecls, DeriveDataTypeable #-}
{- |
Module      :  ./MFLogic/AS_MFLogic.der.hs
Description :  Abstract syntax for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisionalPortability :  portable

Abstract syntax for MFLogic, a modal dynamic logic.It uses/extends CASL and 
  Only the added syntax is specified
-}

module MFLogic.AS_MFLogic where

import Common.Id
import Common.AS_Annotation

import CASL.AS_Basic_CASL

import Data.Data

-- DrIFT command
{-! global: GetRange !-}

-- | A Type synonym of the data type BASIC_SPEC mentioned in module CASL.AS_Basic_CASL

type MF_BASIC_SPEC = BASIC_SPEC MF_BASIC_ITEM MF_SIG_ITEM MF_FORMULA




-- | A Type synonym of data type Annoted mentioned in module Common.AS_Annotation

type AnModFORM = Annoted (FORMULA MF_FORMULA)

 -- | Empty Data type Declaration


data MF_BASIC_ITEM =
    Unused_MF_BASIC_ITEM Range
  deriving (Typeable)

instance Show MF_BASIC_ITEM where
-- instance Typeable MF_BASIC_ITEM where
instance Data MF_BASIC_ITEM where

                  
-- | Extended signature item only

data MF_SIG_ITEM  = Att_items [Annoted (OP_ITEM MF_FORMULA)] Range      -- Attribute Signature
                  | Actn_items [Annoted (PRED_ITEM MF_FORMULA)] Range   -- Action Signature
                    deriving (Show, Typeable, Data)
                    
-- | Extended forulas

data MF_FORMULA
    -- Formula constructors:
    = FormX (FORMULA MF_FORMULA) Range          -- ^ X, i.e., next applied to a formula is a formula
    | FormF (FORMULA MF_FORMULA) Range          -- ^ F, i.e., future applied to a formula is a formula
    | Action PRED_SYMB [TERM MF_FORMULA] Range  -- ^ Action predicate is a formula
    | BEG Range -- Begining of time is a formula
    -- Term constructors:
    -- is this synactic distinction necessary?
    | AttrSel OP_SYMB [TERM MF_FORMULA] Range   -- ^ Attribute application 
    | TermX (TERM MF_FORMULA) Range             -- ^ X applied to Term.
    deriving (Show, Eq, Ord, Typeable, Data)                     

                 
                 

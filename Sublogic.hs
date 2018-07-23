{- |
Module      :  ./MFLogic/Sublogic.hs
Description :  sublogic analysis for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2017-2018
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs)
  for MFLogic. It is based on the respective functions for CASL.

-} 

module MFLogic.Sublogic
    ( MFLogic_Sublogics
    , minFormSublogicMF
    , minMFSigItem
    , setMFFeature
    ) where

import Common.AS_Annotation
import CASL.AS_Basic_CASL (FORMULA(Predication), TERM(Application))
import CASL.Sublogic
import MFLogic.AS_MFLogic

-- | type for MFLogic sublogics

type MFLogic_Sublogics = CASL_SL Bool

hasMFFeature :: MFLogic_Sublogics -> Bool
hasMFFeature = ext_features

setMFFeature :: Bool -> MFLogic_Sublogics -> MFLogic_Sublogics
setMFFeature b s = s { ext_features = b }

theMFFeature :: MFLogic_Sublogics
theMFFeature = setMFFeature True bottom

minFormSublogicMF :: MF_FORMULA -> MFLogic_Sublogics
minFormSublogicMF cf = case cf of
    FormX f _ ->
        sublogics_max theMFFeature $ sl_sentence minFormSublogicMF f
    FormF f _ ->
        sublogics_max theMFFeature $ sl_sentence minFormSublogicMF f    
    BEG _ -> theMFFeature
      
    Action act args rng -> sublogics_max theMFFeature . sl_sentence minFormSublogicMF
        $ Predication act args rng
    AttrSel f as rng -> sublogics_max theMFFeature . sl_term minFormSublogicMF
        $ Application f as rng
    TermX f _ -> sublogics_max theMFFeature $ sl_term minFormSublogicMF f

minMFSigItem :: MF_SIG_ITEM -> MFLogic_Sublogics
minMFSigItem (Att_items l _) = foldr (sublogics_max . sl_op_item minFormSublogicMF . item) theMFFeature l
minMFSigItem (Actn_items l _) = foldr (sublogics_max . sl_pred_item minFormSublogicMF . item) theMFFeature l

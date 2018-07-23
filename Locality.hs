{- |
Module      :  ./MFLogic/Locality.hs
Description :  Locality axiom generation for MFLogic
Copyright   :  (c) Md Nour Hossain, Wolfram Kahl, 2018
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  portable

Locality axioms [Fiadeiro-Maibaum-1992] are implicit axioms
the preservation of which needs to be checked for morphisms;
they therefore enter colimits.

-}

module MFLogic.Locality where
import MFLogic.StatAna (MFSign)
import MFLogic.MFLogicSign
import MFLogic.AS_MFLogic
import CASL.Sign (OpType(..), PredType(..), OpMap, PredMap, Sign(..))
-- | import CASL.Utils ()
import CASL.AS_Basic_CASL (FORMULA(..), QUANTIFIER(..), Junctor(..), VAR_DECL(..), SORT, VAR, TERM(..)
                          ,OP_NAME, PRED_NAME, PRED_SYMB(..), OP_SYMB(..)
                          ,conjunct, disjunct, mkVarDecl, mkVarTerm, mkStEq  )
-- | import qualified CASL.Morphism as Mor

import Common.Id (nullRange, mkSimpleId)

-- import Common.Doc (Doc, sepByCommas)
-- import Common.DocUtils (Pretty(..), printMap, pairElems)
-- import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

-- import Data.Data
-- import qualified Data.Map as Map

type FormulaMF = FORMULA MF_FORMULA
type TermMF = TERM MF_FORMULA

type SortedVar = (VAR , SORT)

mkVar :: String -> Int -> VAR
mkVar s i = mkSimpleId $ s ++ '_' : show i

sortedVarsDECL :: [SortedVar] -> [VAR_DECL]
               -- one could merge consecutive equal sorts.
sortedVarsDECL = map (uncurry mkVarDecl)

sortedVar :: SortedVar -> TermMF
sortedVar = uncurry mkVarTerm

mkSortedVars :: String -> [SORT] -> [SortedVar]
mkSortedVars s = zipWith h [1..]
  where
    h i sort = (mkVar s i, sort)

mfXterm :: TermMF -> TermMF
mfXterm t = ExtTERM $ TermX t nullRange

conjunction, disjunction :: [FormulaMF] -> FormulaMF
conjunction = conjunct
disjunction = disjunct

forallQ, existsQ :: [SortedVar] -> FormulaMF -> FormulaMF
forallQ vs f = Quantification Universal (sortedVarsDECL vs) f nullRange
existsQ vs f = Quantification Existential (sortedVarsDECL vs) f nullRange

equals :: TermMF -> TermMF -> FormulaMF
equals = mkStEq

localityAxiom :: MFSign -> Maybe FormulaMF  -- |Nothing| for $\true$
localityAxiom sign = let
    signMF = extendedInfo sign
    attrMap :: OpMap
    attrMap = attrSig signMF
    actnMap :: PredMap
    actnMap = actnSig signMF
    attrConstraints :: OP_NAME -> [OpType] -> [FormulaMF]
    attrConstraints attr = map (attrConstraint attr)
    attrConstraint :: OP_NAME -> OpType -> FormulaMF
    attrConstraint attr ty = let
        argSorts = opArgs ty
        argSortedVars = mkSortedVars "y" argSorts
        argVarTerms = map sortedVar argSortedVars
        attrAppl = ExtTERM $ AttrSel (Op_name attr) argVarTerms nullRange
        eq = equals (mfXterm attrAppl) attrAppl
      in if null argSorts
        then eq -- don't quantify over empty variable list
        else forallQ argSortedVars eq
    existsActions :: PRED_NAME -> [PredType] -> [FormulaMF]
    existsActions actn = map $ existsAction actn
    existsAction :: PRED_NAME -> PredType -> FormulaMF
    existsAction actn ty = let
        argSorts = predArgs ty
        argSortedVars = mkSortedVars "x" argSorts
        argVarTerms = map sortedVar argSortedVars
        actnAppl = ExtFORMULA $ Action (Pred_name actn) argVarTerms nullRange
      in if null argSorts
        then actnAppl -- don't quantify over empty variable list
        else existsQ argSortedVars actnAppl
  in if MapSet.null attrMap then Nothing
  else let
      attrPart :: FormulaMF
      attrPart = conjunction . concatMap (uncurry attrConstraints) $ MapSet.toList attrMap
      actnPart :: [FormulaMF]
      actnPart = concatMap (uncurry existsActions) $ MapSet.toList actnMap
    in Just $ disjunction (actnPart ++ [attrPart])

{- |
Module      :  ./MFLogic/ComputeZigZagTrans.hs
Description :  compute ZigZag Graph Transformation
Copyright   :  (c) Md. Nour Hossain, and Wolfram Kahl , 2017 -2018
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hossaimn@mcmaster.ca
Stability   :  provisional
Portability :  non-portable

For a given  Diagram (DevGraph), this module collects the 
description (specification) of the components,
get the morphisms, 
the system architecture (Set of nodes and morphism of an diagram),
the system architecture zigzag homomorphism, 
extracts the span, calculates the cospan by performing 
the zigzag graph transformation, implements different helper 
functions to perform the transformation and 
finally return the result architecture.

-}
{-# LANGUAGE ExistentialQuantification, FunctionalDependencies, FlexibleContexts, PatternGuards #-}

module MFLogic.ComputeZigZagTrans where
import MFLogic.AS_MFLogic
import MFLogic.MFLogicSign
import MFLogic.Parse_AS (basicSpecMF)
import MFLogic.Logic_MFLogic
import MFLogic.Locality
import MFLogic.Sublogic
import MFLogic.StatAna
import MFLogic.MFSymbol
import Common.ExtSign
import Common.GlobalAnnotations (emptyGlobalAnnos)
import Common.GraphAlgo 
import CASL.AS_Basic_CASL (SYMB_ITEMS, SYMB_OR_MAP, SYMB_MAP_ITEMS(Symb_map_items), FORMULA,BASIC_ITEMS(Axiom_items),BASIC_SPEC(Basic_spec) )
import CASL.Sign (emptySign, extendedInfo)
import CASL.Morphism (RawSymbol, idMor, Morphism(..))
import Logic.Logic
  ( Logic, Language(language_name)
  , Sentences(map_sen)
  , StaticAnalysis( basic_analysis, induced_from_to_morphism, stat_symb_map_items, signature_colimit, morphism_union)
  , Syntax(parse_symb_map_items)
  , Category(composeMorphisms,inverse)
  , basicSpecPrinter
  ) 
import Logic.Grothendieck
import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.AS_Architecture
import Common.Id
import Common.IRI

import Static.DevGraph
import Common.LibName
import Common.Result
import Common.AS_Annotation
import Common.AnnoState (emptyAnnos)

import Common.Doc (text, (<+>), ($+$), vcat, vsep )
import Common.DocUtils (Pretty, pretty)

import qualified Common.Lib.MapSet as MapSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Graph.Inductive.Graph as Graph
import Common.Lib.Graph (Gr)
import qualified Data.Set as Set
import Data.Maybe (maybeToList,listToMaybe,fromJust,mapMaybe)
import Text.ParserCombinators.Parsec (runParser, (<|>), eof, many)

import Debug.Trace

-- | nodeName or SpecName type 
 
type MF_SPEC_NAME = String -- ^ IRI too complicated for now

type MF_DIAGNODE_NAME = String  -- ^ Atchitecture name Type, i.e., L,  R, A 
type MF_SAHom_NAME = String  -- ^ unused
type MF_MOR_NAME = String -- ^ Morphism name type 

-- | System Architecture Names
 
data SysArch = SysArch
  { sa_nodes :: Set MF_SPEC_NAME  -- ^ A set of Node Names
  , sa_edges :: Set MF_MOR_NAME   -- ^ A set of Morphism Names
    
  }deriving (Show)

-- | System Architecture with actual specification and morphism
 
data SysArchReal obj mor = SysArchReal 
  { sa_specs :: obj   -- ^ A map from Node Name to it's specification, e.g., Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))
  , sa_mors :: mor    -- ^ A map from morphism Name to it's morphism, e.g.,(Map MF_MOR_NAME MorphismMF) 
    
  }

data InterimSpec = InterimSpec
  { isSign :: MFSign
  , isAxioms :: [Annoted (FORMULA MF_FORMULA)]
  }

instance Show InterimSpec where showsPrec _ = shows . pretty

instance Pretty InterimSpec where
  pretty (InterimSpec sign axioms) = pretty sign $+$ pretty (Axiom_items axioms nullRange :: MF_BASIC_ITEMS)
{-
data SysArchReal obj mor = SysArchReal 
  { sa_specs :: Map MF_SPEC_NAME obj   -- ^ A map from Node Name to it's specification, e.g., Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))
  , sa_mors :: Map MF_MOR_NAME mor    -- ^ A map from morphism Name to it's morphism, e.g.,(Map MF_MOR_NAME MorphismMF) 
    
  }
-}

instance (Pretty obj, Pretty mor) => Show (SysArchReal obj mor) where
  showsPrec _ = shows . pretty

instance (Pretty obj, Pretty mor) => Pretty (SysArchReal obj mor) where
  pretty sa =
    vcat (text "MF_SYSARCH_DIAGRAM"
          : (text "  sa_specs:" <+> pretty (sa_specs sa))
          : (text "  sa_mors:" <+> pretty (sa_mors sa))
          : []
         )
{-
instance (Pretty obj, Pretty mor) => Pretty (SysArchReal obj mor) where
  pretty sa =
    vcat (text "MF_SYSARCH_DIAGRAM"
          : (text "  sa_specs:" <+> vcat (map (\ (k, v) -> text (show k) <+> pretty v) (Map.toList (sa_specs sa))))
          : (text "  sa_mors:" <+> vcat (map (\ (k, v) -> text (show k) <+> pretty v) (Map.toList (sa_mors sa))))
          : []
         )
-}

{- | System Architecture Zpath Homomorphism consists of node Name map and
edge Name map.
The sazh0_nodeMap  maps Node Name of an architecture to the pair
of a 'target' node Name and  'morphism' Name of  another architecture. 
the sazh0_edgeMap is a map between two morphism Names. 
Here the type Bool represent the direction.
sazh0_edgeMap can be of two types: 
a) single morpshim Name to single morphism Name map (Signleton list), e.g., 
"ST2S_L"  [("ST2X_R", True)] or
b) a single morphism to zigzag path map, e.g., 
"ST2S_L"  [("ST2X_R", True), ("Q2X_R", False), ("Q2S_S", True)]
-}

data SysArchZPHom0 = SysArchZPHom0
  { sazh0_nodeMap :: Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME) 
  , sazh0_edgeMap :: Map MF_MOR_NAME [(MF_MOR_NAME, Bool)] 
  }deriving (Show)


{-|
System Architecture Zpath Homomorphism consists of spec map and morphism map.
The |sazh_nodeMap|  maps node Name of an architecture to the node Name , node sprcification,
morphism Name and the morphism of  another architecture. 
The |sazh_edgeMap| is a map between a morphism Name to a list of morphism Name, the morphsim
and the direction in another architecture. Oviously, it can be of two types:
a) single to single, e.g., "ST2S_R"  [("ST2S_R_B", morphism, True)] or
b) single morphism to zigzag path, e.g., 
"ST2S_R"  [("ST2S_R_B", morphism, True), ("Q2X_R_B", morphism, False), ("Q2S_R_B", morphism, True)]
-}

data SysArchZPHom obj= SysArchZPHom
  { sazh_nodeMap :: Map MF_SPEC_NAME ((MF_SPEC_NAME, obj), (MF_MOR_NAME, MorphismMF))
 , sazh_edgeMap :: Map MF_MOR_NAME [(MF_MOR_NAME, MorphismMF,Bool)] 
  }deriving (Show)

emptySysArchZPHom :: SysArchZPHom obj
emptySysArchZPHom = SysArchZPHom Map.empty Map.empty


-- | the 'SysArchNodeLabel' is a record consisting three record elements, i.e.,
-- | the basic specification, the range and
-- | the extended signature (plain signature + symbol) 

data SysArchNodeLabel = SysArchNodeLabel
  { sanl_BasicSpec :: MF_BASIC_SPEC
  , sanl_BasicSpecRange :: Range
  , sanl_ExtSig :: ExtSignMF 
  } deriving (Show)



instance Pretty SysArchNodeLabel where
  pretty sanl = vsep
    [text "sanl_BasicSpec:" <+> pretty (sanl_BasicSpec sanl)
    ,text "sanl_BasicSpecRange:" <+> pretty (sanl_BasicSpecRange sanl)
    ,text "sanl_ExtSig:" <+> pretty (sanl_ExtSig sanl)
    ]
instance Pretty SysArch where
  pretty sarch = vsep
    [text "sa_nodes:" <+> pretty (sa_nodes sarch)
    ,text "sa_edges:" <+> pretty (sa_edges sarch)
    ]

instance Pretty SysArchZPHom0 where
  pretty sazh = vsep
    [text "sazh0_nodeMap:" <+> pretty (sazh0_nodeMap sazh)
    ,text "sazh0_edgeMap:" <+> pretty (sazh0_edgeMap sazh)
    ]
instance Pretty Bool where
    pretty = text . show

{- |
The following |MF_SYSARCH_DIAGRAM|  data type consists of the 
folowing four record elements:
a) |mfsaDiag_allSpecs| : all spec name to specificaiton map 
for all the architectures, i.e., L, R, A, .....

b) |mfsaDiag_allMors|: all the morphism maps between two architecture, L -> A, L -> R, P0-> A,
  P1-> A ....

c) |mfsaDiag_nodes|: The set of node names and morphism names of all architectures, e.g.,
L -> Record (Set, Set), R -> Record (Set, Set) , ....

d) |mfsaDiag_edges|: ZedHomomorphism between two architecture, e.g.,
(L,A) -> Zhom, (L,R) -> Zhom, .....

-}

data MF_SYSARCH_DIAGRAM = MF_SYSARCH_DIAGRAM
  { mfsaDiag_allSpecs :: Map  MF_SPEC_NAME SysArchNodeLabel
  , mfsaDiag_allMors :: Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
  , mfsaDiag_nodes :: Map MF_DIAGNODE_NAME SysArch 
  , mfsaDiag_edges ::  Map (MF_DIAGNODE_NAME, MF_DIAGNODE_NAME) SysArchZPHom0                          
  }


instance Show MF_SYSARCH_DIAGRAM where
  showsPrec _ sa = shows $
    vcat (text "MF_SYSARCH_DIAGRAM"
          : (text "  allSpecs:" <+> vcat (map (\ (k, v) -> text (show k) <+> pretty v) (Map.toList (mfsaDiag_allSpecs sa))))
          : (text "  allMors:" <+> vcat (map (\ (k, v) -> text (show k) <+> pretty v) (Map.toList (mfsaDiag_allMors sa))))
          : (text "  nodes:" <+> vcat (map (\ (k, v) -> text (show k) <+> pretty v) (Map.toList (mfsaDiag_nodes sa))))
          : (text "  edges:" <+> vcat (map (\ (k, v) -> text (show k) <+> pretty v) (Map.toList (mfsaDiag_edges sa))))
          : []
         )

-- | (for node part of |mfsaDiag_nodes|, calculate inverse: Map MF_SPEC_NAME MF_DIAGNODE_NAME)

unBSpec :: G_basic_spec -> Maybe MF_BASIC_SPEC
unBSpec (G_basic_spec lid bspec) = case language_name lid of
    "MFLogic" -> case  basicSpecPrinter Nothing lid of
      Nothing -> Nothing
      Just printer -> case runParser (basicSpecMF prefMap) annos "unBSpec" (show $ printer bspec) of
        Left _e -> Nothing
        Right mfBSpec -> Just mfBSpec
    _ -> Nothing
  where
   prefMap = Map.empty -- what is this?
   annos = emptyAnnos ()

-- | Interestingly, the spec name ends up in differen pkaces in the |SPEC_NAME| |IRI|...

unGSpec :: Map MF_SPEC_NAME (Maybe SysArchNodeLabel) -> SPEC -> [MF_BASIC_SPEC]
unGSpec _nodes (Syntax.AS_Structured.Basic_spec gbspec rng) = maybeToList $ unBSpec gbspec
unGSpec nodes (Extension aspecs _) = concatMap (\ (Annoted spec _ _ _) -> unGSpec nodes spec) aspecs
unGSpec nodes (Spec_inst spName [] Nothing _rng) -- restricting to no |FIT_ARG|s and no |IRI|
  = trace ("unGSpec: spName: iriPath = " ++ iriPath spName ++ "; iriQuery = " ++ iriQuery spName ++
              "; prefixName = " ++ prefixName spName ++ "; abbrevPath = " ++ abbrevPath spName ++
              "; abbrevQuery = " ++  abbrevQuery spName) $
    case Map.lookup (abbrevPath spName) nodes of
     Just (Just sanl) -> [sanl_BasicSpec sanl]
     _ -> trace ("unGSpec Spec_inst: " ++ shows spName " not found!") [] -- should this throw an error?
unGSpec _nodes s = trace ("unGSpec: Encountered: " ++ show s) []


unGSymbMapItemsList :: G_symb_map_items_list -> [SYMB_MAP_ITEMS]
unGSymbMapItemsList gSMIList = case parse_symb_map_items MFLogic of
    Nothing -> []
    Just parser -> let parser' = many parser
      in case runParser parser' annos "unGSymbMapItemsList" gmiString of
        Left e ->  trace ("unGSymbMapItemsList: " ++ shows e "\n   ``" ++ gmiString ++ "''")
                   []
        Right r -> r
  where
    annos = emptyAnnos ()
    gmiString = show $ pretty gSMIList

-- | Extract |MF_SYSARCH_DIAGRAM| form Library Environment of a given |DGraph|

extractSysArchDiagramFromLibEnv :: DGraph -> MF_SYSARCH_DIAGRAM 
extractSysArchDiagramFromLibEnv dgraph = trace "========= extractSysArchFromLibEnv =========" $
  let
    Just (specDfn@(Lib_defn _ aItems _ _)) = optLibDefn dgraph
    morphiMap :: Map.Map MorId G_morphism
    morphiMap = morMap dgraph
    edges =  morphiMap 
    nodes = foldr h Map.empty aItems
    h (Annoted (Spec_defn spName  _ (Annoted spec r_spec _ _) r) _ _ _)
      = let  name = drop 1 $ abbrevQuery spName
             mfbspecs = trace ("extractSysArchFromLibEnv.h: spName: iriPath = " ++ iriPath spName ++ "; iriQuery = " ++ iriQuery spName ++
                 "; prefixName = " ++ prefixName spName ++ "; abbrevPath = " ++ abbrevPath spName ++
                 "; abbrevQuery = " ++  abbrevQuery spName) $
               trace ("extractSysArchFromLibEnv: Found spec " ++ show spName ) $ unGSpec nodes spec
             result = (\ bspec -> (bspec, r_spec)) <$> concatMFBasicSpecs mfbspecs
             mExtSig = do
               bspec <- fst <$> result
               basicAna <- basic_analysis MFLogic
               (bspec', extSig, namedAxioms) <- maybeResult
                   $ basicAna (bspec, emptySign emptyMFLogicSign, emptyGlobalAnnos)
               trace (show $ text ("extractSysArchFromLibEnv.h " ++ shows name ":")
                      <+> pretty extSig) $
                 Just extSig
             result' = case result of
               Nothing -> Nothing
               Just (bSpec, rng) -> case mExtSig of
                 Nothing -> error $
                   "extractSysArchFromLibEnv: ExtSig extraction failed for " ++ show name
                 Just extSig -> Just $ SysArchNodeLabel
                   { sanl_BasicSpec = bSpec
                   , sanl_BasicSpecRange = rng
                   , sanl_ExtSig = extSig
                   }
      in trace ("extractSysArchFromLibEnv: Inserting potential MF_BASIC_SPEC " ++ show spName ++ " as " ++ show name) $
          Map.insert name result'
    h _ = id
    nodes' = Map.foldWithKey (\ k mSNAL -> case mSNAL of
       Nothing -> id
       Just snal -> Map.insert k snal
      ) Map.empty nodes
    allMors = extractMorphismsFromLibEnv dgraph nodes'
    nodes'' = addMorphismsToSysArch (extractSysArchDiagramNodesFromLibEnv dgraph ) allMors
  in 
     MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = nodes'
        , mfsaDiag_allMors   = allMors
        , mfsaDiag_nodes     = nodes''
        , mfsaDiag_edges     = extractSysArchZHom nodes'' allMors
        }
{-|
Returns info  related to core architectured, i.e., L,R,A only.
Removes all the assisting architectures and their information, i.e.,
allSpec, Mormap, arch info, zhom.... 
The morphism map does not remove the zmap morphism maps, 
removes only internal morphisms. 
-}

extractCoreFromSysArchDiagram ::  MF_SYSARCH_DIAGRAM -> MF_SYSARCH_DIAGRAM
extractCoreFromSysArchDiagram sysArch = let
      nodeNameSpecMap = mfsaDiag_allSpecs sysArch
      morNameMorMap   = mfsaDiag_allMors sysArch
      diagNameArchMap = mfsaDiag_nodes sysArch
      diagNodesZHom   = mfsaDiag_edges sysArch
      diagNodesSet = Map.keysSet diagNodesZHom
      auxDiagNodesSet = Set.foldr n Set.empty diagNodesSet
      n (sdName,tdName) p 
          | Set.member (sdName,fromJust art) diagNodesSet' = p
          | otherwise = Set.insert sdName p
          where
          diagNodesSet' = Set.delete (sdName, tdName) diagNodesSet
          art = Set.foldr intf Nothing diagNodesSet'
          intf (sa,ta) p
                     | sa == sdName = Just ta
                     | otherwise = p
      auxNodeSet = Map.foldrWithKey fn Set.empty diagNameArchMap
      fn archName arch p
           | Set.member archName auxDiagNodesSet = Set.union (sa_nodes arch) p
           | otherwise = p
      auxMorSet  = Map.foldrWithKey fe Set.empty diagNameArchMap
      fe archName arch p
           | Set.member archName auxDiagNodesSet = Set.union (sa_edges arch) p
           | otherwise = p

      coreNodeNameSpecMap = Set.foldr fnmap nodeNameSpecMap auxNodeSet
      fnmap n = Map.delete n

      corMorNameMorMap   = Set.foldr fmmap morNameMorMap auxMorSet  -- ^ does not remove the zhom between P0 -> A
      fmmap m = Map.delete m

      coreDiagNameArchMap = Set.foldr fArch diagNameArchMap auxDiagNodesSet
      fArch a = Map.delete a

      coreDiagNodesZHom = Set.foldr fZhom diagNodesZHom auxDiagNodesSet
      fZhom ars = Map.delete (ars,fromJust art)
          where art = Map.foldrWithKey intf Nothing diagNodesZHom
                intf (sa,ta) val p
                     | sa == ars = Just ta
                     | otherwise = p
      in MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = coreNodeNameSpecMap
        , mfsaDiag_allMors   = corMorNameMorMap
        , mfsaDiag_nodes     = coreDiagNameArchMap
        , mfsaDiag_edges     = coreDiagNodesZHom
        }
{-|
 Three objects and two morphsims of a span.
-}
 
data Span obj mor = Span
  { spanL, spanR, spanA :: obj
  , spanLtoR, spanLtoA :: mor
  } deriving (Show)

{-|
Name of the architectures of a span
objName : MF_DIAGNODE_NAME , e.g., L, R, A
-}
data SpanByName objName = SpanByName { sbnL, sbnR, sbnA :: objName } deriving (Show)

instance Pretty objName =>  Pretty (SpanByName objName) where
  pretty spanNodeNames = vsep
    [text "sbnL:" <+> pretty (sbnL spanNodeNames)
    ,text "sbnR:" <+> pretty (sbnR spanNodeNames)
    ,text "sbnA:" <+> pretty (sbnA spanNodeNames)
    ]

-- | type synonym of |Span| data type

type MFSpecSpan = Span MF_SPEC_NAME MF_MOR_NAME -- argument for calculating an individual Spec-pushout

-- | unused

type SADSpan = Span SysArch SysArchZPHom0

{-|
Single object and two morphisms of a CoSpan.
-}

data POResultCospan obj mor = POResultCospan { porcObj :: obj, porcR2B, porcA2B :: mor } deriving (Show)

instance (Pretty obj, Pretty mor) => Pretty (Span obj mor)  where
  pretty span = vsep
    [text "spanL" <+> pretty (spanL span)
    ,text "spanR" <+> pretty (spanR span)
    ,text "spanA" <+> pretty (spanA span)
    ,text "spanLtoR" <+> pretty (spanLtoR span)
    ,text "spanLtoA" <+> pretty (spanLtoA span)
    ]

{-| From a system architecture diagram, this funciton extracts
the name of the three architectures that belong to the span, 
e.g., L, A, R.
If there is no span, it will retunt Nothing.
 
-}

extractArchNodesNameOfaSpan :: MF_SYSARCH_DIAGRAM -> Maybe (SpanByName MF_DIAGNODE_NAME) -- ^ |Nothing| if not a span.
extractArchNodesNameOfaSpan (MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = nodeNameSpecMap
        , mfsaDiag_allMors   = morNameMorMap
        , mfsaDiag_nodes     = diagNameArchMap
        , mfsaDiag_edges     = diagNodesZHom
        }) = let
    sArchKeyList = Map.keys diagNodesZHom
    (hl, ha) = head sArchKeyList
    (ll, lr) = last sArchKeyList
    in if hl == ll
          then Just SpanByName {sbnL = hl, sbnA = ha, sbnR = lr }
          else Nothing

{-| For a given system architecture diagram, and 
three architecture names of a architecture span (L,A,R), 
this function returns 
three system architectures name and their system architecture as a pair, i.e.,
(L, SysArch_L), (A,SysArch_A), (R,SysArch_R)
where a system arcitecture is the set of node names and 
the set of morphism names. 
The span morphisms are nested pairs, 
e.g., ((L,R), SysArchZPHom0_LR) and ((L,A), SysArchZPHom0_LA)
that contains source and target achitecture name as a pair and 
a system architecute zpath homomorphism between these two architectures.

-}

extractSystemArchAndZhom  :: MF_SYSARCH_DIAGRAM
       -> SpanByName MF_DIAGNODE_NAME
       -> Maybe (Span (MF_DIAGNODE_NAME, SysArch) ((MF_DIAGNODE_NAME, MF_DIAGNODE_NAME), SysArchZPHom0))
extractSystemArchAndZhom (MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = nodeNameSpecMap
        , mfsaDiag_allMors   = morNameMorMap
        , mfsaDiag_nodes     = diagNameArchMap
        , mfsaDiag_edges     = diagNodesZHom
        }) (SpanByName { sbnL = leftDiag , sbnR = rightDiag , sbnA = applDiag }) = do
          leftArch <-  Map.lookup leftDiag diagNameArchMap
          rightArch <- Map.lookup rightDiag diagNameArchMap
          applArch <- Map.lookup applDiag diagNameArchMap
          spanLeftToRightZhom <- Map.lookup (leftDiag, rightDiag) diagNodesZHom
          spanLeftToApplicaZhom <- Map.lookup (leftDiag, applDiag) diagNodesZHom
          Just Span
            { spanL = (leftDiag,leftArch)
            , spanR = (rightDiag,rightArch)
            , spanA = (applDiag,applArch)
            , spanLtoR = ((leftDiag, rightDiag), spanLeftToRightZhom)
            , spanLtoA = ((leftDiag, applDiag), spanLeftToApplicaZhom)
            }
{-| 
The purpose of this function is to generate a compelte result architecture. 
As arguments this funciton takes 
a) a system architecture diagram
b) a span,i.e., left, right, application architecture and zhom between L->R and L->A,
c) The result architecture name(B), and
d) Result architecture nodes to  specification maps, and 
zHom between R-> B and A -> B.
As a result it will return a complete result system architecture, i.e., 
the node specifications and the morphisms.

-} 


completeResultCoSpan :: MF_SYSARCH_DIAGRAM 
      -> Span (MF_DIAGNODE_NAME, SysArch) ((MF_DIAGNODE_NAME, MF_DIAGNODE_NAME), SysArchZPHom0)
      -> MF_DIAGNODE_NAME -- ^ ``B'' 
      -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF))
                        (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
      -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME ((MF_SPEC_NAME,MF_SPEC_NAME),MorphismMF)))
                        (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))

completeResultCoSpan
    archDiag@(MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = nodeNameSpecMap     -- ^ all specifications name to specificaiton map 
        , mfsaDiag_allMors   = morNameMorMap       -- ^ all morphisms name to morphism map
        , mfsaDiag_nodes     = diagNameArchMap     -- ^ all architecture, node and edge sets 
        , mfsaDiag_edges     = diagNodesZHom       -- ^ sysarchZhom0, i.e., node and edge map  L-->A, L--->R
        })
    (Span
         { spanL = (leftDiag,leftArch)
         , spanR = (rightDiag,rightArch)
         , spanA = (applDiag,applArch)
         , spanLtoR = ((_leftDiag, _rightDiag), spanLeftToRightZhom)
         , spanLtoA = ((_leftDiag', _applDiag), spanLeftToApplicaZhom)
         })
    resArch
    coSpan@(POResultCospan {
         porcObj = object@(SysArchReal 
                  { sa_specs = specMap
                   ,sa_mors = morphMap
                   })
        , porcR2B = morr2b@(SysArchZPHom
                  { sazh_nodeMap = r2bZhomSpecMap
                   , sazh_edgeMap = r2bZhomMorMap
                  })
        , porcA2B = mora2b@(SysArchZPHom
                  { sazh_nodeMap = a2bZhomSpecMap
                   , sazh_edgeMap = a2bZhomMorMap                
                  })
        })
    = let 
         leftArchNodeSet = sa_nodes leftArch       -- ^ left Arch node name set
         leftArchEdgeSet = sa_edges leftArch       -- ^ left Arch edge name set
         rightArchEdgeSet = sa_edges rightArch     -- ^ right Arch edge name set
         applArchEdgeSet = sa_edges applArch       -- ^ application Arch edge name set
         zhomNodeMapL2R = sazh0_nodeMap spanLeftToRightZhom     -- ^ sys archz node map bettwen L2R
         zhomEdgeMapL2R = sazh0_edgeMap  spanLeftToRightZhom    -- ^ sys archz edge map between L2R
         zhomNodeMapL2A = sazh0_nodeMap spanLeftToApplicaZhom   -- ^ sys archz node map bettwen L2A
         zhomEdgeMapL2A = sazh0_edgeMap spanLeftToApplicaZhom   -- ^ sys archz edge map between L2A
         morInBForEdgeInL = Set.foldr k coSpan leftArchEdgeSet  -- ^ for each edge inside leftArchEdgeSet
         k :: MF_MOR_NAME
                     -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
                     -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME  MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
         k edge coSpanForl@(POResultCospan b0 zHomR2B_0 zHomA2B_0) =  if length  (zhomEdgeMapL2R  Map.! edge) == 1 &&  length  (zhomEdgeMapL2A  Map.! edge) == 1  -- ^ simple match, i.e, edge to edge 
                       then let
                       (src,trg) = fst $ morNameMorMap Map.! edge  -- ^ get the source node and target node of a edge in L
                       (src_A, _morSrcL2A) =  zhomNodeMapL2A Map.! src -- ^ the image of the src node in A
                       (src_R, _morSrcL2R) = zhomNodeMapL2R Map.! src -- ^ the image of the src node in R
                       (trg_A, _morTrgL2A) = zhomNodeMapL2A Map.! trg -- ^ the image of the trg node in A
                       (trg_R,_morTrgL2R) = zhomNodeMapL2R Map.! trg  -- ^ the image of the trg node in R
                       edge_R = fst $ head $ zhomEdgeMapL2R Map.! edge  -- ^ the image of edge in R
                       edge_A = fst $ head $ zhomEdgeMapL2A Map.! edge  -- ^ the image of edge in A
                       mor_R = snd $ morNameMorMap Map.! edge_R   -- ^ the morphism for edge_R
                       mor_A = snd $ morNameMorMap Map.! edge_A   -- ^ the morphism for edge_A
                       ((src_B,_srcSignAndAxioms), (_morSrcR2BName, morSrcR2B))=  r2bZhomSpecMap Map.! src_R    -- ^  node name and node signatur + axioms in B, associated to node src_R, plus the zhom name and the zhom between src_R-> src_B 
                       ((trg_B,_trgSignAndAxioms), (_morTrgR2B, morTrgR2B)) = r2bZhomSpecMap Map.! trg_R        -- ^ node name and node signatur + axioms in B, associated to node trg_R, plus the zhom name and the zhom between trg_R -> trg_B
                       (_, (_morSrcA2BName, morSrcA2B)) = a2bZhomSpecMap Map.! src_A                   -- ^ the zhom name and the zhom between src_A-> src_B 
                       (_, (_morTrgA2BName,  morTrgA2B)) = a2bZhomSpecMap Map.! trg_A                  -- ^ the zhom name and the zhom between trg_A -> trg_B
                       theRightHalfMor = extractSingleSquareUniqueMorphism morSrcR2B mor_R morSrcR2B  -- ^ the inverse morphism(src zhom), the morphism in B and the trg zhom sequencially
                       theApplHalfMor = extractSingleSquareUniqueMorphism  morSrcA2B mor_A morTrgA2B  -- ^ the inverse morphism(src zhom), the morphism in A and the trg zhom sequencially
                       theUniversalMor = fromJust $ maybeResult (morphism_union MFLogic theRightHalfMor theApplHalfMor)    
                       theUnversalMorName = src_B ++ "2" ++ trg_B
                       b1 = b0 { sa_mors = Map.insert theUnversalMorName ((src_B,trg_B),theUniversalMor) $ sa_mors b0 }
                       zHomR2B_1 = zHomR2B_0 { sazh_edgeMap = Map.insert edge_R  [(theUnversalMorName, theUniversalMor, True)] $ sazh_edgeMap zHomR2B_0 }
                       zHomA2B_1 = zHomA2B_0 { sazh_edgeMap = Map.insert edge_A [(theUnversalMorName, theUniversalMor, True)] $ sazh_edgeMap zHomA2B_0 }
                       in POResultCospan b1 zHomR2B_1 zHomA2B_1
                       else if length  (zhomEdgeMapL2R  Map.! edge) /= 1 &&  length  (zhomEdgeMapL2A  Map.! edge) == 1
                          then let 
                             theImageZpath = zhomEdgeMapL2R Map.! edge  -- ^ the image (list of edges) of the edge in R
                             edgeAdjToTrg  = fst $ last theImageZpath   -- ^ the edge of the zpath in R, adjacent to target node
                             morInBforZpathmageInR = foldr eachEdge coSpanForl theImageZpath  -- ^ right architecture zpath matching edge_l -> zpath_r   
                             eachEdge item@(edge_r, _bool) coSpanForl@(POResultCospan b0 zHomR2B_0 zHomA2B_0) = if edge_r /= edgeAdjToTrg 
                                      then let
                                         ((src_r,trg_r), theMor_b) = morNameMorMap Map.! edge_r  -- ^ src and trg node name of edge_r
                                         ((src_b,_srcSignAndAxioms), (_morSrcR2BName, morSrcR2B))=  r2bZhomSpecMap Map.! src_r    -- ^  node name and node signatur + axioms in B, associated to node src_r, plus the zhom name and the zhom between src_r-> src_b 
                                         ((trg_b,_trgSignAndAxioms), (_morTrgR2B, morTrgR2B)) = r2bZhomSpecMap Map.! trg_r        -- ^ node name and node signatur + axioms in B, associated to node trg_r, plus the zhom name and the zhom between trg_r -> trg_b
                                         theMorName_b = src_b ++ trg_b     -- ^ the Name of the morphism in B
                                         edge_a = fst $ head $ zhomEdgeMapL2A Map.! edge  -- ^ the image of edge (an edge of L) in A
                                         currentZpathMaybe_b = Map.lookup edge_a $ sazh_edgeMap zHomA2B_0
                                         listZpat_b = case currentZpathMaybe_b of -- ^ keep adding/updating mor into a list
                                             Nothing -> [(theMorName_b, theMor_b, True)]
                                             Just list -> list ++ [(theMorName_b, theMor_b, True)]
                                         b1 = b0 { sa_mors = Map.insert theMorName_b ((src_b,trg_b),theMor_b) $ sa_mors b0 }
                                         zHomR2B_1 = zHomR2B_0 { sazh_edgeMap = Map.insert edge_r  [(theMorName_b, theMor_b, True)] $ sazh_edgeMap zHomR2B_0 }
                                         zHomA2B_1 = zHomA2B_0 { sazh_edgeMap = Map.insert edge_a listZpat_b $ sazh_edgeMap zHomA2B_0 }
                                         in POResultCospan b1 zHomR2B_1 zHomA2B_1
                                       else let  
                                         ((src_r,trg_r), theMor_r) = morNameMorMap Map.! edge_r  -- ^ src and trg node name of edge_r
                                         ((src_b,_srcSignAndAxioms), (_morSrcR2BName, morSrcR2B))=  r2bZhomSpecMap Map.! src_r    -- ^  node name and node signatur + axioms in B, associated to node src_r, plus the zhom name and the zhom between src_r-> src_b 
                                         ((trg_b,_trgSignAndAxioms), (_morTrgR2B, morTrgR2B)) = r2bZhomSpecMap Map.! trg_r        -- ^ node name and node signatur + axioms in B, associated to node trg_r, plus the zhom name and the zhom between trg_r -> trg_b
                                         theMor_b = fromJust $ maybeResult (composeMorphisms theMor_r morTrgR2B)  -- ^ new constructed morphism in B
                                         theMorName_b = src_b ++ trg_b     -- ^ the Name of the morphism in B
                                         edge_a = fst $ head $ zhomEdgeMapL2A Map.! edge  -- ^ the image of edge (an edge of L) in A
                                         currentZpathMaybe_b = Map.lookup edge_a $ sazh_edgeMap zHomA2B_0
                                         listZpat_b = case currentZpathMaybe_b of -- ^ keep adding/updating mor into a list
                                             Nothing -> [(theMorName_b, theMor_b, True)]
                                             Just list -> list ++ [(theMorName_b, theMor_b, True)]
                                         b1 = b0 { sa_mors = Map.insert theMorName_b ((src_b,trg_b),theMor_b) $ sa_mors b0 }
                                         zHomR2B_1 = zHomR2B_0 { sazh_edgeMap = Map.insert edge_r  [(theMorName_b, theMor_b, True)] $ sazh_edgeMap zHomR2B_0 }
                                         zHomA2B_1 = zHomA2B_0 { sazh_edgeMap = Map.insert edge_a listZpat_b $ sazh_edgeMap zHomA2B_0 }
                                         in POResultCospan b1 zHomR2B_1 zHomA2B_1
                              in morInBforZpathmageInR
                               else if length  (zhomEdgeMapL2R  Map.! edge) == 1 && length  (zhomEdgeMapL2A  Map.! edge) /= 1 -- copy of the above and with appropriate changes
                             then let 
                             theImageZpath = zhomEdgeMapL2A Map.! edge  -- ^ the image (list of edges) of the edge in A
                             edgeAdjToTrg  = fst $ last theImageZpath   -- ^ the edge of the zpath in A, adjacent to target node
                             morInBforZpathmageInA = foldr eachEdge coSpanForl theImageZpath  -- ^ right architecture zpath matching edge_l -> zpath_a  
                             eachEdge item@(edge_a, _bool) coSpanForl@(POResultCospan b0 zHomR2B_0 zHomA2B_0) = if edge_a /= edgeAdjToTrg 
                                      then let
                                         ((src_a,trg_a), theMor_b) = morNameMorMap Map.! edge_a  -- ^ src and trg node name of edge_a
                                         ((src_b,_srcSignAndAxioms), (_morSrcA2BName, morSrcA2B))=  a2bZhomSpecMap Map.! src_a    -- ^  node name and node signatur + axioms in B, associated to node src_a, plus the zhom name and the zhom between src_a-> src_b 
                                         ((trg_b,_trgSignAndAxioms), (_morTrgA2B, morTrgA2B)) = a2bZhomSpecMap Map.! trg_a        -- ^ node name and node signatur + axioms in B, associated to node trg_a, plus the zhom name and the zhom between trg_a -> trg_b
                                         theMorName_b = src_b ++ trg_b     -- ^ the Name of the morphism in B
                                         edge_r = fst $ head $ zhomEdgeMapL2R Map.! edge  -- ^ the image of edge (an edge of L) in R
                                         currentZpathMaybe_b = Map.lookup edge_r $ sazh_edgeMap zHomR2B_0
                                         listZpat_b = case currentZpathMaybe_b of -- ^ keep adding/updating mor into a list
                                             Nothing -> [(theMorName_b, theMor_b, True)]
                                             Just list -> list ++ [(theMorName_b, theMor_b, True)]
                                         b1 = b0 { sa_mors = Map.insert theMorName_b ((src_b,trg_b),theMor_b) $ sa_mors b0 }
                                         zHomR2B_1 = zHomR2B_0 { sazh_edgeMap = Map.insert edge_r listZpat_b $ sazh_edgeMap zHomR2B_0 } 
                                         zHomA2B_1 = zHomA2B_0 { sazh_edgeMap = Map.insert edge_a  [(theMorName_b, theMor_b, True)] $ sazh_edgeMap zHomA2B_0 } 
                                         in POResultCospan b1 zHomR2B_1 zHomA2B_1
                                      else let  
                                         ((src_a,trg_a), theMor_a) = morNameMorMap Map.! edge_a  -- ^ src and trg node name of edge_a
                                         ((src_b,_srcSignAndAxioms), (_morSrcA2BName, morSrcA2B))=  a2bZhomSpecMap Map.! src_a    -- ^  node name and node signatur + axioms in B, associated to node src_a, plus the zhom name and the zhom between src_a-> src_b 
                                         ((trg_b,_trgSignAndAxioms), (_morTrgA2B, morTrgA2B)) = a2bZhomSpecMap Map.! trg_a        -- ^ node name and node signatur + axioms in B, associated to node trg_a, plus the zhom name and the zhom between trg_a -> trg_b
                                         theMor_b = fromJust $ maybeResult $ composeMorphisms theMor_a morTrgA2B  -- ^ new constructed morphism in B
                                         theMorName_b = src_b ++ trg_b     -- ^ the Name of the morphism in B
                                         edge_r = fst $ head $ zhomEdgeMapL2R Map.! edge  -- ^ the image of edge (an edge of L) in R
                                         currentZpathMaybe_b = Map.lookup edge_r $ sazh_edgeMap zHomR2B_0
                                         listZpat_b = case currentZpathMaybe_b of -- ^ keep adding/updating mor into a list
                                             Nothing -> [(theMorName_b, theMor_b, True)]
                                             Just list -> list ++ [(theMorName_b, theMor_b, True)]
                                         b1 = b0 { sa_mors = Map.insert theMorName_b ((src_b,trg_b),theMor_b) $ sa_mors b0 }
                                         zHomR2B_1 = zHomR2B_0 { sazh_edgeMap = Map.insert edge_r listZpat_b $ sazh_edgeMap zHomR2B_0 }  
                                         zHomA2B_1 = zHomA2B_0 { sazh_edgeMap = Map.insert edge_a  [(theMorName_b, theMor_b, True)] $ sazh_edgeMap zHomA2B_0 }  
                                         in POResultCospan b1 zHomR2B_1 zHomA2B_1
                                   in morInBforZpathmageInA
                              else error "Alright, Do Some Work and Make a Decision"
      
         morInBForEdgesInLR = Set.foldr r morInBForEdgeInL rightArchEdgeSet  -- for each edge inside leftArchEdgeSet
         r edge_r rl@(POResultCospan b0 zHomR2B_0 zHomA2B_0) 
              | hasEdgePreImage zhomEdgeMapL2R leftArchEdgeSet edge_r == False = trace ("morInBForEdgesInLR:" ++ show edge_r ) $ let 
                                            ((src_r, trg_r), theMor_b) = morNameMorMap Map.! edge_r  -- ^ src and trg node name of edge_r
                                            ((src_b,_srcSignAndAxioms), (_morSrcR2BName, morSrcR2B))=  r2bZhomSpecMap Map.! src_r    -- ^  node name and node signatur + axioms in B, associated to node src_r, plus the zhom name and the zhom between src_r-> src_b 
                                            ((trg_b,_trgSignAndAxioms), (_morTrgR2B, morTrgR2B)) = r2bZhomSpecMap Map.! trg_r        -- ^ node name and node signatur + axioms in B, associated to node trg_r, plus the zhom name and the zhom between trg_r -> trg_b
                                            theMorName_b = src_b ++ trg_b     -- ^ the Name of the morphism in B
                                            b1 = b0 { sa_mors = Map.insert theMorName_b ((src_b,trg_b),theMor_b) $ sa_mors b0 }
                                            zHomR2B_1 = zHomR2B_0 { sazh_edgeMap = Map.insert edge_r  [(theMorName_b, theMor_b, True)] $ sazh_edgeMap zHomR2B_0 }
                                            zHomA2B_1 = zHomA2B_0
                                            in POResultCospan b1 zHomR2B_1 zHomA2B_1
              | otherwise = rl
       
         morInBForEdgesInLRA = Set.foldr a morInBForEdgesInLR applArchEdgeSet  -- for each edge inside leftArchEdgeSet
         a edge_a rla@(POResultCospan b0 zHomR2B_0 zHomA2B_0) 
                                 |  hasEdgePreImage zhomEdgeMapL2A leftArchEdgeSet edge_a == False = let 
                                            ((src_a,trg_a), theMor_b) = morNameMorMap Map.! edge_a  -- ^ src and trg node name of edge_a
                                            ((src_b,_srcSignAndAxioms), (_morSrcA2BName, morSrcA2B))=  a2bZhomSpecMap Map.! src_a    -- ^  node name and node signatur + axioms in B, associated to node src_a, plus the zhom name and the zhom between src_a-> src_b 
                                            ((trg_b,_trgSignAndAxioms), (_morTrgA2B, morTrgA2B)) = a2bZhomSpecMap Map.! trg_a        -- ^ node name and node signatur + axioms in B, associated to node trg_a, plus the zhom name and the zhom between trg_a -> trg_b
                                            theMorName_b = src_b ++ trg_b     -- ^ the Name of the morphism in B
                                            b1 = b0 { sa_mors = Map.insert theMorName_b ((src_b,trg_b), theMor_b) $ sa_mors b0 }
                                            zHomR2B_1 = zHomR2B_0 
                                            zHomA2B_1 = zHomA2B_0 { sazh_edgeMap = Map.insert edge_a  [(theMorName_b, theMor_b, True)] $ sazh_edgeMap zHomA2B_0 }
                                            in POResultCospan b1 zHomR2B_1 zHomA2B_1
                                 | otherwise = rla                              
         in morInBForEdgesInLRA


computeNodeSpecZhomAtResultArch :: MF_SYSARCH_DIAGRAM 
      -> Span (MF_DIAGNODE_NAME, SysArch) ((MF_DIAGNODE_NAME, MF_DIAGNODE_NAME), SysArchZPHom0)
      -> MF_DIAGNODE_NAME -- ^ ``B''
      -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF))
                        (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))

computeNodeSpecZhomAtResultArch archDiag@(MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = nodeNameSpecMap     -- ^ all specifications name to specificaiton map 
        , mfsaDiag_allMors   = morNameMorMap       -- ^ all morphisms name to morphism map
        , mfsaDiag_nodes     = diagNameArchMap     -- ^ all architecture, node and edge sets 
        , mfsaDiag_edges     = diagNodesZHom       -- ^ sysarchZhom0, i.e., node and edge map  L-->A, L--->R
        }) span@(Span
         { spanL = (leftDiag,leftArch)
         , spanR = (rightDiag,rightArch)
         , spanA = (applDiag,applArch)
         , spanLtoR = ((_leftDiag, _rightDiag), spanLeftToRightZhom)
         , spanLtoA = ((_leftDiag', _applDiag), spanLeftToApplZhom)
         }) resArch  = let
         leftArchNodeSet = sa_nodes leftArch       -- ^ left Arch node name set
         leftArchEdgeSet = sa_edges leftArch       -- ^ left Arch edge name set
         zhomNodeMapL2R = sazh0_nodeMap spanLeftToRightZhom     -- ^ sys archz node map bettwen L2R
         zhomEdgeMapL2R = sazh0_edgeMap  spanLeftToRightZhom    -- ^ sys archz edge map between L2R
         zhomNodeMapL2A = sazh0_nodeMap spanLeftToApplZhom   -- ^ sys archz node map bettwen L2A
         zhomEdgeMapL2A = sazh0_edgeMap spanLeftToApplZhom   -- ^ sys archz edge map between L2A
         pushoutForLeftObjects :: POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
         pushoutForLeftObjects = Set.foldr addLocalPushout (POResultCospan (SysArchReal Map.empty Map.empty) emptySysArchZPHom emptySysArchZPHom) leftArchNodeSet
    
         addLocalPushout :: MF_SPEC_NAME
                            -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
                            -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
         addLocalPushout lNode rCospanSoFar@(POResultCospan b0 zHomR2B_0 zHomA2B_0) = let
             (rNode, l2rEdge) = zhomNodeMapL2R Map.! lNode   -- a + b
             (aNode, l2aEdge) = zhomNodeMapL2A Map.! lNode
             theSpecSpan = span { spanL = lNode , spanR = rNode , spanA = aNode
                                 ,spanLtoR = l2rEdge , spanLtoA = l2aEdge}
             thePushout@(POResultCospan thePOSpecification mfmorR2B mfmorA2B) = spec_pushout archDiag theSpecSpan   -- the signature axiom pair, two morphisms
             
             thePOSpecName = lNode ++ "_" ++ resArch
             
             zHomR2BName = rNode ++ "2" ++ resArch
             zHomA2BName = aNode ++ "2" ++ resArch
             b1 = b0 { sa_specs = Map.insert thePOSpecName thePOSpecification $ sa_specs b0 }
             zHomR2B_1 = zHomR2B_0 { sazh_nodeMap = Map.insert rNode ((thePOSpecName, thePOSpecification), (zHomR2BName, mfmorR2B)) $ sazh_nodeMap zHomR2B_0 }
             zHomA2B_1 = zHomA2B_0 { sazh_nodeMap = Map.insert aNode ((thePOSpecName, thePOSpecification), (zHomA2BName, mfmorA2B)) $ sazh_nodeMap zHomA2B_0 }
             in POResultCospan b1 zHomR2B_1 zHomA2B_1

         rightArchNodeSet = sa_nodes rightArch       -- ^ right Arch node name set
         newObjAndZhomforRightObjectsOnly = Set.foldr theNewObjZhomForR pushoutForLeftObjects rightArchNodeSet
         theNewObjZhomForR :: MF_SPEC_NAME
                            -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
                            -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
         theNewObjZhomForR rNode  lCospanSoFar@(POResultCospan b0 zHomR2B_0 zHomA2B_0)
              | hasPreImage zhomNodeMapL2R rNode == False = let
                           thePOSpecificationOnlyR :: MF_BASIC_SPEC
                           thePOSpecificationOnlyR =  sanl_BasicSpec $ nodeNameSpecMap Map.!rNode        -- ^ the basic specification , need to convert it to Sign + Axioms
                           thePOSignatureOnlyR :: ExtSignMF
                           thePOSignatureOnlyR = sanl_ExtSig  $ nodeNameSpecMap Map.!rNode   -- ^ the signature part of the basic spec
                           thePOAxiomsOnlyR = concat $ getAxiomsFromBasicSpec' thePOSpecificationOnlyR  -- ^ discarding outer annotations:
                           thePOSignatureOnlyR' :: MFSign   -- ^ type MFSign = Sign MF_FORMULA SignExtMF
                           thePOSignatureOnlyR' = plainSign thePOSignatureOnlyR 
                           thePOSpecNameOnlyR =  rNode ++ "_"  ++ resArch              -- ^ the new specificaiton name in B
                           -- idMor :: m -> Sign f e -> Morphism f e m
                           idMorR2BOnlyR = idMor (identityMFMap $ extendedInfo thePOSignatureOnlyR') thePOSignatureOnlyR'      -- ^ the Zhom, it is an idendity 
                           idMorR2BNameOnlyR = rNode ++ "R2" ++ resArch                 -- ^ the Zhom name
                           b1 = b0 { sa_specs = Map.insert thePOSpecNameOnlyR (thePOSignatureOnlyR', thePOAxiomsOnlyR) $ sa_specs b0 }
                           zHomR2B_1 = zHomR2B_0 { sazh_nodeMap = Map.insert rNode ((thePOSpecNameOnlyR, (thePOSignatureOnlyR', thePOAxiomsOnlyR)), (idMorR2BNameOnlyR, idMorR2BOnlyR)) $ sazh_nodeMap zHomR2B_0 }
                           zHomA2B_1 = zHomA2B_0 
                           in POResultCospan b1 zHomR2B_1 zHomA2B_1
             | otherwise = lCospanSoFar 

         applArchNodeSet = sa_nodes applArch       -- ^ application Arch node name set
         newObjAndZhomforApplPlusObjectsOnly = Set.foldr theNewObjZhomForR newObjAndZhomforRightObjectsOnly applArchNodeSet
         theNewObjZhomForA ::  MF_SPEC_NAME
                            -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
                            -> POResultCospan (SysArchReal (Map MF_SPEC_NAME (MFSign, ([Annoted (FORMULA MF_FORMULA)]))) (Map MF_MOR_NAME MorphismMF)) (SysArchZPHom (MFSign, ([Annoted (FORMULA MF_FORMULA)])))
         theNewObjZhomForA aNode  lrCospanSoFar@(POResultCospan b0 zHomR2B_0 zHomA2B_0)
              | hasPreImage zhomNodeMapL2A aNode == False = let
                           thePOSpecificationOnlyA :: MF_BASIC_SPEC
                           thePOSpecificationOnlyA =  sanl_BasicSpec $ nodeNameSpecMap Map.!aNode        -- ^ the basic specification
                           thePOSignatureOnlyA :: ExtSignMF
                           thePOSignatureOnlyA = sanl_ExtSig  $ nodeNameSpecMap Map.!aNode               -- ^ the signature part of the basic spec
                           thePOAxiomsOnlyA = concat $ getAxiomsFromBasicSpec' thePOSpecificationOnlyA  -- ^ discarding outer annotations:
                           thePOSpecNameOnlyA =  aNode ++ "_" ++ resArch          -- ^ the new specificaiton name in B
                           thePOSignatureOnlyA' :: MFSign   -- ^ type MFSign = Sign MF_FORMULA SignExtMF
                           thePOSignatureOnlyA' = plainSign thePOSignatureOnlyA
                           -- idMor :: m -> Sign f e -> Morphism f e m
                           idMorA2BOnlyA = idMor (identityMFMap $ extendedInfo thePOSignatureOnlyA') thePOSignatureOnlyA'  -- ^ the  Zhom, it is an idendity 
                           idMorA2BNameOnlyA = aNode ++ "A2" ++ resArch            -- ^ the Zhom name
                           b1 = b0 { sa_specs = Map.insert thePOSpecNameOnlyA (thePOSignatureOnlyA', thePOAxiomsOnlyA) $ sa_specs b0 }
                           zHomR2B_1 = zHomR2B_0
                           zHomA2B_1 = zHomA2B_0  { sazh_nodeMap = Map.insert aNode ((thePOSpecNameOnlyA, (thePOSignatureOnlyA', thePOAxiomsOnlyA)), (idMorA2BNameOnlyA, idMorA2BOnlyA)) $ sazh_nodeMap zHomR2B_0 }
                           in POResultCospan b1 zHomR2B_1 zHomA2B_1
             | otherwise = lrCospanSoFar
  
  in newObjAndZhomforApplPlusObjectsOnly



{-| This function is designed to get the pushout morphism (unique morphism)
for a single square. 
type MorphismMF = Morphism MF_FORMULA SignExtMF MFMap 
is defined in MFLogic/Logic_MFLogic.hs
implemented bad way, if inverse or composition goes wrong we are not throwing any diags:: [Diagnosis]
-}

extractSingleSquareUniqueMorphism ::  MorphismMF -> MorphismMF -> MorphismMF -> MorphismMF
extractSingleSquareUniqueMorphism inv mor1 mor2 = fromJust $ maybeResult (composeMorphisms (fromJust $ maybeResult (composeMorphisms (fromJust $ maybeResult (inverse inv)) mor1)) mor2)

{-|
For a given span (Node Name(S_A) <----Node Name(S_L) -----> Node Name(S_R)) and 
a system architecture diagram,
this function calculate the cospan (------>Node Signature <-------)       
type Node = Int
type LNode a = (Node, a)
Graph.mkGraph :: [LNode a] -> [LEdge b] -> Gr a b
Gr sign (Int, morphism)
signature_pushout  (Span S_A <-- S_L --> S_R)
-}

signature_pushout :: MF_SYSARCH_DIAGRAM -> MFSpecSpan -> POResultCospan MFSign MorphismMF  -- Using Logic.signature_colimit
signature_pushout (MF_SYSARCH_DIAGRAM
        { mfsaDiag_allSpecs  = nodeNameSpecMap
        , mfsaDiag_allMors   = morNameMorMap
        , mfsaDiag_nodes     = diagNameArchMap
        , mfsaDiag_edges     = diagNodesZHom
        }) (Span
       { spanL = leftNode
       , spanR = rightNode
       , spanA = appliNode
       , spanLtoR = morNameLeftNodeToRight
       , spanLtoA = morNameLeftNodeToAppli
  }) = let
  leftNodeSign = plainSign . sanl_ExtSig $ nodeNameSpecMap Map.! leftNode   -- ^ signature of the left Node
  rightNodeSign = plainSign . sanl_ExtSig $ nodeNameSpecMap Map.! rightNode -- ^ signature of the right Node
  appliNodeSign = plainSign . sanl_ExtSig $ nodeNameSpecMap Map.! appliNode -- ^ signature of the application Node
  morLtoRNode = snd $ morNameMorMap Map.! morNameLeftNodeToRight -- ^ morphism between left Node to right Node
  morLtoANode = snd $ morNameMorMap Map.! morNameLeftNodeToAppli -- ^ morphism between left Node to application Node
  nodeList = [(0,leftNodeSign),(1,rightNodeSign),(2,appliNodeSign)] 
  morphisList = [(0,1,(3,morLtoRNode)),(0,2,(4,morLtoANode))]
  diag :: Gr MFSign (Int, MorphismMF)
  diag = Graph.mkGraph nodeList morphisList
  res = signature_colimit MFLogic diag
  in case res of
    Result _ (Just (sign, intToMorMap)) -> POResultCospan
                { porcObj    = sign
                , porcR2B   = intToMorMap Map.! 1
                , porcA2B  = intToMorMap Map.! 2
                }
    Result diagnoses Nothing      -> error $ "signature_pushout: signature_colimit failed: " ++ show diagnoses

{-|
A basic specification has both signatue and axioms.
This function get all the axioms from a specification.
-}

getAxiomsFromBasicSpec :: MF_BASIC_SPEC -> [Annoted ([Annoted (FORMULA MF_FORMULA)], Range)]
getAxiomsFromBasicSpec (CASL.AS_Basic_CASL.Basic_spec aitems) = mapMaybe h aitems
  where
    h a@(Annoted {item = Axiom_items axs rng}) = Just $ a { item = (axs, rng) }
    h _ = Nothing

-- ^ discarding outer annotations:
getAxiomsFromBasicSpec' :: MF_BASIC_SPEC -> [[Annoted (FORMULA MF_FORMULA)]]
getAxiomsFromBasicSpec' = map (fst . item) . getAxiomsFromBasicSpec

{-|
For a givn system architecture diagram and a spac span (S_A<-------S_L--------->S_R), 
where S_A,S_L,S_R are specification names (node names) and two arrows are morphism names.
This function returns the cospan (-------> Node Specificaitoin <------).
The Node specification contains a pair of the signature along with the  translated axioms and 
the two morphisms are the mrophsimMF.

-}


spec_pushout :: MF_SYSARCH_DIAGRAM -> MFSpecSpan
           -> POResultCospan (MFSign, ([Annoted (FORMULA MF_FORMULA)])) MorphismMF -- also translate axioms
spec_pushout archDiag specSpan = let
            sigPushout = signature_pushout archDiag specSpan -- ^ Record of a MFSign and two MorphismMF
            -- cospan signature and morphisms
            coSpanSign = porcObj sigPushout                  -- ^ The Signature of the cospan 
            coSpanLeft = porcR2B sigPushout                 -- ^ The left morphism of the cospan
            coSpanRight = porcA2B sigPushout               -- ^ the right morphism of the cospan
            -- span node names and morphism names
            leftNode = spanL specSpan                        -- ^ The left node name of the span
            rightNode = spanR specSpan                       -- ^ The right node name of the span
            appliNode = spanA specSpan                       -- ^ The application node name of the span
            morNameLeftNodeToRight = spanLtoR specSpan       -- ^ The morphism name from node left to right
            morNameLeftNodeToAppli = spanLtoA specSpan       -- ^ The morphism name from ndoe left to application
            -- extract all specs and from system architecture
            nodeNameSpecMap = mfsaDiag_allSpecs archDiag
            -- extract the morphisms from the right and application node specification
            rightNodeAxioms = getAxiomsFromBasicSpec' (sanl_BasicSpec $ nodeNameSpecMap Map.! rightNode)
            appliNodeAxioms = getAxiomsFromBasicSpec' (sanl_BasicSpec $ nodeNameSpecMap Map.! appliNode)
            -- the translated axioms
            r = do
              -- discarding outer annotations...
              rightTransAxioms <- mapM (mapAnM (map_sen MFLogic coSpanLeft)) rightNodeAxioms
              appliTransAxioms <- mapM (mapAnM (map_sen MFLogic coSpanRight)) appliNodeAxioms
              return $ POResultCospan
                  { porcObj    = (coSpanSign, concat $ rightTransAxioms ++ appliTransAxioms)
                  , porcR2B   = coSpanLeft
                  , porcA2B  = coSpanRight
                  }
          in case r of
            Result _ (Just cospan) -> cospan
            Result diagnoses _ -> error $ "spec_pushout: " ++ show diagnoses

{-|
Extract the set of specification/node names of an architecture and
for all of the architectures of a |DGraph| 
-}

extractSysArchDiagramNodesFromLibEnv :: DGraph -> Map MF_DIAGNODE_NAME (Set MF_SPEC_NAME) 
extractSysArchDiagramNodesFromLibEnv dgraph = trace "========= extractSysArchDiagramNodesFromLibEnv =========" $
  let
    Just (specDfn@(Lib_defn _ aItems _ _)) = optLibDefn dgraph
    nodes = foldr h Map.empty aItems
    h (Annoted (Arch_spec_defn archSpName (Annoted (Basic_arch_spec unitDeclDef _ _) _ _ _) r) _ _ _)
      = let  archName = drop 1 $ abbrevQuery archSpName
             archSpecNames = foldr c Set.empty unitDeclDef
             c (Annoted (Unit_decl _ (Unit_spec (Spec_name cName)) _ _) _ _ _)
                 = trace ("\nextractSysArchDiagramNodesFromLibEnv: cName: iriPath = " ++ iriPath cName ++ "; iriQuery = " ++ iriQuery cName ++
              "; prefixName = " ++ prefixName cName ++ "; abbrevPath = " ++ abbrevPath cName ++
              "; abbrevQuery = " ++  abbrevQuery cName) $
                   Set.insert $ abbrevPath cName
             c _ = id
      in Map.insert archName archSpecNames
    h _ = id
 in  nodes

{-|
Find the set of edge names of a specific architecture.
One of the argument is the set of node names of the architecture
-}
findLocalMorphisms :: Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
  -> Set MF_SPEC_NAME -> SysArch 
findLocalMorphisms edgeMap localSpecNames =
                 let edges = Map.foldrWithKey m Set.empty edgeMap
                     m :: MF_MOR_NAME
                           -> ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF) -> Set MF_MOR_NAME -> Set MF_MOR_NAME

                     m mName ((mS, mT), mor)
                       | Set.member mS localSpecNames && Set.member mT localSpecNames
                       = Set.insert mName
                       | otherwise = id

                 in  SysArch 
                    { sa_nodes = localSpecNames
                    , sa_edges = edges
                      }

-- for given a  map of architecture name to set of architecture node names and
-- a map of morphism name to ((source node name, target node name), morphism)  it returns 
-- a map from architecture name to systemarchitecture (node name set and edge name set).
{-|
Add set of morphism names with the set of node names
of an architecture, and it is done for all of the architectures 
of a |Dgraph|. 

Arguments: 
a) A map of architecture name to set of architecture node names
b) A map of morphism name to ((source node name, target node name), morphism)

Returns: 
a map from architecture name to systemarchitecture (node name set and edge name set).
-}
addMorphismsToSysArch ::  Map MF_DIAGNODE_NAME (Set MF_SPEC_NAME) 
  ->  Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
  -> Map MF_DIAGNODE_NAME SysArch 
addMorphismsToSysArch archMap edgeMap =
  Map.map (findLocalMorphisms edgeMap) archMap

{-| For given different system architectures info,
it returns the System architecture Zhomomorphism (both edge map and node map)
between the architectures.
 -}
extractSysArchZHom ::  Map MF_DIAGNODE_NAME SysArch -- (Set MF_SPEC_NAME) 
  -> Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
  -> Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) SysArchZPHom0 
extractSysArchZHom archMap edgeMap = let
    nodesMap :: Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME))
    nodesMap = Map.foldrWithKey m' Map.empty edgeMap
      where
        m, m'  :: MF_MOR_NAME
           -> ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
           -> Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME))
           -> Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME))
        m' mName ((mS, mT), mor) r = trace (unwords ["extractSysArchZHom.m:", show mS, show mT]) $ m mName ((mS, mT), mor) r
        m mName ((mS, mT), mor) r
           | Just anS <- lookupInArchs archMap mS
           , Just anT <- lookupInArchs archMap mT
           , anS /= anT
           = let nm0, nm1 :: Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME)
                 nm0 = Map.findWithDefault Map.empty (anS, anT) r
                 nm1 = Map.insert mS (mT, mName) nm0
             in Map.insert (anS, anT) nm1 r
           | otherwise = r

    edgesMap :: Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_MOR_NAME [(MF_MOR_NAME, Bool)])
    edgesMap = Map.foldrWithKey n Map.empty nodesMap
      where
      n  :: (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME)
         -> Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME)
         -> Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_MOR_NAME [(MF_MOR_NAME, Bool)])
         -> Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_MOR_NAME [(MF_MOR_NAME, Bool)])
      n (sdName, tdName) specNameMorName localMap = let               
          localEdges :: Set MF_MOR_NAME
          localEdges = case Map.lookup sdName  archMap of   -- ^ get the edges in L 
                            Just arch -> sa_edges arch
                            _   -> Set.empty

          -- ^ this function find the other source diagnode (architecture, i.e., P0,) name
          otherDiagNode ::  MF_SPEC_NAME -> MF_SPEC_NAME -> Maybe MF_DIAGNODE_NAME   
          otherDiagNode sN tN =  Map.foldrWithKey d Nothing nodesMap
            where
            d :: (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME)
              -> Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME)
              -> Maybe MF_DIAGNODE_NAME 
              -> Maybe MF_DIAGNODE_NAME 
            d (sdName2, tdName2) specNameMorName2 no
                 |  tdName2 ==  tdName
                 , sdName2 /= sdName
                 , hasPreImage specNameMorName2 sN
                 , hasPreImage specNameMorName2 tN =  Just sdName2
                 | otherwise = no   
          morNameMap = Set.foldr k Map.empty localEdges -- ^ For each edge in L create the map of zhom st2sL---> st2sA, true 
          k edge = let 
               (preImageSrcNode, preImageTrgNode) = case Map.lookup edge edgeMap of  -- source and target node for e in L
                                                         Just ((s,t),m) -> (s,t)
                                                         _              -> error "Error preImageSrcNode "
                
               imageSrcNode = case Map.lookup preImageSrcNode specNameMorName of  -- ^ source node image in A/R
                 Just (n,m) -> n
                 _          -> error "Error  imageSrcNode" -- ^ IMPOSSIBLE
               imageTrgNode = case Map.lookup preImageTrgNode specNameMorName of   -- ^ target node image in A/R
                                   Just (n,m) -> n
                                   _          -> error "Error  imageTrgNode" -- ^ IMPOSSIBLE               
               theZpath = Map.foldrWithKey v Nothing edgeMap  -- ^ image of the edge  
               v zPath (sNtN@(_sN,_tN),mor) p
                       | sNtN == (imageSrcNode, imageTrgNode)
                        = Just zPath  
                       | otherwise = p
            in case theZpath of
              Nothing -> case otherDiagNode imageSrcNode imageTrgNode of
                             Just othDN ->  Map.insert edge $ findComplex imageSrcNode imageTrgNode othDN tdName nodesMap archMap edgeMap
                             Nothing    -> id
              Just singleEdge -> Map.insert edge [(singleEdge, True)] 
                     
        in Map.insert (sdName, tdName) morNameMap localMap

    wrap :: (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) -> (Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME)) -> SysArchZPHom0
    wrap p@(_aS, _aT) nm = SysArchZPHom0  { sazh0_nodeMap = nm
                                          , sazh0_edgeMap = Map.findWithDefault Map.empty p edgesMap
                                          }     
  in Map.mapWithKey wrap nodesMap

{-|
Finds the complex zhom edge mapping, i.e., a mapping between signle edge to 
zigzag path (undirected path of path length more than 1),e.g., [(e1,True),(e2,True,)]
-}
findComplex :: MF_SPEC_NAME -> MF_SPEC_NAME 
     -> MF_DIAGNODE_NAME -> MF_DIAGNODE_NAME 
     -> Map (MF_DIAGNODE_NAME,MF_DIAGNODE_NAME) (Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME))
     -> Map MF_DIAGNODE_NAME SysArch 
     -> Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)  
     -> {- Maybe -} [(MF_MOR_NAME,Bool)]
findComplex srcN trgN otrArch trgArch  nodesMap archMap morMap =
   trace("========= findComplex =========" ++ srcN ++ "====" ++ trgN ++ shows otrArch  "========="++ shows (pretty nodesMap) "=========" )
   $ let
      localNodeMap :: Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME)
      localNodeMap = fromJust $  Map.lookup (otrArch, trgArch) nodesMap
      localNodeSet :: Set MF_SPEC_NAME   
      localNodeSet =  sa_nodes $ fromJust $ Map.lookup otrArch archMap
      localMorSet :: Set MF_MOR_NAME 
      localMorSet = sa_edges $ fromJust $ Map.lookup trgArch archMap
      preImage = fromJust $ Map.foldrWithKey f Nothing localNodeMap  -- always retun Just sN
        where
          f sN (tN,mN) p
            | tN == srcN = Just sN
            | otherwise  = p
      -- |buildEdgeList| precondition: |srcN| is |nodesMap (otrArch, trgArch)| image of |preImage|
      -- and |theList| is a path from |findComplex.srcN| to |srcN|
      buildEdgeList :: Set MF_SPEC_NAME -> MF_SPEC_NAME -> MF_SPEC_NAME -> [(MF_MOR_NAME,Bool)] -> [(MF_MOR_NAME,Bool)]
      buildEdgeList temNodeSet preImage srcN theList = trace ("========= buildEdgeList ======srcN===" ++ srcN ++ "==preImage==" ++ preImage ++ "==temNodeSet==" ++ show temNodeSet++ "==theList==" ++ show theList) $ let
          (new, temNodeSet') = findAdjaceNodePlus preImage morMap temNodeSet localNodeSet
          imageOfAdjNode = lookupImages new localNodeMap
          theEdge = findEdge imageOfAdjNode srcN morMap
          -- theList' = theList ++ [(theEdge,True)]
        in if  isTarget localMorSet imageOfAdjNode morMap &&  imageOfAdjNode /= trgN
            then let theList' = theList ++ [(theEdge,True)]
                 in buildEdgeList temNodeSet' new imageOfAdjNode theList'
            else if isSource localMorSet imageOfAdjNode morMap 
            then let theList' = theList ++ [(theEdge,False)]
                 in buildEdgeList temNodeSet' new imageOfAdjNode theList'
            else theList ++ [(theEdge, isTarget localMorSet imageOfAdjNode morMap && imageOfAdjNode == trgN)]
    in buildEdgeList (Set.singleton preImage) preImage srcN []



{-|
Checks whether a |nodeName| has preimages in the SysArchZhom0 |nodeMap|
-}
hasPreImage :: Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME)-> MF_SPEC_NAME -> Bool
hasPreImage localNodeMap nodeName =  Map.foldrWithKey f False localNodeMap 
        where
          f sN (tN,mN) p
            | tN == nodeName = True
            | otherwise  = p
            

{-|
Checks whether a |morName/edge| has a preimage in SysArchsZhom0 |edgeMap|
-}
hasEdgePreImage :: Map MF_MOR_NAME [(MF_MOR_NAME, Bool)] -> Set MF_MOR_NAME
                   -> MF_MOR_NAME -> Bool
hasEdgePreImage edgeMapBtnTwoArch srsArchMorSet morName = let
           concatList  = foldr f [] srsArchMorSet
           f morN ebl = trace ("mor  name:" ++ show morN ++ "mor  name:" ++ show morName) $ let
              llist   = edgeMapBtnTwoArch Map.! morN
              in ebl ++ llist
           exists = trace ("concat list:" ++ show concatList ) $ foldr n False concatList
           n (nm, _b) p
              | nm == morName = True
              | otherwise = p
           in exists

{-|
Find the adjacency node name of a given node 
That has not been visited yet. 
-}
findAdjaceNodePlus :: MF_SPEC_NAME
                -> Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
                -> Set MF_SPEC_NAME -> Set MF_SPEC_NAME
                    -> (MF_SPEC_NAME, Set MF_SPEC_NAME )
findAdjaceNodePlus preImage morMap temNodeSet localNodeSet =trace("========= findAdjaceNodePlus =========" ++ preImage ) $ let 
      adjNode = Map.foldrWithKey adj Nothing morMap
      adj morName ((sN,tN),mor) p
        | sN == preImage 
        , Set.notMember tN temNodeSet
        , Set.member tN localNodeSet = Just tN -- |True| means ``forward''
        | tN == preImage
        , Set.notMember sN temNodeSet
        , Set.member sN localNodeSet = Just sN
        | otherwise  = p
    in case adjNode of
       Just n -> (n, Set.insert n temNodeSet)
       Nothing -> error "findAdjaceNode went wrong" --POSSIBLE But the caller is making sure there is an adjacence Node


{-|
For given two nodes and a |edgeMap| this function finds the edge
-}
findEdge :: MF_SPEC_NAME -> MF_SPEC_NAME
    -> Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
    -> MF_MOR_NAME
findEdge n1 n2 edgeM = let
           morName =  Map.foldrWithKey hf  Nothing  edgeM
           hf morN ((sN,tN),mor) p
               | n1 == sN
               , n2 == tN  = Just morN
               | n1 == tN
               , n2 == sN  = Just morN
               | otherwise = p
           in case morName of
             Just mN -> mN
             Nothing  -> error "findEdge"   --IMPOSSIBLE  
{-|
For given a |nodeName| and a |nodeMap| between two architectures
this function finds the image |nodeName| 
-}

lookupImages :: MF_SPEC_NAME -> Map MF_SPEC_NAME (MF_SPEC_NAME, MF_MOR_NAME) -> MF_SPEC_NAME
lookupImages givenSpecName specNameMap = trace("========= lookupImages =========" ++ givenSpecName ) $ let
           theSpecNameMaybe = Map.lookup givenSpecName specNameMap
           in case theSpecNameMaybe of
             Just (theSpecName,mor) -> theSpecName
             Nothing          -> error "lookupImages"  -- IMPOSSIBLE
{-|
Checks whether a given |specName| (node Name) is a target (component) or not.
Takes a node name and all morphisms as arguments and
returns Bool
-}

isTarget :: Set MF_MOR_NAME -> MF_SPEC_NAME ->  Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF) -> Bool -- Maybe MF_MOR_NAME
isTarget localMorSet specName morMap = Map.foldrWithKey v False morMap
           where  
               v morName ((sN,tN),mor) p
                       | Set.member morName localMorSet
                       , specName == tN = True
                       | otherwise       = p

-- checks whether a given spec_name (node Name) is a source(part of a connector) or not
{-|

-}
isSource :: Set MF_MOR_NAME -> MF_SPEC_NAME ->  Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF) -> Bool
isSource localMorSet specName morMap =  Map.foldrWithKey v False morMap
         where 
               v morName ((sN,tN),mor) p
                       | Set.member morName localMorSet
                       , specName == sN = True
                       | otherwise = p


{-|
This function cheks whether a node |Sender | belongs to a given architecture | L | or not
-}
isNodeExist :: MF_SPEC_NAME -> MF_DIAGNODE_NAME -> Map MF_DIAGNODE_NAME SysArch -> Bool
isNodeExist spN archName archMap = let
         theArch = Map.lookup archName archMap
         nodeSet = sa_nodes $ fromJust theArch
         in Set.member spN nodeSet

{-|
The Map values are disjoint union, i.e.,  sets of MF_SPEC_NAME are disjoint union.
The first successful lookup is used.
|lookupInArchs archMap specName = Just an| iff |specName| occurs as a diagram node in the SysArch identified by |an|.
-}
lookupInArchs :: Map MF_DIAGNODE_NAME SysArch 
    -> MF_SPEC_NAME -> Maybe MF_DIAGNODE_NAME
lookupInArchs archMap specName = case man of
    Nothing -> trace ("lookupInArchs: " ++ shows specName " not found!") Nothing
    _ -> man
  where
    man = Map.foldWithKey f Nothing archMap
    f an spns r
      | Set.member specName (sa_nodes spns) = Just an
      | otherwise = r

{-|
For a given dgraph and specification it returns all the morphisms
-}

extractMorphismsFromLibEnv :: DGraph
  -> Map MF_SPEC_NAME SysArchNodeLabel
  ->  Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)

extractMorphismsFromLibEnv dgraph nodes = trace "========= extractMorphismsFromLibEnv =========" $
  let
    Just (specDfn@(Lib_defn _ aItems _ _)) = optLibDefn dgraph 
    edges = foldr h Map.empty aItems
    h (Annoted (View_defn iri _ (View_type s1 s2 _) gmap _) _ _ _)
      = let
           morName = drop 1 $ abbrevQuery iri
           extractSpecName (Annoted (Spec_inst cName _ _ _) _ _ _)
             = trace ("\n!!! extractMorphismsFromLibEnv: cName: iriPath = " ++ iriPath cName ++ "; iriQuery = " ++ iriQuery cName ++
               "; prefixName = " ++ prefixName cName ++ "; abbrevPath = " ++ abbrevPath cName ++
               "; abbrevQuery = " ++  abbrevQuery cName) $
              abbrevPath cName
           srcNode = extractSpecName s1
           trgNode = extractSpecName s2
           gsymMapItemList = case gmap of
                            --  [G_symb_map [Symb_map_items _ sml]] -> sml
                               G_symb_map sml : _ -> sml
                               [] -> G_symb_map_items_list MFLogic []
                               _ -> error $ "extractMorphismsFromLibEnv: gmap = " ++ show gmap

       in case unGSymbMapItemsList gsymMapItemList of
        -- [] -> id
         sil -> maybe id (Map.insert morName) $ do
           srcExtSig <- sanl_ExtSig <$> Map.lookup srcNode nodes
           trgExtSig <- sanl_ExtSig <$> Map.lookup trgNode nodes
           let  srcSig = plainSign srcExtSig
           let  trgSig = plainSign trgExtSig


           case stat_symb_map_items MFLogic srcSig (Just trgSig) sil >>= \ endoMap ->
                induced_from_to_morphism MFLogic endoMap srcExtSig trgExtSig of
             Result _ (Just mor) -> Just ((srcNode, trgNode), mor)
             _ -> Nothing

    h _ = id
  in edges     



{-|
?????
-}
zigZagGraphTransformation :: LibName -> LibEnv -> Result LibEnv
zigZagGraphTransformation libName libEnv = trace ("ZigZagGraphTransformation " ++ show libName) $ do
   let dgraph = lookupDGraph libName libEnv
   let archDiags = archSpecDiags dgraph
   let nodeNames = nameMap dgraph
   let bodyDg    = dgBody dgraph
   let globEnvDg = globalEnv dgraph
   let theoryMap = thMap dgraph
   let listNode = nodesDG dgraph  -- ^ list of nodes in number
   -- labDG :: DGraph -> Node -> DGNodeLab
   let dgNodeString = getNameOfNode  3 dgraph -- ^ get the name of the node String
   let dgNodeLabel = labDG dgraph 3
   let dgnTheory   = dgn_theory dgNodeLabel
   -- morMapI :: DGraph -> (Map.Map MorId G_morphism, MorId)
   let mormapID = morMapI dgraph
   let mMap      = morMap dgraph
   let sysArchALL = extractSysArchDiagramFromLibEnv dgraph
   let coreSysArch = extractCoreFromSysArchDiagram sysArchALL
   let preMorMap :: Map MF_MOR_NAME ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
       preMorMap = extractMorphismsFromLibEnv dgraph $ mfsaDiag_allSpecs sysArchALL
       addLoc :: ((MF_SPEC_NAME, MF_SPEC_NAME), MorphismMF)
              -> ((MF_SPEC_NAME, MF_SPEC_NAME), ((Maybe FormulaMF, Maybe FormulaMF), MorphismMF))
       addLoc (p, m) = let
           src = msource m
           trg = mtarget m
           srcLocality = localityAxiom src
           trgLocality = localityAxiom trg
           -- Just srcLocality' = maybeResult $ map_sen MFLogic m srcLocality
           -- |srcLocality'| has to be a consequence of |trgLocality| and the |trg| axioms.
        in (p, ((srcLocality, trgLocality), m))
   -- Worked from HERE 
   let archSpecNames = extractSysArchDiagramNodesFromLibEnv dgraph
   let spanArchNames = names
           where
              names = case extractArchNodesNameOfaSpan coreSysArch of
                       Just n -> n
                       Nothing -> error "Man!, Could not find any Architecture Name, error in extractArchNodesNameOfaSpan"
   let theSpan = archAndZhom0
           where
              archAndZhom0 = case extractSystemArchAndZhom coreSysArch spanArchNames of
                                 Just ne -> ne
                                 Nothing -> error "Oops! no span, might be error in  extractSystemArchAndZhom"
   let coSpanNodeInfoOnly = computeNodeSpecZhomAtResultArch coreSysArch theSpan "B" 
   let coSpan = completeResultCoSpan coreSysArch theSpan "B" coSpanNodeInfoOnly                   
  --  let localTh   = computeLocalTheory libEnv libName
   -- let archs :: Map ArchId ([Spec], [Morphism])
   -- let archMors :: [((ArchId, ArchId), [Morphism])]
   fail $ -- "ZigZagGraphTransformation: Not yet implemented\n" ++  show archDiags ++
           (replicate 80 '=' ++ "\n" ++ shows (text "Result Arch. B = " <+> pretty (porcObj coSpan)) ('\n' : replicate 80 '=' ++ "\n") ) ++
           (replicate 80 '=' ++ "\n Three Architecture Name = " ++ shows spanArchNames ('\n' : replicate 80 '=' ++ "\n") ) ++
           (replicate 80 '=' ++ "\n The Span = " ++ shows theSpan ('\n' : replicate 80 '=' ++ "\n") ) ++
           (replicate 80 '=' ++ "\n CoSpan Nodes Info Only = " ++ shows coSpanNodeInfoOnly ('\n' : replicate 80 '=' ++ "\n") ) ++
           (replicate 80 '=' ++ "\n CoSpan = " ++ shows coSpan ('\n' : replicate 80 '=' ++ "\n") ) ++
           (replicate 80 '=' ++ "\nCore System Architecture Diagram= " ++ shows coreSysArch ('\n' : replicate 80 '=' ++ "\n") ) ++
           "Zigzaggraph Node label=====" ++  show dgNodeLabel ++ "\n" ++
           "Morphism Map Id for DGraph=====" ++  show mormapID ++ "\n" ++
           "ZigZagGraph Theory =======" ++  show dgnTheory ++"\n" ++
           "Zigzaggraph list of Node====" ++  show listNode ++ "\n" ++
           "Zigzaggraphdg Node String for Node 3 is ==\n" ++  show dgNodeString ++"\n" ++
          (replicate 80 '=' ++ "\n" ++ shows (text "archSpecNames = " <+> pretty archSpecNames) "\n") ++
          (replicate 80 '=' ++ "\nsysArchALL = " ++ shows sysArchALL ('\n' : replicate 80 '=' ++ "\n")
          ) ++
          (replicate 80 '=' ++ "\n" ++ shows (text "preMorMap = " <+> pretty (Map.map addLoc preMorMap)) "\n") ++
          (case optLibDefn dgraph of
             Nothing -> "=== No optLibDefn ===\n"
             Just libDefn -> "=== optLibDefn = " ++ shows libDefn "\n"
          ) ++ "ZigZagGraph mor Map\n" ++  show mMap ++ "\n" ++
        
          "\nNodes by name\n" ++ unlines (map (("    " ++) . show) $ MapSet.toList nodeNames) ++
          "\nspecRoots\n" ++ unlines (map (("    " ++) . show) . Map.toList $ specRoots dgraph) ++
          -- next candidate: |morMap dgraph|
          "\n body of the dgraph\n" ++ show bodyDg ++
           "\n global Environment\n" ++
              (unlines (concatMap ((replicate 50 '=' :) . (: []) . show) $ Map.toList globEnvDg))



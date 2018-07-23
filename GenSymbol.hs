
data GenSymbol symbType = GenSymbol
   { symName :: Id
   , symbType :: symbType
   }
   deriving (Show, Eq, Ord, Typeable, Data)

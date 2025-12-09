module Generics.Instant.TH.Utils (
    typ,
    typeVariables,
    tyVarBndrToName,
    tyVarBndrsToNames,
    toSpecificityBndr,
    toPlainBndr
) where

import Language.Haskell.TH


-- Helper functions for Template Haskell
typ :: Name -> Info -> Q Type
typ q i = return $ foldl (\a -> AppT a . VarT . tyVarBndrToName) (ConT q)
            (typeVariables i)

typeVariables :: Info -> [TyVarBndr Specificity]
typeVariables (TyConI (DataD    _ _ tv _ _ _)) = map toSpecificityBndr tv
typeVariables (TyConI (NewtypeD _ _ tv _ _ _)) = map toSpecificityBndr tv
typeVariables _                           = []

tyVarBndrToName :: TyVarBndr Specificity -> Name
tyVarBndrToName (PlainTV  name _)   = name
tyVarBndrToName (KindedTV name _ _) = name

toSpecificityBndr :: TyVarBndr () -> TyVarBndr Specificity
toSpecificityBndr (PlainTV name _) = PlainTV name InferredSpec
toSpecificityBndr (KindedTV name _ kind) = KindedTV name InferredSpec kind

toPlainBndr :: TyVarBndr Specificity -> TyVarBndr ()
toPlainBndr (PlainTV name _) = PlainTV name ()
toPlainBndr (KindedTV name _ kind) = KindedTV name () kind

-- bndrVisToSpec :: TyVarBndr BndrVis -> TyVarBndr Specificity

tyVarBndrsToNames :: [TyVarBndr Specificity] -> [Name]
tyVarBndrsToNames = map tyVarBndrToName

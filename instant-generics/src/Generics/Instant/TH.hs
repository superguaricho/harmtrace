{-# LANGUAGE TemplateHaskell, LambdaCase, RecordWildCards, CPP #-}
{-# OPTIONS_GHC -w                #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Instant.TH
-- Copyright   :  (c) 2011 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module contains Template Haskell code that can be used to
-- automatically generate the boilerplate code for the generic deriving
-- library.
-----------------------------------------------------------------------------

-- Adapted from Generics.Deriving.TH
module Generics.Instant.TH (
    -- * Main generator
      deriveAll, deriveAllL

    -- * Individual generators
    , deriveConstructors
    , deriveRepresentable
    , deriveRep

    -- * Utilities
    , simplInstance, gadtInstance
    , genRepName, typeVariables, tyVarBndrToName
  ) where

import Generics.Instant.Base
import Generics.SYB (everywhere, mkT, everything, mkQ, gshow, extQ)

import Language.Haskell.TH hiding (Fixity())
import Language.Haskell.TH.Syntax (Lift(..), showName)

import Data.List (intercalate, nub, elemIndex)
import qualified Data.Map as M
import Control.Monad
import Control.Arrow ((&&&))

-- Used by gadtInstance
data TypeArgsEqs = TypeArgsEqs { args :: [Type]        -- ^ Constructor args
                               , vars :: [Name]        -- ^ Variables
                               , teqs :: [(Type,Type)] -- ^ Type equalities
                               } deriving Show

-- | Given the names of a generic class, a type to instantiate, a function in
-- the class and the default implementation, generates the code for a basic
-- generic instance.
simplInstance :: Name -> Name -> Name -> Name -> Q [Dec]
simplInstance cl ty fn df = do
  i <- reify ty
  let typ = return (foldl (\a -> AppT a . VarT . tyVarBndrToName)
                              (ConT ty) (typeVariables i))
  (: []) <$> instanceD (cxt []) (conT cl `appT` typ)
    [funD fn [clause [] (normalB (varE df)) []]]

-- | Given the names of a generic class, a GADT type to instantiate, a function
-- in the class and the default implementation, generates the code for a basic
-- generic instance. This is tricky in general because we have to analyze the
-- return types of each of the GADT constructors and give instances accordingly.
gadtInstance :: Name -> Name -> Name -> Name -> Q [Dec]
gadtInstance cl ty fn df = do
  -- runIO $ putStrLn $ "--- gadtInstance for " ++ show ty
  i <- reify ty
  let typ = foldl (\a -> AppT a . VarT . tyVarBndrToName)
                              (ConT ty) (typeVariables i)

      dt :: ([TyVarBndr ()],[Con])
      dt = case i of
             TyConI (DataD _ _ vs _ cs _) -> (vs, cs)
             _ -> error ("gadtInstance: " ++ show ty ++ "is not a valid type")

      -- List of index variable names
      idxs :: [Name]
      idxs = uncurry extractIndices dt

      -- Get all the arguments, variables, and type equalities introduced by the
      -- constructors
      eqs :: [Name] -> [Con] -> [TypeArgsEqs]
      eqs nms = map f where
        f :: Con -> TypeArgsEqs
        f (NormalC _ tys)    = TypeArgsEqs (map snd tys)             [] []
        f (RecC _ tys)       = TypeArgsEqs (map (\(_,_,t) -> t) tys) [] []
        f (InfixC t1 _ t2)   = TypeArgsEqs [snd t1, snd t2]          [] []
        f (ForallC vs cxt c) = case f c of
            TypeArgsEqs ts vs' eqs' ->
              TypeArgsEqs ts (tyVarBndrsToNames vs ++ vs')
                          (concatMap g cxt ++ eqs')
        f (GadtC _ tys _)    = TypeArgsEqs (map snd tys)             [] []
        f (RecGadtC _ tys _) = TypeArgsEqs (map (\(_,_,t) -> t) tys) [] []
        g :: Pred -> [(Type,Type)]
#if MIN_VERSION_template_haskell(2,10,0)
        g (AppT (AppT EqualityT (VarT t1)) t2)
#else
        g (EqualP (VarT t1) t2)
#endif
          | t1 `elem` nms = [(VarT t1,t2)]
          | otherwise     = []
        g _ = []

      subst :: [(Type,Type)] -> Type -> Type
      subst s = everywhere (mkT f) where
        f (VarT a) = case lookup (VarT a) s of
                       Nothing -> VarT a
                       Just t  -> t
        f x        = x

      mkInst :: TypeArgsEqs -> Dec
      mkInst t = InstanceD Nothing (map mkCxt (args t))
                           (ConT cl `AppT` subst (teqs t) typ) instBody

      mkCxt :: Type -> Pred
      mkCxt =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT cl)
#else
        ClassP cl . (:[])
#endif

      -- The instance body is empty for regular cases
      instBody :: [Dec]
      instBody = [FunD fn [Clause [] (NormalB (VarE df)) []]]

      update :: TypeArgsEqs -> [TypeArgsEqs] -> [TypeArgsEqs]
      -- update True  t1 [] = [t1]
      update _  [] = []
      update t1 (t2:ts) | teqs t1 == teqs t2 =
                            t2 {args = nub (args t1 ++ args t2)} : ts
                        | otherwise          = t2 : update t1 ts

      -- Types without any type equalities (not real GADTs) need to be handled
      -- differently. Others are dealt with using filterMerge.
      handleADTs :: ([TypeArgsEqs] -> [TypeArgsEqs])
                 -> [TypeArgsEqs] -> [TypeArgsEqs]
      handleADTs f ts | all (null . teqs) ts
                      = [TypeArgsEqs (concatMap args ts) [] []]
                      | otherwise = f ts

      -- We need to
      -- 1) ignore constructors that don't introduce any type equalities
      -- 2) merge constructors with the same return type
      -- This code is terribly inefficient and could easily be improved, btw.
      filterMerge :: [TypeArgsEqs] -> [TypeArgsEqs]
      filterMerge (t0@(TypeArgsEqs ts vs eqs):t)
        | eqs == [] = update t0 (filterMerge t)
        | otherwise = case filterMerge t of
            l -> if any (\t2 -> any (\eq1 -> any (\eq2 -> typeMatch vs (vars t2) eq1 eq2) (teqs t2)) eqs) l
                 then update t0 l
                 else t0 : l
      filterMerge [] = []
      
      -- For (2) above, we need to consider type equality modulo
      -- quantified-variable names
      typeMatch :: [Name] -> [Name] -> (Type,Type) -> (Type,Type) -> Bool
      typeMatch vs1 vs2 eq1 eq2 | length vs1 /= length vs2 = False
                                | otherwise
                                = eq1 == everywhere (mkT f) eq2
        where f (VarT n) = case n `elemIndex` vs2 of
                             -- is not a quantified variable
                             Nothing -> VarT n
                             -- it is, replace it with the equivalent var
                             Just i  -> VarT (vs1 !! i)
              f x        = x

      allTypeArgsEqs = eqs idxs (snd dt)

      normInsts = map mkInst   (handleADTs filterMerge allTypeArgsEqs)

  -- runIO  $ putStrLn $ "--- gadtInstance generated: " ++ show (length normInsts) ++ " instances"
  return $ normInsts


-- | Given the type and the name (as string) for the type to derive,
-- generate the 'Constructor' instances and the 'Representable' instance.
deriveAll :: Name -> Q [Dec]
deriveAll n = do
  do a <- deriveConstructors n
     b <- deriveRepresentable n
--     runIO $ putStrLn $ "** Constructors: "  ++ show a
--     runIO $ putStrLn $ "** Representable: " ++ show b
     return (a ++ b)

-- | Same as 'deriveAll', but taking a list as input.
deriveAllL :: [Name] -> Q [Dec]
deriveAllL = fmap concat . mapM deriveAll

-- | Given a datatype name, derive datatypes and
-- instances of class 'Constructor'.
deriveConstructors :: Name -> Q [Dec]
deriveConstructors = constrInstance

-- | Given the type and the name (as string) for the Representable type
-- synonym to derive, generate the 'Representable' instance.
deriveRepresentable :: Name -> Q [Dec]
deriveRepresentable n = do
  -- runIO $ putStrLn $ " === DERIVEREPRESENTABLE FOR: " ++ show n
  rep <- deriveRep n
  inst <- deriveInst n
  -- runIO $ putStrLn $ "********** rep ++ inst: " ++ show rep ++ show inst
  return $ rep ++ inst

-- | Derive only the 'Rep' type synonym. Not needed if 'deriveRepresentable'
-- is used.
deriveRep :: Name -> Q [Dec]
deriveRep n = do
  -- runIO $ putStrLn $ "=== Calling deriveRep for: " ++ show n
  i <- reify n
  -- runIO $ putStrLn $ "REIFY RESULT: " ++ show i
  let d = case i of
            TyConI dec -> dec
            _ -> error "unknown construct"
  let getDt :: Dec -> Name
      getDt (DataD _ dt _ _ _ _) = dt
  -- runIO $ putStrLn $ "*** Data type: " ++ show (getDt d)
  exTyFamsInsts <- genExTyFamInsts d
  -- runIO $ putStrLn $ "*** exTyFamsInsts: " ++ show exTyFamsInsts
  (: exTyFamsInsts) <$>
    tySynD (genRepName n) (typeVariables i) (repType d (typeVariables i))

-- | Construct the `Rep Foo` type from the `Foo`real definition. Here is
-- translated each constructor to `:+:` (sum), `:*:` (product), `CEq`
-- (indice equalities), `Rec` (recursión), etc.
deriveInst :: Name -> Q [Dec]
deriveInst t = do
  i <- reify t
  let typ q = return $ foldl (\a -> AppT a . VarT . tyVarBndrToName) (ConT q)
                (typeVariables i)
      -- inlPrg = pragInlD t (inlineSpecPhase True False True 1)
  fcs <- mkFrom t 1 0 t
  tcs <- mkTo   t 1 0 t
  (:[]) <$>
    instanceD (cxt [])
      (conT ''Representable `appT` typ t)
        [
#if MIN_VERSION_template_haskell(2,15,0)
          do
            actualTyp <- typ t
            let repTypName = (genRepName t)
            -- runIO $ putStrLn $ "== + TypName : " ++ show repTypName 
            repTyp <- typ repTypName
            repTypeCon <- conT ''Rep
            let lhsType = AppT repTypeCon actualTyp
            -- runIO $ putStrLn $ "== + lhsType : " ++ show lhsType 
            let tysyn = TySynInstD (TySynEqn Nothing lhsType repTyp)
            -- runIO $ putStrLn $ "== + From deriveInst, tysyn: " ++ show tysyn
            return $ tysyn
#elif __GLASGOW_HASKELL__ >= 707
          tySynInstD ''Rep (TySynEqn [typ t] (typ (genRepName t)))
#else
          tySynInstD ''Rep [typ t] (typ (genRepName t))
#endif
        , {- inlPrg, -} funD 'from fcs, funD 'to tcs]

constrInstance :: Name -> Q [Dec]
constrInstance n = do
  i <- reify n
  case i of
    TyConI (DataD    _ n _ _ cs _) -> mkInstance n cs
    TyConI (NewtypeD _ n _ _ c  _) -> mkInstance n [c]
    _ -> return []
  where
    mkInstance n cs = do
      ds <- mapM (mkConstrData n) cs
      is <- mapM (mkConstrInstance n) cs
      return $ ds ++ is

typeVariables :: Info -> [TyVarBndr ()]
typeVariables (TyConI (DataD    _ _ tv _ _ _)) = tv
typeVariables (TyConI (NewtypeD _ _ tv _ _ _)) = tv
typeVariables _                                = []

tyVarBndrsToNames :: [TyVarBndr flag] -> [Name]
tyVarBndrsToNames = map tyVarBndrToName

tyVarBndrToName :: TyVarBndr flag -> Name
tyVarBndrToName (PlainTV  name _)   = name
tyVarBndrToName (KindedTV name _ _) = name

stripRecordNames :: Con -> Con
stripRecordNames (RecC n f) =
  NormalC n (map (\(_, s, t) -> (s, t)) f)
stripRecordNames c = c

genName :: [Name] -> Name
genName = mkName . (++"_") . intercalate "_" . map nameBase

genRepName :: Name -> Name
genRepName = mkName . (++"_") . ("Rep"  ++) . nameBase

mkConstrData :: Name -> Con -> Q Dec
mkConstrData dt (NormalC n _) =
  dataD (cxt []) (genName [dt, n]) [] Nothing [] []
mkConstrData dt r@(RecC _ _) =
  mkConstrData dt (stripRecordNames r)
mkConstrData dt (InfixC t1 n t2) =
  mkConstrData dt (NormalC n [t1,t2])
-- Contexts are ignored
mkConstrData dt (ForallC _ _ c) = mkConstrData dt c
mkConstrData dt (GadtC [n] _ _) = dataD (cxt []) (genName [dt, n]) [] Nothing [] []
mkConstrData dt (RecGadtC [n] _ _) = dataD (cxt []) (genName [dt, n]) [] Nothing [] []
mkConstrData dt _ = error "mkConstrData: unsupported constructor"

instance Lift Fixity where
  lift Prefix      = conE 'Prefix
  lift (Infix a n) = conE 'Infix `appE` [| a |] `appE` [| n |]

instance Lift Associativity where
  lift LeftAssociative  = conE 'LeftAssociative
  lift RightAssociative = conE 'RightAssociative
  lift NotAssociative   = conE 'NotAssociative

mkConstrInstance :: Name -> Con -> Q Dec
-- Contexts are ignored
mkConstrInstance dt (ForallC _ _ c) = mkConstrInstance dt c
mkConstrInstance dt (NormalC n _) = mkConstrInstanceWith dt n []
mkConstrInstance dt (RecC    n _) = mkConstrInstanceWith dt n
      [ funD 'conIsRecord [clause [wildP] (normalB (conE 'True)) []]]
mkConstrInstance dt (InfixC t1 n t2) =
  do
    mf <- reifyFixity n
    case mf of
      Just f -> return $ convertFixity f
      Nothing -> return Prefix
    instanceD (cxt []) (appT (conT ''Constructor) (conT $ genName [dt, n]))
      [funD 'conName   [clause [wildP] (normalB (stringE (nameBase n))) []],
       funD 'conFixity [clause [wildP] (normalB [| fi |]) []]]
  where
    convertFixity (Fixity n d) = Infix (convertDirection d) n
    convertDirection InfixL = LeftAssociative
    convertDirection InfixR = RightAssociative
    convertDirection InfixN = NotAssociative
mkConstrInstance dt (GadtC [n] _ _) = mkConstrInstanceWith dt n []
mkConstrInstance dt (RecGadtC [n] _ _ ) = mkConstrInstanceWith dt n []
mkConstrInstance dt _ = error "mkConstrInstance; unsupported constructor"

mkConstrInstanceWith :: Name -> Name -> [Q Dec] -> Q Dec
mkConstrInstanceWith dt n extra =
  instanceD (cxt []) (appT (conT ''Constructor) (conT $ genName [dt, n]))
    (funD 'conName [clause [wildP] (normalB (stringE (nameBase n))) []] : extra)

repType :: Dec -> [TyVarBndr flag] -> Q Type
repType i repVs = do
  -- runIO $ putStrLn "=== RET_TYPE DEBUG ==="
  -- runIO $ putStrLn $ "Input of: " ++ show i
  do let sum :: Q Type -> Q Type -> Q Type
         sum a b = conT ''(:+:) `appT` a `appT` b
     case i of
        (DataD _ dt vs _ cs _) ->
          foldBal' sum (error "Empty datatypes are not supported.")
            (map (repConGADT (dt, tyVarBndrsToNames vs) repVs
                   (extractIndices vs cs)) cs)
          {- runIO $ putStrLn "=== COSTRUCTORS ==="
             forM_ cs $ \con -> do
               runIO $ putStrLn $ "Constructor: "++ show con
               case con of
                 GadtC names _ _ ->
                   runIO $ putStrLn $ " -> GADT CONSTRUCTOR " ++ show names
                 _ ->
                   runIO $ putStrLn "-> Regular constructor"
             runIO $ putStrLn $ " --> Calling foldBal'"
                foldBal' sum (error "Empty datatypes are not supported.")
                  (map (repConGADT (dt, tyVarBndrsToNames vs) repVs (extractIndices vs cs)) cs)
            -}
        (NewtypeD _ dt vs _ c _) -> repConGADT (dt, tyVarBndrsToNames vs) repVs (extractIndices vs [c]) c
        (TySynD t _ _)           -> error "type synonym?"
        _                        -> error "unknown construct"


-- 
                  
-- Given a datatype declaration, returns a list of its type variables which are
-- used as index and not as data
extractIndices :: [TyVarBndr flag] -> [Con] -> [Name]
extractIndices vs = nub . everything (++) ([] `mkQ` isIndexEq `extQ` fromGadt) where
  gadtVars = tyVarBndrsToNames vs

  isIndexEq :: Pred -> [Name]
  isIndexEq p = case p of
#if MIN_VERSION_template_haskell(2,10,0)
     AppT (AppT EqualityT (VarT a)) (VarT b)
#else
     EqualP (VarT a) (VarT b)
#endif
       -> [v | v <- [a, b], v `elem` gadtVars]
#if MIN_VERSION_template_haskell(2,10,0)
     AppT (AppT EqualityT (VarT a)) _
#else
     EqualP (VarT a) _
#endif
       -> [a | a `elem` gadtVars] 
       --  if a `elem` gadtVars then [a] else []
#if MIN_VERSION_template_haskell(2,10,0)
     AppT (AppT EqualityT _) (VarT a)
#else
     EqualP _ (VarT a)
#endif
       -> [a | a `elem` gadtVars] 
       --  if a `elem` gadtVars then [a] else []
     _ -> []

  fromGadt :: Con -> [Name]
  fromGadt (GadtC _ _ retType) =
    let
      unapply (AppT f a) = let (base, args) = unapply f in (base, args ++ [a])
      unapply t          = (t, [])

      getVars = everything (++) ([] `mkQ` (\case VarT n -> [n]; _ -> []))

      (_, args) = unapply retType
      free_vars_in_args = nub (concatMap getVars args)
    in
      [v | v <- gadtVars, v `notElem` free_vars_in_args]
  fromGadt _ = []

--

getFirstTypeVar :: Name -> Q Name
getFirstTypeVar typeName = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tyVars _ _ _) ->
      case tyVars of
        [] -> error $ "No type variables in " ++ show typeName
        (firstVar:_) -> return (tyVarBndrToName firstVar)
    _ -> error $ "Not a data type: " ++ show typeName

getTypeVars :: Name -> Q [Name]
getTypeVars typeName = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tyVars _ _ _) ->
      return (map tyVarBndrToName tyVars)
    _ -> error $ "Not a data type: " ++ show typeName

-- |
-- extractEqualityFromReturnType: Extract equality from the return type.
extractEqualityFromReturnType :: Type -> Name -> Q (Name, Type)
extractEqualityFromReturnType repType expectedType =
  case repType of
    AppT (ConT typeName) concreteType
     | typeName == expectedType
     -> do
          typeVars <- getTypeVars typeName
          case typeVars of
                    [] -> error $ "No type variables in " ++ show typeName
                    (firstVar:_) -> return (firstVar, concreteType)
extractEqualityFromReturnType t _ =
  error $ "Cannot extract equality from return type: " ++ show t

-- extractEqualityFromReturnType :: Type -> (Name, Type)
-- extractEqualityFromReturnType (AppT (ConT typeName) concreteType) = 
  -- Para T Mm: typeName = T, concreteType = Mm
  -- Necesitas encontrar el índice (m) de T
--   (findIndexVar typeName, concreteType)
-- extractEqualityFromReturnType _ = error "Not a simple GADT constructor"

unApply :: Type -> [Type]
unApply t = go t []
  where
    go (AppT f x) acc = go f (x:acc)
    go t acc = t:acc

-- | Función de Análisis Unificada
analyzeGadtConstructor :: (Name, [Name]) -> [Name] -> Con -> Q (Type, Type -> Type)
analyzeGadtConstructor d@(dt, dtVs) [indexVar] (ForallC vs ctx c) = do
   -- 1. Descubrir reglas de movilidad (código que ya existe)
   let vsN = tyVarBndrsToNames vs
       mRules = mobilityRules vsN ctx

   -- 2. Crear la función de sustitución (código que ya existe)
       substTyVar :: [Name] -> Type -> Type -- La función que reemplaza un tipo por `X ...`
       substTyVar ns = everywhere (mkT f) where
           f (VarT v) = case elemIndex v ns of
                          Nothing -> VarT v
                          Just i  -> ConT ''X
                                      `AppT` ConT (genName [dt,getConName c])
                                      `AppT` int2TLNat i
                                      `AppT` VarT indexVar
           f x        = x
       subst = if null mRules then id else substTyVar vsN
   -- 3. Generar la representación del tipo para este (usando el  ya sustituido)
       c' = case c of
         NormalC cn fields -> NormalC cn (map (fmap subst) fields)
         RecC cn fields    -> RecC    cn (map (\(n,s,t) -> (n,s,subst t)) fields)
         InfixC t1 cn t2   -> InfixC (fmap subst t1) cn (fmap subst t2)
         _                 -> c      
   rep <- repCon d c' (genTypeEqs ctx)
   -- 4. Devolver AMBOS resultados
   return (rep, subst)
   where
      genTypeEqs :: Cxt -> (Type, Type)
      genTypeEqs [] = baseEqs
      genTypeEqs (p:r) = case p of
#if MIN_VERSION_template_haskell(2,10,0)
         (AppT (AppT EqualityT t1) t2) -> (t1, t2)
#else
         (EqualP t1 t2) -> (t1, t2)
#endif
         _ -> genTypeEqs r
-- Caso para constructores que no son GADT
analyzeGadtConstructor d _ c = do
  let subst = id
  rep <- repCon d c baseEqs
  return (rep, subst)

--

repConGADT :: (Name, [Name]) -> [TyVarBndr flag] -> [Name] -> Con -> Q Type
repConGADT d@(dt, dtVs) repVs [indexVar] (GadtC [conName] fields resTy) = do
  -- runIO $ putStrLn "Case GadtC in repConGADT************************************************"
  -- runIO $ putStrLn $ "Constructor: " ++ show conName
  let parts = unApply resTy
  case parts of
    (ConT dtName : args) -> do
      let idxTy = last args
      --  let (ConT dtName `AppT` _paramA `AppT` idxTy) = resTy
          t1 = VarT indexVar   -- índice de la definición
          prod = foldBal (\a b -> conT ''(:*:) `appT` a `appT` b)
                     (map (repField (dt, dtVs) . snd) fields)
      conT ''CEq `appT` conT (genName [dt, conName])
                 `appT` return t1
                 `appT` return idxTy
                 `appT` prod
    _ -> fail $ "repConGadt: resTy no es aplicaión a ConT, sino: " ++ show resTy
repConGADT (dt, dtVs) _repVs [indexVar] (RecGadtC [conName] fields resTy) = do
  let (ConT dtName `AppT` _paramA `AppT` idxTy) = resTy
      t1 = VarT indexVar
      t2 = idxTy
      prod = foldBal (\a b -> conT ''(:*:) `appT` a `appT` b)
                     (map (repField' (dt, dtVs) conName) fields)
  conT ''CEq `appT` conT (genName [dt, conName])
              `appT` return t1
              `appT` return t2
              `appT` prod
repConGADT d@(dt, dtVs) repVs idxVars c = do
   (rep, _) <- analyzeGadtConstructor d idxVars c
   return rep
repConGADT _ _ vs@(_:_:_) ForallC{} =
  error ("Datatype indexed over >1 variable: " ++ show vs)
-- No constraints, go on as usual
-- Fallback para NormalC, RecC, InfixC
repConGADT d _ _ c = repCon d c baseEqs

-- Extract the constructor name
getConName :: Con -> Name
getConName (NormalC n _)      = n
getConName (RecC n _)         = n
getConName (InfixC _ n _)     = n
getConName (ForallC _ _ c)    = getConName c
getConName (GadtC [n] _ _)    = n
getConName (RecGadtC [n] _ _) = n

-- Generate a type-level natural from an Int
int2TLNat :: Int -> Type
int2TLNat 0 = ConT 'Ze
int2TLNat n = ConT 'Su `AppT` int2TLNat (n-1)

-- Generate the mobility rules for the existential type families
genExTyFamInsts :: Dec -> Q [Dec]
genExTyFamInsts (DataD    _ n _ _ cs _) = concat <$>
                                          mapM (genExTyFamInsts' n) cs
genExTyFamInsts (NewtypeD _ n _ _ c  _) = genExTyFamInsts' n c


genExTyFamInsts' :: Name -> Con -> Q [Dec]
-- Caso: GADT sin registros
genExTyFamInsts' dt (GadtC [conName] _fields resTy) =
  mobilityFromResTy dt conName resTy
-- Caso: RecGadtC
genExTyFamInsts' dt (RecGadtC [conName] fields resTy) =
  genExTyFamInsts' dt
                   (GadtC [conName] (map (\(_,_,t) ->
                       (Bang NoSourceUnpackedness NoSourceStrictness, t)) fields)
                           resTy)                    
genExTyFamInsts' dt (ForallC vs cxt c) = do
  -- runIO $ putStrLn $ "Name: " ++ show dt
  -- runIO $ putStrLn $ "Constructor: " ++ show (getConName c)
  -- runIO $ putStrLn $ "Context: " ++ show cxt
  -- runIO $ putStrLn $ "Variables: " ++ show vs
  let mRules = mobilityRules (tyVarBndrsToNames vs) cxt
  -- runIO $ putStrLn $ " Mobility rules found" ++ show mRules
  do let mR = mobilityRules (tyVarBndrsToNames vs) cxt
         conName = ConT (genName [dt,getConName c])
#if MIN_VERSION_template_haskell(2,15,0)
         tySynInst ty n x = TySynInstD (TySynEqn Nothing
                                       (foldl AppT (ConT ''X) [conName, int2TLNat n, ty])
                                       x)
#elif __GLASGOW_HASKELL__ >= 707
         tySynInst ty n x = TySynInstD ''X (TySynEqn [conName, int2TLNat n, ty] x)
#else
         tySynInst ty n x = TySynInstD ''X [conName, int2TLNat n, ty] x
#endif
     return [ tySynInst ty n (VarT nm) | (n,(nm, ty)) <- zip [0..] mR ]
genExTyFamInsts' _ _ = return []

-- Extrae igualdades a partir de resTy y llama a mobilityRules
mobilityFromResTy :: Name -> Name -> Type -> Q [Dec]
mobilityFromResTy dt conName resTy = do
  -- runIO $ putStrLn $ "mobilityFromResTy: " ++ show dt 
  -- resTy tendrá forma: T v1 v2 ... vn
  let (ConT _ : args) = unApply resTy
      -- suponemos que el último argumento es el índice
      idxTy = last args
      
      -- variable de índice: por convención la llamamos "n"
      indexVar = mkName "n"
      
      -- fabricamos igualdad: n ~ idxTy
      eq = AppT (AppT EqualityT (VarT indexVar)) idxTy

      -- mobilityRules espera: (existenciales, contexto)
      -- aquí existenciales se deducirían de idxTy si hay
      mR = mobilityRules [indexVar] [eq]

      tySynInst ty n x = TySynInstD
                              (TySynEqn Nothing
                                (foldl AppT (ConT ''X) [ConT (genName [dt, conName]), int2TLNat n, ty]) x)

  return [ tySynInst ty n (VarT nm) | (n,(nm, ty)) <- zip [0..] mR ]

  where
  -- desarma aplicaciones (f x y z -> [f,x,y,z])
  unApply t = go t []
    where
      go (AppT f x) acc = go f (x:acc)
      go t acc = t:acc

-- Compute the shape of the mobility rules
mobilityRules :: [Name] -> Cxt -> [(Name,Type)]
mobilityRules [] _   = []
mobilityRules vs cxt = concat [ mobilityRules' v p | v <- vs, p <- cxt ] where
  mobilityRules' :: Name -> Pred -> [(Name,Type)]
  mobilityRules' v p = case p of
#if MIN_VERSION_template_haskell(2,10,0)
    AppT (AppT EqualityT (VarT _)) (VarT _)
#else
    EqualP (VarT _) (VarT _)
#endif
      -> []

#if MIN_VERSION_template_haskell(2,10,0)
    AppT (AppT EqualityT (VarT a)) x
#else
    EqualP (VarT a) x
#endif
      | v `inComplex` x -> [(v,x)]
      | otherwise -> []

#if MIN_VERSION_template_haskell(2,10,0)
    AppT (AppT EqualityT x) (VarT a)
      -> mobilityRules' v (AppT (AppT EqualityT (VarT a)) x)
#else
    EqualP x (VarT a)
      -> mobilityRules' v (EqualP (VarT a) x)
#endif
    _ -> []

  inComplex :: Name -> Type -> Bool
  inComplex v (VarT _) = False
  inComplex v x = everything (||) (False `mkQ` q) x where
    q (VarT x) | x == v    = True
               | otherwise = False
    q _                    = False

flattenEqs :: (Type, Type) -> Q Type
flattenEqs (t1, t2) = return t1 `appT` return t2

-- () ~ ()
baseEqs :: (Type, Type)
baseEqs = (TupleT 0, TupleT 0)

repCon :: (Name, [Name]) -> Con -> (Type,Type) -> Q Type
repCon d (ForallC _ _ c) eqs = repCon d c eqs
repCon (dt, vs) (NormalC n []) (t1,t2) =
    conT ''CEq `appT` conT (genName [dt, n]) `appT` return t1
                                               `appT` return t2 `appT` conT ''U
repCon (dt, vs) (NormalC n fs) (t1,t2) =
    conT ''CEq `appT` conT (genName [dt, n]) `appT` return t1
                                               `appT` return t2 `appT`
      foldBal prod (map (repField (dt, vs) . snd) fs) where
    prod :: Q Type -> Q Type -> Q Type
    prod a b = conT ''(:*:) `appT` a `appT` b
repCon (dt, vs) r@(RecC n []) (t1,t2)  =
    conT ''CEq `appT` conT (genName [dt, n]) `appT` return t1
                                               `appT` return t2 `appT` conT ''U
repCon (dt, vs) r@(RecC n fs) (t1,t2) =
    conT ''CEq `appT` conT (genName [dt, n]) `appT` return t1
                                               `appT` return t2 `appT`
      foldBal prod (map (repField' (dt, vs) n) fs) where
    prod :: Q Type -> Q Type -> Q Type
    prod a b = conT ''(:*:) `appT` a `appT` b
-- Constructor GADT normal (sin campos registrados)
repCon d@(dt, vs) (GadtC [n] fieldTypes _resultType) (t1, t2) = do
  -- runIO $ putStrLn $ "**** Processing GADT constructor: " ++ show n
  let prod :: Q Type -> Q Type -> Q Type
      prod a b = conT ''(:*:) `appT` a `appT` b
  let fieldReps = map (repField d . snd) fieldTypes  -- Procesa cada campo
  let foldedRep = foldBal prod fieldReps             -- Combínalos con productos
  -- Construye la representación final con GCeq1 (o CEq)
  -- runIO $ putStrLn $ "  * Folded representation: " ++ show foldedRep
  conT ''CEq `appT` conT (genName [dt, n]) `appT` return t1 `appT` return t2 `appT` foldedRep
-- Constructor GADT de registro (con campos registrados)  
repCon d@(dt, vs) (RecGadtC [n] fields _resultType) (t1, t2) = do
  -- runIO $ putStrLn $ "**** Processing RecGADT constructor: " ++ show n
  -- 'fields' es una lista de campos: [(Name, Strict, Type)]
  let prod :: Q Type -> Q Type -> Q Type
      prod a b = conT ''(:*:) `appT` a `appT` b
  let fieldReps = map (repField' d n) fields  -- Usa la función para campos registrados
  let foldedRep = foldBal prod fieldReps
  conT ''CEq `appT` conT (genName [dt, n]) `appT` return t1 `appT` return t2 `appT` foldedRep
repCon _ _ _ = error "repCon: unsupported constructor"

dataDeclToType :: (Name, [Name]) -> Type
dataDeclToType (dt, vs) = foldl (\a b -> AppT a (VarT b)) (ConT dt) vs

repField :: (Name, [Name]) -> Type -> Q Type
repField d t = conT ''Rec `appT` return t
--repField d t | t == dataDeclToType d = conT ''I

repField' :: (Name, [Name]) -> Name -> (Name, Strict, Type) -> Q Type
repField' (dt, vs) ns (f, _, t) = conT ''Rec `appT` return t
-- Note: we should generate Var too, at some point
--repField' d ns (_, _, t) | t == dataDeclToType d = conT ''I

mkFrom :: Name -> Int -> Int -> Name -> Q [Q Clause]
mkFrom ns m i n =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapE e = e -- lrE m i e
      i <- reify n
      let b = case i of
                TyConI (DataD _ dt vs _ cs _) ->
                  zipWith (fromCon wrapE ns (dt, map tyVarBndrToName vs)
                    (length cs)) [1..] cs
                TyConI (NewtypeD _ dt vs _ c _) ->
                  [fromCon wrapE ns (dt, map tyVarBndrToName vs) 1 0 c]
                TyConI (TySynD t _ _) -> error "type synonym?"
                  -- [clause [varP (field 0)] (normalB (wrapE $ conE 'K1 `appE` varE (field 0))) []]
                _ -> error "unknown construct"
      return b

mkTo :: Name -> Int -> Int -> Name -> Q [Q Clause]
mkTo ns m i n =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapP p = p -- lrP m i p
      i <- reify n
      let b = case i of
                TyConI (DataD _ dt vs _ cs _) ->
                  zipWith (toCon wrapP ns (dt, map tyVarBndrToName vs)
                    (length cs)) [1..] cs
                TyConI (NewtypeD _ dt vs _ c _) ->
                  [toCon wrapP ns (dt, map tyVarBndrToName vs) 1 0 c]
                TyConI (TySynD t _ _) -> error "type synonym?"
                  -- [clause [wrapP $ conP 'K1 [varP (field 0)]] (normalB $ varE (field 0)) []]
                _ -> error "unknown construct"
      return b

fromCon :: (Q Exp -> Q Exp) -> Name -> (Name, [Name]) -> Int -> Int -> Con -> Q Clause
-- Contexts are ignored
fromCon wrap ns d m i (ForallC _ _ c) = fromCon wrap ns d m i c
fromCon wrap ns (dt, vs) m i (NormalC cn []) =
  clause
    [conP cn []]
    (normalB $ wrap $ lrE m i $ appE (conE 'C) $ conE 'U) []
fromCon wrap ns (dt, vs) m i (NormalC cn fs) =
  -- runIO (putStrLn ("constructor " ++ show ix)) >>
  clause
    [conP cn (map (varP . field) [0..length fs - 1])]
    (normalB $ wrap $ lrE m i $ conE 'C `appE`
      foldBal prod (zipWith (fromField (dt, vs)) [0..] (map snd fs))) []
  where prod x y = conE '(:*:) `appE` x `appE` y
fromCon wrap ns (dt, vs) m i r@(RecC cn []) =
  clause
    [conP cn []]
    (normalB $ wrap $ lrE m i $ conE 'C `appE` conE 'U) []
fromCon wrap ns (dt, vs) m i r@(RecC cn fs) =
  clause
    [conP cn (map (varP . field) [0..length fs - 1])]
    (normalB $ wrap $ lrE m i $ conE 'C `appE`
      foldBal prod (zipWith (fromField (dt, vs)) [0..] (map trd fs))) []
  where prod x y = conE '(:*:) `appE` x `appE` y
fromCon wrap ns (dt, vs) m i (InfixC t1 cn t2) =
  fromCon wrap ns (dt, vs) m i (NormalC cn [t1,t2])
-- En fromCon (para GadtC)
fromCon wrap ns (dt, vs) m i (GadtC [cn] fieldTypes _) =
  clause
    [conP cn (map (varP . field) [0..length fieldTypes - 1])]
    (normalB $ wrap $ lrE m i $ 
        conE 'C `appE` 
        foldBal prod (zipWith (fromField (dt, vs)) [0..] (map snd fieldTypes)))
    []
  where prod x y = conE '(:*:) `appE` x `appE` y

fromField :: (Name, [Name]) -> Int -> Type -> Q Exp
--fromField (dt, vs) nr t | t == dataDeclToType (dt, vs) = conE 'I `appE` varE (field nr)
fromField (dt, vs) nr t = conE 'Rec `appE` varE (field nr)

toCon :: (Q Pat -> Q Pat) -> Name -> (Name, [Name]) -> Int -> Int -> Con -> Q Clause
toCon wrap ns d m i (ForallC _ _ c) = toCon wrap ns d m i c
toCon wrap ns (dt, vs) m i (NormalC cn []) =
    clause
      [wrap $ lrP m i $ conP 'C [conP 'U []]]
      (normalB $ conE cn) []
toCon wrap ns (dt, vs) m i (NormalC cn fs) =
    -- runIO (putStrLn ("constructor " ++ show ix)) >>
    clause
      [wrap $ lrP m i $ conP 'C
        [foldBal prod (zipWith (toField (dt, vs)) [0..] (map snd fs))]]
      (normalB $ foldl appE (conE cn) (map (varE . field) [0..length fs - 1])) []
  where prod x y = conP '(:*:) [x,y]
toCon wrap ns (dt, vs) m i r@(RecC cn []) =
    clause
      [wrap $ lrP m i $ conP 'U []]
      (normalB $ conE cn) []
toCon wrap ns (dt, vs) m i r@(RecC cn fs) =
    clause
      [wrap $ lrP m i $ conP 'C
        [foldBal prod (zipWith (toField (dt, vs)) [0..] (map trd fs))]]
      (normalB $ foldl appE (conE cn) (map (varE . field) [0..length fs - 1])) []
  where prod x y = conP '(:*:) [x,y]
toCon wrap ns (dt, vs) m i (InfixC t1 cn t2) =
    toCon wrap ns (dt, vs) m i (NormalC cn [t1,t2])
toCon wrap ns (dt, vs) m i (GadtC [cn] fieldTypes _) =
    clause
      [wrap $ lrP m i $ conP 'C
        [foldBal prod (zipWith (toField (dt, vs)) [0..] (map snd fieldTypes))]]
      (normalB $ foldl appE (conE cn) (map (varE . field) [0..length fieldTypes - 1]))[]
  where prod x y = conP '(:*:) [x,y]

toField :: (Name, [Name]) -> Int -> Type -> Q Pat
--toField (dt, vs) nr t | t == dataDeclToType (dt, vs) = conP 'I [varP (field nr)]
toField (dt, vs) nr t = conP 'Rec [varP (field nr)]


field :: Int -> Name
field n = mkName $ "f" ++ show n

lrP :: Int -> Int -> (Q Pat -> Q Pat)
{-
lrP 1 0 p = p
lrP m 0 p = conP 'L [p]
lrP m i p = conP 'R [lrP (m-1) (i-1) p]
-}
lrP m i p | m == 0       = error "1"
          | m == 1       = p
          | i <= div m 2 = conP 'L [lrP (div m 2)     i             p]
          | i >  div m 2 = conP 'R [lrP (m - div m 2) (i - div m 2) p]

lrE :: Int -> Int -> (Q Exp -> Q Exp)
{-
lrE 1 0 e = e
lrE m 0 e = conE 'L `appE` e
lrE m i e = conE 'R `appE` lrE (m-1) (i-1) e
-}
lrE m i e | m == 0       = error "2"
          | m == 1       = e
          | i <= div m 2 = conE 'L `appE` lrE (div m 2)     i         e
          | i >  div m 2 = conE 'R `appE` lrE (m - div m 2) (i - div m 2) e

trd (_,_,c) = c

-- | Variant of foldr1 which returns a special element for empty lists
foldr1' f x [] = x
foldr1' _ _ [x] = x
foldr1' f x (h:t) = f h (foldr1' f x t)

-- | Variant of foldr1 for producing balanced lists
foldBal :: (a -> a -> a) -> [a] -> a
foldBal op = foldBal' op (error "foldBal: empty list")

foldBal' :: (a -> a -> a) -> a -> [a] -> a
foldBal' _  x []  = x
foldBal' _  _ [y] = y
foldBal' op x l   = let (a,b) = splitAt (length l `div` 2) l
                    in foldBal' op x a `op` foldBal' op x b


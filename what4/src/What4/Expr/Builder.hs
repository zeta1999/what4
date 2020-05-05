{-|
Module      : What4.Expr.Builder
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

This module defines the canonical implementation of the solver interface
from "What4.Interface". Type @'ExprBuilder' t st@ is
an instance of the classes 'IsExprBuilder' and 'IsSymExprBuilder'.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.Builder
  ( -- * ExprBuilder
    ExprBuilder
  , newExprBuilder
  , getSymbolVarBimap
  , sbMakeExpr
  , sbNonceExpr
  , curProgramLoc
  , sbUnaryThreshold
  , sbCacheStartSize
  , sbBVDomainRangeLimit
  , sbStateManager
  , exprCounter
  , startCaching
  , stopCaching

    -- * Specialized representations
  , bvUnary
  , natSum
  , intSum
  , realSum
  , bvSum
  , scalarMul

    -- * configuration options
  , unaryThresholdOption
  , bvdomainRangeLimitOption
  , cacheStartSizeOption
  , cacheTerms

    -- * Expr
  , Expr(..)
  , asApp
  , asNonceApp
  , iteSize
  , exprLoc
  , ppExpr
  , ppExprTop
  , exprMaybeId
  , asConjunction
  , asDisjunction
  , Polarity(..)
  , BM.negatePolarity
    -- ** AppExpr
  , AppExpr
  , appExprId
  , appExprLoc
  , appExprApp
    -- ** NonceAppExpr
  , NonceAppExpr
  , nonceExprId
  , nonceExprLoc
  , nonceExprApp
    -- ** Type abbreviations
  , BoolExpr
  , NatExpr
  , IntegerExpr
  , RealExpr
  , BVExpr
  , CplxExpr
  , StringExpr

    -- * App
  , App(..)
  , traverseApp
  , appType
    -- * NonceApp
  , NonceApp(..)
  , nonceAppType

    -- * Bound Variable information
  , ExprBoundVar
  , bvarId
  , bvarLoc
  , bvarName
  , bvarType
  , bvarKind
  , bvarAbstractValue
  , VarKind(..)
  , boundVars
  , ppBoundVar
  , evalBoundVars

    -- * Symbolic Function
  , ExprSymFn(..)
  , SymFnInfo(..)
  , symFnArgTypes
  , symFnReturnType

    -- * SymbolVarBimap
  , SymbolVarBimap
  , SymbolBinding(..)
  , emptySymbolVarBimap
  , lookupBindingOfSymbol
  , lookupSymbolOfBinding

    -- * IdxCache
  , IdxCache
  , newIdxCache
  , lookupIdx
  , lookupIdxValue
  , insertIdxValue
  , deleteIdxValue
  , clearIdxCache
  , idxCacheEval
  , idxCacheEval'

    -- * BV Or Set
  , BVOrSet
  , bvOrToList
  , bvOrSingleton
  , bvOrInsert
  , bvOrUnion
  , bvOrAbs
  , traverseBVOrSet

    -- * Re-exports
  , SymExpr
  , What4.Interface.bvWidth
  , What4.Interface.exprType
  , What4.Interface.IndexLit(..)
  , What4.Interface.ArrayResultWrapper(..)
  ) where

import qualified Control.Exception as Ex
import           Control.Lens hiding (asIndex, (:>), Empty)
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.Trans.Writer.Strict (writer, runWriter)
import           Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import qualified Data.Bits as Bits
import           Data.Foldable
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Basic as H
import           Data.Hashable
import           Data.IORef
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Monoid (Any(..))
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.HashTable as PH
import qualified Data.Parameterized.Map as PM
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio (numerator, denominator)
import           Data.STRef
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word (Word64)
import           GHC.Generics (Generic)
import qualified Numeric as N
import           Numeric.Natural
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.BaseTypes
import           What4.Concrete
import qualified What4.Config as CFG
import           What4.Interface
import           What4.ProgramLoc
import qualified What4.SemiRing as SR
import           What4.Symbol
import           What4.Expr.App
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.Expr.BoolMap (BoolMap, Polarity(..), BoolMapView(..))
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.MATLAB
import           What4.Expr.WeightedSum (WeightedSum, SemiRingProduct)
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.StringSeq as SSeq
import           What4.Expr.UnaryBV (UnaryBV)
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import           What4.Utils.StringLiteral

------------------------------------------------------------------------
-- Utilities

toDouble :: Rational -> Double
toDouble = fromRational

cachedEval :: (HashableF k, TestEquality k)
           => PH.HashTable RealWorld k a
           -> k tp
           -> IO (a tp)
           -> IO (a tp)
cachedEval tbl k action = do
  mr <- stToIO $ PH.lookup tbl k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- action
      seq r $ do
      stToIO $ PH.insert tbl k r
      return r



-- | This type represents 'Expr' values that were built from a
-- 'NonceApp'.
--
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Selector functions are provided to destruct 'NonceAppExpr' values,
-- but the constructor is kept hidden. The preferred way to construct
-- an 'Expr' from a 'NonceApp' is to use 'sbNonceExpr'.
data NonceAppExpr t (tp :: BaseType)
   = NonceAppExprCtor { nonceExprId  :: {-# UNPACK #-} !(Nonce t tp)
                     , nonceExprLoc :: !ProgramLoc
                     , nonceExprApp :: !(NonceApp t (Expr t) tp)
                     , nonceExprAbsValue :: !(AbstractValue tp)
                     }

-- | This type represents 'Expr' values that were built from an 'App'.
--
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Selector functions are provided to destruct 'AppExpr' values, but
-- the constructor is kept hidden. The preferred way to construct an
-- 'Expr' from an 'App' is to use 'sbMakeExpr'.
data AppExpr t (tp :: BaseType)
   = AppExprCtor { appExprId  :: {-# UNPACK #-} !(Nonce t tp)
                , appExprLoc :: !ProgramLoc
                , appExprApp :: !(App (Expr t) tp)
                , appExprAbsValue :: !(AbstractValue tp)
                }

------------------------------------------------------------------------
-- Expr

-- | The main ExprBuilder expression datastructure.  The non-trivial @Expr@
-- values constructed by this module are uniquely identified by a
-- nonce value that is used to explicitly represent sub-term sharing.
-- When traversing the structure of an @Expr@ it is usually very important
-- to memoize computations based on the values of these identifiers to avoid
-- exponential blowups due to shared term structure.
--
-- Type parameter @t@ is a phantom type brand used to relate nonces to
-- a specific nonce generator (similar to the @s@ parameter of the
-- @ST@ monad). The type index @tp@ of kind 'BaseType' indicates the
-- type of the values denoted by the given expression.
--
-- Type @'Expr' t@ instantiates the type family @'SymExpr'
-- ('ExprBuilder' t st)@.
data Expr t (tp :: BaseType) where
  SemiRingLiteral :: !(SR.SemiRingRepr sr) -> !(SR.Coefficient sr) -> !ProgramLoc -> Expr t (SR.SemiRingBase sr)
  BoolExpr :: !Bool -> !ProgramLoc -> Expr t BaseBoolType
  StringExpr :: !(StringLiteral si) -> !ProgramLoc -> Expr t (BaseStringType si)
  -- Application
  AppExpr :: {-# UNPACK #-} !(AppExpr t tp) -> Expr t tp
  -- An atomic predicate
  NonceAppExpr :: {-# UNPACK #-} !(NonceAppExpr t tp) -> Expr t tp
  -- A bound variable
  BoundVarExpr :: !(ExprBoundVar t tp) -> Expr t tp

-- | Destructor for the 'AppExpr' constructor.
{-# INLINE asApp #-}
asApp :: Expr t tp -> Maybe (App (Expr t) tp)
asApp (AppExpr a) = Just (appExprApp a)
asApp _ = Nothing

-- | Destructor for the 'NonceAppExpr' constructor.
{-# INLINE asNonceApp #-}
asNonceApp :: Expr t tp -> Maybe (NonceApp t (Expr t) tp)
asNonceApp (NonceAppExpr a) = Just (nonceExprApp a)
asNonceApp _ = Nothing

exprLoc :: Expr t tp -> ProgramLoc
exprLoc (SemiRingLiteral _ _ l) = l
exprLoc (BoolExpr _ l) = l
exprLoc (StringExpr _ l) = l
exprLoc (NonceAppExpr a)  = nonceExprLoc a
exprLoc (AppExpr a)   = appExprLoc a
exprLoc (BoundVarExpr v) = bvarLoc v

mkExpr :: Nonce t tp
      -> ProgramLoc
      -> App (Expr t) tp
      -> AbstractValue tp
      -> Expr t tp
mkExpr n l a v = AppExpr $ AppExprCtor { appExprId  = n
                                    , appExprLoc = l
                                    , appExprApp = a
                                    , appExprAbsValue = v
                                    }

type BoolExpr t = Expr t BaseBoolType
type NatExpr  t = Expr t BaseNatType
type BVExpr t n = Expr t (BaseBVType n)
type IntegerExpr t = Expr t BaseIntegerType
type RealExpr t = Expr t BaseRealType
type CplxExpr t = Expr t BaseComplexType
type StringExpr t si = Expr t (BaseStringType si)



iteSize :: Expr t tp -> Integer
iteSize e =
  case asApp e of
    Just (BaseIte _ sz _ _ _) -> sz
    _ -> 0

instance IsExpr (Expr t) where
  asConstantPred = exprAbsValue

  asNat (SemiRingLiteral SR.SemiRingNatRepr n _) = Just n
  asNat _ = Nothing

  natBounds x = exprAbsValue x

  asInteger (SemiRingLiteral SR.SemiRingIntegerRepr n _) = Just n
  asInteger _ = Nothing

  integerBounds x = exprAbsValue x

  asRational (SemiRingLiteral SR.SemiRingRealRepr r _) = Just r
  asRational _ = Nothing

  rationalBounds x = ravRange $ exprAbsValue x

  asComplex e
    | Just (Cplx c) <- asApp e = traverse asRational c
    | otherwise = Nothing

  exprType (SemiRingLiteral sr _ _) = SR.semiRingBase sr
  exprType (BoolExpr _ _) = BaseBoolRepr
  exprType (StringExpr s _) = BaseStringRepr (stringLiteralInfo s)
  exprType (NonceAppExpr e)  = nonceAppType (nonceExprApp e)
  exprType (AppExpr e) = appType (appExprApp e)
  exprType (BoundVarExpr i) = bvarType i

  asUnsignedBV (SemiRingLiteral (SR.SemiRingBVRepr _ _) i _) = Just i
  asUnsignedBV _ = Nothing

  asSignedBV x = toSigned (bvWidth x) <$> asUnsignedBV x

  unsignedBVBounds x = Just $ BVD.ubounds $ exprAbsValue x
  signedBVBounds x = Just $ BVD.sbounds (bvWidth x) $ exprAbsValue x

  asAffineVar e = case exprType e of
    BaseNatRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingNatRepr e ->
        Just (ConcreteNat a, x, ConcreteNat b)
    BaseIntegerRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingIntegerRepr e ->
        Just (ConcreteInteger a, x, ConcreteInteger b)
    BaseRealRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingRealRepr e ->
        Just (ConcreteReal a, x, ConcreteReal b)
    BaseBVRepr w
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e)) e ->
        Just (ConcreteBV w a, x, ConcreteBV w b)
    _ -> Nothing

  asString (StringExpr x _) = Just x
  asString _ = Nothing

  asConstantArray (asApp -> Just (ConstantArray _ _ def)) = Just def
  asConstantArray _ = Nothing

  asStruct (asApp -> Just (StructCtor _ flds)) = Just flds
  asStruct _ = Nothing

  printSymExpr = pretty


asSemiRingLit :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (SR.Coefficient sr)
asSemiRingLit sr (SemiRingLiteral sr' x _loc)
  | Just Refl <- testEquality sr sr'
  = Just x

  -- special case, ignore the BV ring flavor for this purpose
  | SR.SemiRingBVRepr _ w  <- sr
  , SR.SemiRingBVRepr _ w' <- sr'
  , Just Refl <- testEquality w w'
  = Just x

asSemiRingLit _ _ = Nothing

asSemiRingSum :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (WeightedSum (Expr t) sr)
asSemiRingSum sr (asSemiRingLit sr -> Just x) = Just (WSum.constant sr x)
asSemiRingSum sr (asApp -> Just (SemiRingSum x))
   | Just Refl <- testEquality sr (WSum.sumRepr x) = Just x
asSemiRingSum _ _ = Nothing

asSemiRingProd :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (SemiRingProduct (Expr t) sr)
asSemiRingProd sr (asApp -> Just (SemiRingProd x))
  | Just Refl <- testEquality sr (WSum.prodRepr x) = Just x
asSemiRingProd _ _ = Nothing

-- | This privides a view of a semiring expr as a weighted sum of values.
data SemiRingView t sr
   = SR_Constant !(SR.Coefficient sr)
   | SR_Sum  !(WeightedSum (Expr t) sr)
   | SR_Prod !(SemiRingProduct (Expr t) sr)
   | SR_General

viewSemiRing:: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> SemiRingView t sr
viewSemiRing sr x
  | Just r <- asSemiRingLit sr x  = SR_Constant r
  | Just s <- asSemiRingSum sr x  = SR_Sum s
  | Just p <- asSemiRingProd sr x = SR_Prod p
  | otherwise = SR_General

asWeightedSum :: HashableF (Expr t) => SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> WeightedSum (Expr t) sr
asWeightedSum sr x
  | Just r <- asSemiRingLit sr x = WSum.constant sr r
  | Just s <- asSemiRingSum sr x = s
  | otherwise = WSum.var sr x


asConjunction :: Expr t BaseBoolType -> [(Expr t BaseBoolType, Polarity)]
asConjunction (BoolExpr True _) = []
asConjunction (asApp -> Just (ConjPred xs)) =
 case BM.viewBoolMap xs of
   BoolMapUnit     -> []
   BoolMapDualUnit -> [(BoolExpr False initializationLoc, Positive)]
   BoolMapTerms (tm:|tms) -> tm:tms
asConjunction x = [(x,Positive)]


asDisjunction :: Expr t BaseBoolType -> [(Expr t BaseBoolType, Polarity)]
asDisjunction (BoolExpr False _) = []
asDisjunction (asApp -> Just (NotPred (asApp -> Just (ConjPred xs)))) =
 case BM.viewBoolMap xs of
   BoolMapUnit     -> []
   BoolMapDualUnit -> [(BoolExpr True initializationLoc, Positive)]
   BoolMapTerms (tm:|tms) -> map (over _2 BM.negatePolarity) (tm:tms)
asDisjunction x = [(x,Positive)]

asPosAtom :: Expr t BaseBoolType -> (Expr t BaseBoolType, Polarity)
asPosAtom (asApp -> Just (NotPred x)) = (x, Negative)
asPosAtom x                           = (x, Positive)

asNegAtom :: Expr t BaseBoolType -> (Expr t BaseBoolType, Polarity)
asNegAtom (asApp -> Just (NotPred x)) = (x, Positive)
asNegAtom x                           = (x, Negative)


------------------------------------------------------------------------
-- SymbolVarBimap

-- | A bijective map between vars and their canonical name for printing
-- purposes.
-- Parameter @t@ is a phantom type brand used to track nonces.
newtype SymbolVarBimap t = SymbolVarBimap (Bimap SolverSymbol (SymbolBinding t))

-- | This describes what a given SolverSymbol is associated with.
-- Parameter @t@ is a phantom type brand used to track nonces.
data SymbolBinding t
   = forall tp . VarSymbolBinding !(ExprBoundVar t tp)
     -- ^ Solver
   | forall args ret . FnSymbolBinding  !(ExprSymFn t (Expr t) args ret)

instance Eq (SymbolBinding t) where
  VarSymbolBinding x == VarSymbolBinding y = isJust (testEquality x y)
  FnSymbolBinding  x == FnSymbolBinding  y = isJust (testEquality (symFnId x) (symFnId y))
  _ == _ = False

instance Ord (SymbolBinding t) where
  compare (VarSymbolBinding x) (VarSymbolBinding y) =
    toOrdering (compareF x y)
  compare VarSymbolBinding{} _ = LT
  compare _ VarSymbolBinding{} = GT
  compare (FnSymbolBinding  x) (FnSymbolBinding  y) =
    toOrdering (compareF (symFnId x) (symFnId y))

-- | Empty symbol var bimap
emptySymbolVarBimap :: SymbolVarBimap t
emptySymbolVarBimap = SymbolVarBimap Bimap.empty

lookupBindingOfSymbol :: SolverSymbol -> SymbolVarBimap t -> Maybe (SymbolBinding t)
lookupBindingOfSymbol s (SymbolVarBimap m) = Bimap.lookup s m

lookupSymbolOfBinding :: SymbolBinding t -> SymbolVarBimap t -> Maybe SolverSymbol
lookupSymbolOfBinding b (SymbolVarBimap m) = Bimap.lookupR b m

------------------------------------------------------------------------
-- MatlabSolverFn

-- Parameter @t@ is a phantom type brand used to track nonces.
data MatlabFnWrapper t c where
   MatlabFnWrapper :: !(MatlabSolverFn (Expr t) a r) -> MatlabFnWrapper t (a::> r)

instance TestEquality (MatlabFnWrapper t) where
  testEquality (MatlabFnWrapper f) (MatlabFnWrapper g) = do
    Refl <- testSolverFnEq f g
    return Refl


instance HashableF (MatlabFnWrapper t) where
  hashWithSaltF s (MatlabFnWrapper f) = hashWithSalt s f

data ExprSymFnWrapper t c
   = forall a r . (c ~ (a ::> r)) => ExprSymFnWrapper (ExprSymFn t (Expr t) a r)

data SomeSymFn sym = forall args ret . SomeSymFn (SymFn sym args ret)

------------------------------------------------------------------------
-- ExprBuilder

-- | Cache for storing dag terms.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprBuilder t (st :: Type -> Type)
   = SB { sbTrue  :: !(BoolExpr t)
        , sbFalse :: !(BoolExpr t)
          -- | Constant zero.
        , sbZero  :: !(RealExpr t)
          -- | Configuration object for this symbolic backend
        , sbConfiguration :: !CFG.Config
          -- | Flag used to tell the backend whether to evaluate
          -- ground rational values as double precision floats when
          -- a function cannot be evaluated as a rational.
        , sbFloatReduce :: !Bool
          -- | The maximum number of distinct values a term may have and use the
          -- unary representation.
        , sbUnaryThreshold :: !(CFG.OptionSetting BaseIntegerType)
          -- | The maximum number of distinct ranges in a BVDomain expression.
        , sbBVDomainRangeLimit :: !(CFG.OptionSetting BaseIntegerType)
          -- | The starting size when building a new cache
        , sbCacheStartSize :: !(CFG.OptionSetting BaseIntegerType)
          -- | Counter to generate new unique identifiers for elements and functions.
        , exprCounter :: !(NonceGenerator IO t)
          -- | Reference to current allocator for expressions.
        , curAllocator :: !(IORef (ExprAllocator t))
          -- | Number of times an 'Expr' for a non-linear operation has been
          -- created.
        , sbNonLinearOps :: !(IORef Integer)
          -- | The current program location
        , sbProgramLoc :: !(IORef ProgramLoc)
          -- | Additional state maintained by the state manager
        , sbStateManager :: !(IORef (st t))

        , sbVarBindings :: !(IORef (SymbolVarBimap t))
        , sbUninterpFnCache :: !(IORef (Map (SolverSymbol, Some (Ctx.Assignment BaseTypeRepr)) (SomeSymFn (ExprBuilder t st))))
          -- | Cache for Matlab functions
        , sbMatlabFnCache
          :: !(PH.HashTable RealWorld (MatlabFnWrapper t) (ExprSymFnWrapper t))
        , sbSolverLogger
          :: !(IORef (Maybe (SolverEvent -> IO ())))
        }

type instance SymFn (ExprBuilder t st) = ExprSymFn t (Expr t)
type instance SymExpr (ExprBuilder t st) = Expr t
type instance BoundVar (ExprBuilder t st) = ExprBoundVar t
type instance SymAnnotation (ExprBuilder t st) = Nonce t


-- | Get abstract value associated with element.
exprAbsValue :: Expr t tp -> AbstractValue tp
exprAbsValue (SemiRingLiteral sr x _) =
  case sr of
    SR.SemiRingNatRepr  -> natSingleRange x
    SR.SemiRingIntegerRepr  -> singleRange x
    SR.SemiRingRealRepr -> ravSingle x
    SR.SemiRingBVRepr _ w -> BVD.singleton w x

exprAbsValue (StringExpr l _) = stringAbsSingle l
exprAbsValue (BoolExpr b _)   = Just b
exprAbsValue (NonceAppExpr e) = nonceExprAbsValue e
exprAbsValue (AppExpr e)      = appExprAbsValue e
exprAbsValue (BoundVarExpr v) =
  fromMaybe (unconstrainedAbsValue (bvarType v)) (bvarAbstractValue v)

instance HasAbsValue (Expr t) where
  getAbsValue = exprAbsValue

------------------------------------------------------------------------

------------------------------------------------------------------------
-- ExprAllocator

-- | ExprAllocator provides an interface for creating expressions from
-- an applications.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprAllocator t
   = ExprAllocator { appExpr  :: forall tp
                            .  ProgramLoc
                            -> App (Expr t) tp
                            -> AbstractValue tp
                            -> IO (Expr t tp)
                  , nonceExpr :: forall tp
                             .  ProgramLoc
                             -> NonceApp t (Expr t) tp
                             -> AbstractValue tp
                             -> IO (Expr t tp)
                  }


------------------------------------------------------------------------
-- Expr operations

{-# INLINE compareExpr #-}
compareExpr :: Expr t x -> Expr t y -> OrderingF x y

-- Special case, ignore the BV semiring flavor for this purpose
compareExpr (SemiRingLiteral (SR.SemiRingBVRepr _ wx) x _) (SemiRingLiteral (SR.SemiRingBVRepr _ wy) y _) =
  case compareF wx wy of
    LTF -> LTF
    EQF -> fromOrdering (compare x y)
    GTF -> GTF
compareExpr (SemiRingLiteral srx x _) (SemiRingLiteral sry y _) =
  case compareF srx sry of
    LTF -> LTF
    EQF -> fromOrdering (SR.sr_compare srx x y)
    GTF -> GTF
compareExpr SemiRingLiteral{} _ = LTF
compareExpr _ SemiRingLiteral{} = GTF

compareExpr (StringExpr x _) (StringExpr y _) =
  case compareF x y of
    LTF -> LTF
    EQF -> EQF
    GTF -> GTF

compareExpr StringExpr{} _ = LTF
compareExpr _ StringExpr{} = GTF

compareExpr (BoolExpr x _) (BoolExpr y _) = fromOrdering (compare x y)
compareExpr BoolExpr{} _ = LTF
compareExpr _ BoolExpr{} = GTF

compareExpr (NonceAppExpr x) (NonceAppExpr y) = compareF x y
compareExpr NonceAppExpr{} _ = LTF
compareExpr _ NonceAppExpr{} = GTF

compareExpr (AppExpr x) (AppExpr y) = compareF (appExprId x) (appExprId y)
compareExpr AppExpr{} _ = LTF
compareExpr _ AppExpr{} = GTF

compareExpr (BoundVarExpr x) (BoundVarExpr y) = compareF x y

instance TestEquality (NonceAppExpr t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (NonceAppExpr t)  where
  compareF x y = compareF (nonceExprId x) (nonceExprId y)

instance Eq (NonceAppExpr t tp) where
  x == y = isJust (testEquality x y)

instance Ord (NonceAppExpr t tp) where
  compare x y = toOrdering (compareF x y)

instance TestEquality (Expr t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (Expr t)  where
  compareF = compareExpr

instance Eq (Expr t tp) where
  x == y = isJust (testEquality x y)

instance Ord (Expr t tp) where
  compare x y = toOrdering (compareF x y)

instance Hashable (Expr t tp) where
  hashWithSalt s (BoolExpr b _) = hashWithSalt (hashWithSalt s (0::Int)) b
  hashWithSalt s (SemiRingLiteral sr x _) =
    case sr of
      SR.SemiRingNatRepr     -> hashWithSalt (hashWithSalt s (1::Int)) x
      SR.SemiRingIntegerRepr -> hashWithSalt (hashWithSalt s (2::Int)) x
      SR.SemiRingRealRepr    -> hashWithSalt (hashWithSalt s (3::Int)) x
      SR.SemiRingBVRepr _ w  -> hashWithSalt (hashWithSaltF (hashWithSalt s (4::Int)) w) x

  hashWithSalt s (StringExpr x _) = hashWithSalt (hashWithSalt s (5::Int)) x
  hashWithSalt s (AppExpr x)      = hashWithSalt (hashWithSalt s (6::Int)) (appExprId x)
  hashWithSalt s (NonceAppExpr x) = hashWithSalt (hashWithSalt s (7::Int)) (nonceExprId x)
  hashWithSalt s (BoundVarExpr x) = hashWithSalt (hashWithSalt s (8::Int)) x

instance PH.HashableF (Expr t) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- PPIndex

data PPIndex
   = ExprPPIndex {-# UNPACK #-} !Word64
   | RatPPIndex !Rational
  deriving (Eq, Ord, Generic)

instance Hashable PPIndex

------------------------------------------------------------------------
-- countOccurrences

countOccurrences :: Expr t tp -> Map.Map PPIndex Int
countOccurrences e0 = runST $ do
  visited <- H.new
  countOccurrences' visited e0
  Map.fromList <$> H.toList visited

type OccurrenceTable s = H.HashTable s PPIndex Int


incOccurrence :: OccurrenceTable s -> PPIndex -> ST s () -> ST s ()
incOccurrence visited idx sub = do
  mv <- H.lookup visited idx
  case mv of
    Just i -> H.insert visited idx $! i+1
    Nothing -> sub >> H.insert visited idx 1

-- FIXME... why does this ignore Nat and Int literals?
countOccurrences' :: forall t tp s . OccurrenceTable s -> Expr t tp -> ST s ()
countOccurrences' visited (SemiRingLiteral SR.SemiRingRealRepr r _) = do
  incOccurrence visited (RatPPIndex r) $
    return ()
countOccurrences' visited (AppExpr e) = do
  let idx = ExprPPIndex (indexValue (appExprId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (appExprApp e)
countOccurrences' visited (NonceAppExpr e) = do
  let idx = ExprPPIndex (indexValue (nonceExprId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (nonceExprApp e)
countOccurrences' _ _ = return ()

------------------------------------------------------------------------
-- boundVars

type BoundVarMap s t = H.HashTable s PPIndex (Set (Some (ExprBoundVar t)))

cache :: (Eq k, Hashable k) => H.HashTable s k r -> k -> ST s r -> ST s r
cache h k m = do
  mr <- H.lookup h k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      H.insert h k r
      return r


boundVars :: Expr t tp -> ST s (BoundVarMap s t)
boundVars e0 = do
  visited <- H.new
  _ <- boundVars' visited e0
  return visited

boundVars' :: BoundVarMap s t
           -> Expr t tp
           -> ST s (Set (Some (ExprBoundVar t)))
boundVars' visited (AppExpr e) = do
  let idx = indexValue (appExprId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (appExprApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (NonceAppExpr e) = do
  let idx = indexValue (nonceExprId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (nonceExprApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (BoundVarExpr v)
  | QuantifierVarKind <- bvarKind v = do
      let idx = indexValue (bvarId v)
      cache visited (ExprPPIndex idx) $
        return (Set.singleton (Some v))
boundVars' _ _ = return Set.empty

------------------------------------------------------------------------
-- Pretty printing

instance Show (Expr t tp) where
  show = show . ppExpr

instance Pretty (Expr t tp) where
  pretty = ppExpr


-- | @AppPPExpr@ represents a an application, and it may be let bound.
data AppPPExpr
   = APE { apeIndex :: !PPIndex
         , apeLoc :: !ProgramLoc
         , apeName :: !Text
         , apeExprs :: ![PPExpr]
         , apeLength :: !Int
           -- ^ Length of AppPPExpr not including parenthesis.
         }

data PPExpr
   = FixedPPExpr !Doc ![Doc] !Int
     -- ^ A fixed doc with length.
   | AppPPExpr !AppPPExpr
     -- ^ A doc that can be let bound.

-- | Pretty print a AppPPExpr
apeDoc :: AppPPExpr -> (Doc, [Doc])
apeDoc a = (text (Text.unpack (apeName a)), ppExprDoc True <$> apeExprs a)

textPPExpr :: Text -> PPExpr
textPPExpr t = FixedPPExpr (text (Text.unpack t)) [] (Text.length t)

stringPPExpr :: String -> PPExpr
stringPPExpr t = FixedPPExpr (text t) [] (length t)

-- | Get length of Expr including parens.
ppExprLength :: PPExpr -> Int
ppExprLength (FixedPPExpr _ [] n) = n
ppExprLength (FixedPPExpr _ _ n) = n + 2
ppExprLength (AppPPExpr a) = apeLength a + 2

parenIf :: Bool -> Doc -> [Doc] -> Doc
parenIf _ h [] = h
parenIf False h l = hsep (h:l)
parenIf True h l = parens (hsep (h:l))

-- | Pretty print PPExpr
ppExprDoc :: Bool -> PPExpr -> Doc
ppExprDoc b (FixedPPExpr d a _) = parenIf b d a
ppExprDoc b (AppPPExpr a) = uncurry (parenIf b) (apeDoc a)

data PPExprOpts = PPExprOpts { ppExpr_maxWidth :: Int
                           , ppExpr_useDecimal :: Bool
                           }

defaultPPExprOpts :: PPExprOpts
defaultPPExprOpts =
  PPExprOpts { ppExpr_maxWidth = 68
            , ppExpr_useDecimal = True
            }

-- | Pretty print an 'Expr' using let bindings to create the term.
ppExpr :: Expr t tp -> Doc
ppExpr e
     | Prelude.null bindings = ppExprDoc False r
     | otherwise =
         text "let" <+> align (vcat bindings) PP.<$>
         text " in" <+> align (ppExprDoc False r)
  where (bindings,r) = runST (ppExpr' e defaultPPExprOpts)

instance ShowF (Expr t)

-- | Pretty print the top part of an element.
ppExprTop :: Expr t tp -> Doc
ppExprTop e = ppExprDoc False r
  where (_,r) = runST (ppExpr' e defaultPPExprOpts)

-- | Contains the elements before, the index, doc, and width and
-- the elements after.
type SplitPPExprList = Maybe ([PPExpr], AppPPExpr, [PPExpr])

findExprToRemove :: [PPExpr] -> SplitPPExprList
findExprToRemove exprs0 = go [] exprs0 Nothing
  where go :: [PPExpr] -> [PPExpr] -> SplitPPExprList -> SplitPPExprList
        go _ [] mr = mr
        go prev (e@FixedPPExpr{} : exprs) mr = do
          go (e:prev) exprs mr
        go prev (AppPPExpr a:exprs) mr@(Just (_,a',_))
          | apeLength a < apeLength a' = go (AppPPExpr a:prev) exprs mr
        go prev (AppPPExpr a:exprs) _ = do
          go (AppPPExpr a:prev) exprs (Just (reverse prev, a, exprs))


ppExpr' :: forall t tp s . Expr t tp -> PPExprOpts -> ST s ([Doc], PPExpr)
ppExpr' e0 o = do
  let max_width = ppExpr_maxWidth o
  let use_decimal = ppExpr_useDecimal o
  -- Get map that counts number of elements.
  let m = countOccurrences e0
  -- Return number of times a term is referred to in dag.
  let isShared :: PPIndex -> Bool
      isShared w = fromMaybe 0 (Map.lookup w m) > 1

  -- Get bounds variables.
  bvars <- boundVars e0

  bindingsRef <- newSTRef Seq.empty

  visited <- H.new :: ST s (H.HashTable s PPIndex PPExpr)
  visited_fns <- H.new :: ST s (H.HashTable s Word64 Text)

  let -- Add a binding to the list of bindings
      addBinding :: AppPPExpr -> ST s PPExpr
      addBinding a = do
        let idx = apeIndex a
        cnt <- Seq.length <$> readSTRef bindingsRef

        vars <- fromMaybe Set.empty <$> H.lookup bvars idx
        let args :: [String]
            args = viewSome ppBoundVar <$> Set.toList vars

        let nm = case idx of
                   ExprPPIndex e -> "v" ++ show e
                   RatPPIndex _ -> "r" ++ show cnt
        let lhs = parenIf False (text nm) (text <$> args)
        let doc = text "--" <+> pretty (plSourceLoc (apeLoc a)) <$$>
                  lhs <+> text "=" <+> uncurry (parenIf False) (apeDoc a)
        modifySTRef' bindingsRef (Seq.|> doc)
        let len = length nm + sum ((\arg_s -> length arg_s + 1) <$> args)
        let nm_expr = FixedPPExpr (text nm) (map text args) len
        H.insert visited idx $! nm_expr
        return nm_expr

  let fixLength :: Int
                -> [PPExpr]
                -> ST s ([PPExpr], Int)
      fixLength cur_width exprs
        | cur_width > max_width
        , Just (prev_e, a, next_e) <- findExprToRemove exprs = do
          r <- addBinding a
          let exprs' = prev_e ++ [r] ++ next_e
          fixLength (cur_width - apeLength a + ppExprLength r) exprs'
      fixLength cur_width exprs = do
        return $! (exprs, cur_width)

  -- Pretty print an argument.
  let renderArg :: PrettyArg (Expr t) -> ST s PPExpr
      renderArg (PrettyArg e) = getBindings e
      renderArg (PrettyText txt) = return (textPPExpr txt)
      renderArg (PrettyFunc nm args) =
        do exprs0 <- traverse renderArg args
           let total_width = Text.length nm + sum ((\e -> 1 + ppExprLength e) <$> exprs0)
           (exprs1, cur_width) <- fixLength total_width exprs0
           let exprs = map (ppExprDoc True) exprs1
           return (FixedPPExpr (text (Text.unpack nm)) exprs cur_width)

      renderApp :: PPIndex
                -> ProgramLoc
                -> Text
                -> [PrettyArg (Expr t)]
                -> ST s AppPPExpr
      renderApp idx loc nm args = Ex.assert (not (Prelude.null args)) $ do
        exprs0 <- traverse renderArg args
        -- Get width not including parenthesis of outer app.
        let total_width = Text.length nm + sum ((\e -> 1 + ppExprLength e) <$> exprs0)
        (exprs, cur_width) <- fixLength total_width exprs0
        return APE { apeIndex = idx
                   , apeLoc = loc
                   , apeName = nm
                   , apeExprs = exprs
                   , apeLength = cur_width
                   }

      cacheResult :: PPIndex
                  -> ProgramLoc
                  -> PrettyApp (Expr t)
                  -> ST s PPExpr
      cacheResult _ _ (nm,[]) = do
        return (textPPExpr nm)
      cacheResult idx loc (nm,args) = do
        mr <- H.lookup visited idx
        case mr of
          Just d -> return d
          Nothing -> do
            a <- renderApp idx loc nm args
            if isShared idx then
              addBinding a
             else
              return (AppPPExpr a)

      bindFn :: ExprSymFn t (Expr t) idx ret -> ST s (PrettyArg (Expr t))
      bindFn f = do
        let idx = indexValue (symFnId f)
        mr <- H.lookup visited_fns idx
        case mr of
          Just d -> return (PrettyText d)
          Nothing -> do
            case symFnInfo f of
              UninterpFnInfo{} -> do
                let def_doc = text (show f) <+> text "=" <+> text "??"
                modifySTRef' bindingsRef (Seq.|> def_doc)
              DefinedFnInfo vars rhs _ -> do
                let pp_vars = toListFC (text . ppBoundVar) vars
                let def_doc = text (show f) <+> hsep pp_vars <+> text "=" <+> ppExpr rhs
                modifySTRef' bindingsRef (Seq.|> def_doc)
              MatlabSolverFnInfo fn_id _ _ -> do
                let def_doc = text (show f) <+> text "=" <+> ppMatlabSolverFn fn_id
                modifySTRef' bindingsRef (Seq.|> def_doc)

            let d = Text.pack (show f)
            H.insert visited_fns idx $! d
            return $! PrettyText d

      -- Collect definitions for all applications that occur multiple times
      -- in term.
      getBindings :: Expr t u -> ST s PPExpr
      getBindings (SemiRingLiteral sr x l) =
        case sr of
          SR.SemiRingNatRepr ->
            return $ stringPPExpr (show x)
          SR.SemiRingIntegerRepr ->
            return $ stringPPExpr (show x)
          SR.SemiRingRealRepr -> cacheResult (RatPPIndex x) l app
             where n = numerator x
                   d = denominator x
                   app | d == 1      = prettyApp (fromString (show n)) []
                       | use_decimal = prettyApp (fromString (show (fromRational x :: Double))) []
                       | otherwise   = prettyApp "divReal"  [ showPrettyArg n, showPrettyArg d ]
          SR.SemiRingBVRepr _ w ->
            return $ stringPPExpr $ "0x" ++ (N.showHex x []) ++ ":[" ++ show w ++ "]"

      getBindings (StringExpr x _) =
        return $ stringPPExpr $ (show x)
      getBindings (BoolExpr b _) =
        return $ stringPPExpr (if b then "true" else "false")
      getBindings (NonceAppExpr e) =
        cacheResult (ExprPPIndex (indexValue (nonceExprId e))) (nonceExprLoc e)
          =<< ppNonceApp bindFn (nonceExprApp e)
      getBindings (AppExpr e) =
        cacheResult (ExprPPIndex (indexValue (appExprId e)))
                    (appExprLoc e)
                    (ppApp' (appExprApp e))
      getBindings (BoundVarExpr i) =
        return $ stringPPExpr $ ppBoundVar i

  r <- getBindings e0
  bindings <- toList <$> readSTRef bindingsRef
  return (toList bindings, r)


------------------------------------------------------------------------
-- Uncached storage

-- | Create a new storage that does not do hash consing.
newStorage :: NonceGenerator IO t -> IO (ExprAllocator t)
newStorage g = do
  return $! ExprAllocator { appExpr = uncachedExprFn g
                         , nonceExpr = uncachedNonceExpr g
                         }

uncachedExprFn :: NonceGenerator IO t
              -> ProgramLoc
              -> App (Expr t) tp
              -> AbstractValue tp
              -> IO (Expr t tp)
uncachedExprFn g pc a v = do
  n <- freshNonce g
  return $! mkExpr n pc a v

uncachedNonceExpr :: NonceGenerator IO t
                 -> ProgramLoc
                 -> NonceApp t (Expr t) tp
                 -> AbstractValue tp
                 -> IO (Expr t tp)
uncachedNonceExpr g pc p v = do
  n <- freshNonce g
  return $! NonceAppExpr $ NonceAppExprCtor { nonceExprId = n
                                          , nonceExprLoc = pc
                                          , nonceExprApp = p
                                          , nonceExprAbsValue = v
                                          }

------------------------------------------------------------------------
-- Cached storage

cachedNonceExpr :: NonceGenerator IO t
               -> PH.HashTable RealWorld (NonceApp t (Expr t)) (Expr t)
               -> ProgramLoc
               -> NonceApp t (Expr t) tp
               -> AbstractValue tp
               -> IO (Expr t tp)
cachedNonceExpr g h pc p v = do
  me <- stToIO $ PH.lookup h p
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = NonceAppExpr $ NonceAppExprCtor { nonceExprId = n
                                            , nonceExprLoc = pc
                                            , nonceExprApp = p
                                            , nonceExprAbsValue = v
                                            }
      seq e $ stToIO $ PH.insert h p e
      return $! e


cachedAppExpr :: forall t tp
               . NonceGenerator IO t
              -> PH.HashTable RealWorld (App (Expr t)) (Expr t)
              -> ProgramLoc
              -> App (Expr t) tp
              -> AbstractValue tp
              -> IO (Expr t tp)
cachedAppExpr g h pc a v = do
  me <- stToIO $ PH.lookup h a
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = mkExpr n pc a v
      seq e $ stToIO $ PH.insert h a e
      return e

-- | Create a storage that does hash consing.
newCachedStorage :: forall t
                  . NonceGenerator IO t
                 -> Int
                 -> IO (ExprAllocator t)
newCachedStorage g sz = stToIO $ do
  appCache  <- PH.newSized sz
  predCache <- PH.newSized sz
  return $ ExprAllocator { appExpr = cachedAppExpr g appCache
                        , nonceExpr = cachedNonceExpr g predCache
                        }

instance PolyEq (Expr t x) (Expr t y) where
  polyEqF x y = do
    Refl <- testEquality x y
    return Refl


------------------------------------------------------------------------
-- IdxCache

-- | An IdxCache is used to map expressions with type @Expr t tp@ to
-- values with a corresponding type @f tp@. It is a mutable map using
-- an 'IO' hash table. Parameter @t@ is a phantom type brand used to
-- track nonces.
newtype IdxCache t (f :: BaseType -> Type)
      = IdxCache { cMap :: IORef (PM.MapF (Nonce t) f) }

-- | Create a new IdxCache
newIdxCache :: MonadIO m => m (IdxCache t f)
newIdxCache = liftIO $ IdxCache <$> newIORef PM.empty

{-# INLINE lookupIdxValue #-}
-- | Return the value associated to the expr in the index.
lookupIdxValue :: MonadIO m => IdxCache t f -> Expr t tp -> m (Maybe (f tp))
lookupIdxValue _ SemiRingLiteral{} = return Nothing
lookupIdxValue _ StringExpr{} = return Nothing
lookupIdxValue _ BoolExpr{} = return Nothing
lookupIdxValue c (NonceAppExpr e) = lookupIdx c (nonceExprId e)
lookupIdxValue c (AppExpr e)  = lookupIdx c (appExprId e)
lookupIdxValue c (BoundVarExpr i) = lookupIdx c (bvarId i)

{-# INLINE lookupIdx #-}
lookupIdx :: (MonadIO m) => IdxCache t f -> Nonce t tp -> m (Maybe (f tp))
lookupIdx c n = liftIO $ PM.lookup n <$> readIORef (cMap c)

{-# INLINE insertIdxValue #-}
-- | Bind the value to the given expr in the index.
insertIdxValue :: MonadIO m => IdxCache t f -> Nonce t tp -> f tp -> m ()
insertIdxValue c e v = seq v $ liftIO $ modifyIORef (cMap c) $ PM.insert e v

{-# INLINE deleteIdxValue #-}
-- | Remove a value from the IdxCache
deleteIdxValue :: MonadIO m => IdxCache t f -> Nonce t (tp :: BaseType) -> m ()
deleteIdxValue c e = liftIO $ modifyIORef (cMap c) $ PM.delete e

-- | Remove all values from the IdxCache
clearIdxCache :: MonadIO m => IdxCache t f -> m ()
clearIdxCache c = liftIO $ writeIORef (cMap c) PM.empty

exprMaybeId :: Expr t tp -> Maybe (Nonce t tp)
exprMaybeId SemiRingLiteral{} = Nothing
exprMaybeId StringExpr{} = Nothing
exprMaybeId BoolExpr{} = Nothing
exprMaybeId (NonceAppExpr e) = Just $! nonceExprId e
exprMaybeId (AppExpr  e) = Just $! appExprId e
exprMaybeId (BoundVarExpr e) = Just $! bvarId e

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
{-# INLINE idxCacheEval #-}
idxCacheEval :: (MonadIO m)
             => IdxCache t f
             -> Expr t tp
             -> m (f tp)
             -> m (f tp)
idxCacheEval c e m = do
  case exprMaybeId e of
    Nothing -> m
    Just n -> idxCacheEval' c n m

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
{-# INLINE idxCacheEval' #-}
idxCacheEval' :: (MonadIO m)
              => IdxCache t f
              -> Nonce t tp
              -> m (f tp)
              -> m (f tp)
idxCacheEval' c n m = do
  mr <- lookupIdx c n
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      insertIdxValue c n r
      return r

------------------------------------------------------------------------
-- ExprBuilder operations

curProgramLoc :: ExprBuilder t st -> IO ProgramLoc
curProgramLoc sym = readIORef (sbProgramLoc sym)

-- | Create an element from a nonce app.
sbNonceExpr :: ExprBuilder t st
           -> NonceApp t (Expr t) tp
           -> IO (Expr t tp)
sbNonceExpr sym a = do
  s <- readIORef (curAllocator sym)
  pc <- curProgramLoc sym
  nonceExpr s pc a (quantAbsEval exprAbsValue a)

semiRingLit :: ExprBuilder t st
            -> SR.SemiRingRepr sr
            -> SR.Coefficient sr
            -> IO (Expr t (SR.SemiRingBase sr))
semiRingLit sb sr x = do
  l <- curProgramLoc sb
  return $! SemiRingLiteral sr x l

sbMakeExpr :: ExprBuilder t st -> App (Expr t) tp -> IO (Expr t tp)
sbMakeExpr sym a = do
  s <- readIORef (curAllocator sym)
  pc <- curProgramLoc sym
  let v = abstractEval exprAbsValue a
  when (isNonLinearApp a) $
    modifyIORef' (sbNonLinearOps sym) (+1)
  case appType a of
    -- Check if abstract interpretation concludes this is a constant.
    BaseBoolRepr | Just b <- v -> return $ backendPred sym b
    BaseNatRepr  | Just c <- asSingleNatRange v -> natLit sym c
    BaseIntegerRepr | Just c <- asSingleRange v -> intLit sym c
    BaseRealRepr | Just c <- asSingleRange (ravRange v) -> realLit sym c
    BaseBVRepr w | Just x <- BVD.asSingleton v -> bvLit sym w x
    _ -> appExpr s pc a v

-- | Update the binding to point to the current variable.
updateVarBinding :: ExprBuilder t st
                 -> SolverSymbol
                 -> SymbolBinding t
                 -> IO ()
updateVarBinding sym nm v
  | nm == emptySymbol = return ()
  | otherwise =
    modifyIORef' (sbVarBindings sym) $ (ins nm $! v)
  where ins n x (SymbolVarBimap m) = SymbolVarBimap (Bimap.insert n x m)

-- | Creates a new bound var.
sbMakeBoundVar :: ExprBuilder t st
               -> SolverSymbol
               -> BaseTypeRepr tp
               -> VarKind
               -> Maybe (AbstractValue tp)
               -> IO (ExprBoundVar t tp)
sbMakeBoundVar sym nm tp k absVal = do
  n  <- sbFreshIndex sym
  pc <- curProgramLoc sym
  return $! BVar { bvarId   = n
                 , bvarLoc  = pc
                 , bvarName = nm
                 , bvarType = tp
                 , bvarKind = k
                 , bvarAbstractValue = absVal
                 }

-- | Create fresh index
sbFreshIndex :: ExprBuilder t st -> IO (Nonce t (tp::BaseType))
sbFreshIndex sb = freshNonce (exprCounter sb)

sbFreshSymFnNonce :: ExprBuilder t st -> IO (Nonce t (ctx:: Ctx BaseType))
sbFreshSymFnNonce sb = freshNonce (exprCounter sb)

------------------------------------------------------------------------
-- Configuration option for controlling the maximum number of value a unary
-- threshold may have.

-- | Maximum number of values in unary bitvector encoding.
--
--   This option is named \"backend.unary_threshold\"
unaryThresholdOption :: CFG.ConfigOption BaseIntegerType
unaryThresholdOption = CFG.configOption BaseIntegerRepr "backend.unary_threshold"

-- | The configuration option for setting the maximum number of
-- values a unary threshold may have.
unaryThresholdDesc :: CFG.ConfigDesc
unaryThresholdDesc = CFG.mkOpt unaryThresholdOption sty help (Just (ConcreteInteger 0))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just (text "Maximum number of values in unary bitvector encoding.")

------------------------------------------------------------------------
-- Configuration option for controlling how many disjoint ranges
-- should be allowed in bitvector domains.

-- | Maximum number of ranges in bitvector abstract domains.
--
--   This option is named \"backend.bvdomain_range_limit\"
bvdomainRangeLimitOption :: CFG.ConfigOption BaseIntegerType
bvdomainRangeLimitOption = CFG.configOption BaseIntegerRepr "backend.bvdomain_range_limit"

bvdomainRangeLimitDesc :: CFG.ConfigDesc
bvdomainRangeLimitDesc = CFG.mkOpt bvdomainRangeLimitOption sty help (Just (ConcreteInteger 2))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just (text "Maximum number of ranges in bitvector domains.")

------------------------------------------------------------------------
-- Cache start size

-- | Starting size for element cache when caching is enabled.
--
--   This option is named \"backend.cache_start_size\"
cacheStartSizeOption :: CFG.ConfigOption BaseIntegerType
cacheStartSizeOption = CFG.configOption BaseIntegerRepr "backend.cache_start_size"

-- | The configuration option for setting the size of the initial hash set
-- used by simple builder
cacheStartSizeDesc :: CFG.ConfigDesc
cacheStartSizeDesc = CFG.mkOpt cacheStartSizeOption sty help (Just (ConcreteInteger 100000))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just (text "Starting size for element cache")

------------------------------------------------------------------------
-- Cache terms

-- | Indicates if we should cache terms.  When enabled, hash-consing
--   is used to find and deduplicate common subexpressions.
--
--   This option is named \"use_cache\"
cacheTerms :: CFG.ConfigOption BaseBoolType
cacheTerms = CFG.configOption BaseBoolRepr "use_cache"

cacheOptStyle ::
  NonceGenerator IO t ->
  IORef (ExprAllocator t) ->
  CFG.OptionSetting BaseIntegerType ->
  CFG.OptionStyle BaseBoolType
cacheOptStyle gen storageRef szSetting =
  CFG.boolOptSty & CFG.set_opt_onset
        (\mb b -> f (fmap fromConcreteBool mb) (fromConcreteBool b) >> return CFG.optOK)
 where
 f :: Maybe Bool -> Bool -> IO ()
 f mb b | mb /= Just b = if b then start else stop
        | otherwise = return ()

 stop  = do s <- newStorage gen
            writeIORef storageRef s

 start = do sz <- CFG.getOpt szSetting
            s <- newCachedStorage gen (fromInteger sz)
            writeIORef storageRef s

cacheOptDesc ::
  NonceGenerator IO t ->
  IORef (ExprAllocator t) ->
  CFG.OptionSetting BaseIntegerType ->
  CFG.ConfigDesc
cacheOptDesc gen storageRef szSetting =
  CFG.mkOpt
    cacheTerms
    (cacheOptStyle gen storageRef szSetting)
    (Just (text "Use hash-consing during term construction"))
    (Just (ConcreteBool False))


newExprBuilder ::
  st t {- ^ Current state for simple builder. -} ->
  NonceGenerator IO t {- ^ Nonce generator for names -} ->
  IO (ExprBuilder t st)
newExprBuilder st gen = do
  st_ref <- newIORef st
  es <- newStorage gen

  let t = BoolExpr True initializationLoc
  let f = BoolExpr False initializationLoc
  let z = SemiRingLiteral SR.SemiRingRealRepr 0 initializationLoc

  loc_ref       <- newIORef initializationLoc
  storage_ref   <- newIORef es
  bindings_ref  <- newIORef emptySymbolVarBimap
  uninterp_fn_cache_ref <- newIORef Map.empty
  matlabFnCache <- stToIO $ PH.new
  loggerRef     <- newIORef Nothing

  -- Set up configuration options
  cfg <- CFG.initialConfig 0
           [ unaryThresholdDesc
           , bvdomainRangeLimitDesc
           , cacheStartSizeDesc
           ]
  unarySetting       <- CFG.getOptionSetting unaryThresholdOption cfg
  domainRangeSetting <- CFG.getOptionSetting bvdomainRangeLimitOption cfg
  cacheStartSetting  <- CFG.getOptionSetting cacheStartSizeOption cfg
  CFG.extendConfig [cacheOptDesc gen storage_ref cacheStartSetting] cfg
  nonLinearOps <- newIORef 0

  return $! SB { sbTrue  = t
               , sbFalse = f
               , sbZero = z
               , sbConfiguration = cfg
               , sbFloatReduce = True
               , sbUnaryThreshold = unarySetting
               , sbBVDomainRangeLimit = domainRangeSetting
               , sbCacheStartSize = cacheStartSetting
               , sbProgramLoc = loc_ref
               , exprCounter = gen
               , curAllocator = storage_ref
               , sbNonLinearOps = nonLinearOps
               , sbStateManager = st_ref
               , sbVarBindings = bindings_ref
               , sbUninterpFnCache = uninterp_fn_cache_ref
               , sbMatlabFnCache = matlabFnCache
               , sbSolverLogger = loggerRef
               }

-- | Get current variable bindings.
getSymbolVarBimap :: ExprBuilder t st -> IO (SymbolVarBimap t)
getSymbolVarBimap sym = readIORef (sbVarBindings sym)

-- | Stop caching applications in backend.
stopCaching :: ExprBuilder t st -> IO ()
stopCaching sb = do
  s <- newStorage (exprCounter sb)
  writeIORef (curAllocator sb) s

-- | Restart caching applications in backend (clears cache if it is currently caching).
startCaching :: ExprBuilder t st -> IO ()
startCaching sb = do
  sz <- CFG.getOpt (sbCacheStartSize sb)
  s <- newCachedStorage (exprCounter sb) (fromInteger sz)
  writeIORef (curAllocator sb) s

bvBinDivOp :: (1 <= w)
            => (Integer -> Integer -> Integer)
            -> (NatRepr w -> BVExpr t w -> BVExpr t w -> App (Expr t) (BaseBVType w))
            -> ExprBuilder t st
            -> BVExpr t w
            -> BVExpr t w
            -> IO (BVExpr t w)
bvBinDivOp f c sb x y = do
  let w = bvWidth x
  case (asUnsignedBV x, asUnsignedBV y) of
    (Just i, Just j) | j /= 0 -> bvLit sb w $ f i j
    _ -> sbMakeExpr sb $ c w x y

bvSignedBinDivOp :: (1 <= w)
                 => (Integer -> Integer -> Integer)
                 -> (NatRepr w -> BVExpr t w
                               -> BVExpr t w
                               -> App (Expr t) (BaseBVType w))
                 -> ExprBuilder t st
                 -> BVExpr t w
                 -> BVExpr t w
                 -> IO (BVExpr t w)
bvSignedBinDivOp f c sym x y = do
  let w = bvWidth x
  case (asSignedBV x, asSignedBV y) of
    (Just i, Just j) | j /= 0 -> bvLit sym w $ f i j
    _ -> sbMakeExpr sym $ c w x y


asConcreteIndices :: IsExpr e
                  => Ctx.Assignment e ctx
                  -> Maybe (Ctx.Assignment IndexLit ctx)
asConcreteIndices = traverseFC f
  where f :: IsExpr e => e tp -> Maybe (IndexLit tp)
        f x =
          case exprType x of
            BaseNatRepr  -> NatIndexLit . fromIntegral <$> asNat x
            BaseBVRepr w -> BVIndexLit w <$> asUnsignedBV x
            _ -> Nothing

symbolicIndices :: forall sym ctx
                 . IsExprBuilder sym
                => sym
                -> Ctx.Assignment IndexLit ctx
                -> IO (Ctx.Assignment (SymExpr sym) ctx)
symbolicIndices sym = traverseFC f
  where f :: IndexLit tp -> IO (SymExpr sym tp)
        f (NatIndexLit n)  = natLit sym n
        f (BVIndexLit w i) = bvLit sym w i

-- | This evaluate a symbolic function against a set of arguments.
betaReduce :: ExprBuilder t st
           -> ExprSymFn t (Expr t) args ret
           -> Ctx.Assignment (Expr t) args
           -> IO (Expr t ret)
betaReduce sym f args =
  case symFnInfo f of
    UninterpFnInfo{} ->
      sbNonceExpr sym $! FnApp f args
    DefinedFnInfo bound_vars e _ -> do
      evalBoundVars sym e bound_vars args
    MatlabSolverFnInfo fn_id _ _ -> do
      evalMatlabSolverFn fn_id sym args


-- | This runs one action, and if it returns a value different from the input,
-- then it runs the second.  Otherwise it returns the result value passed in.
--
-- It is used when an action may modify a value, and we only want to run a
-- second action if the value changed.
runIfChanged :: Eq e
             => e
             -> (e -> IO e) -- ^ First action to run
             -> r           -- ^ Result if no change.
             -> (e -> IO r) -- ^ Second action to run
             -> IO r
runIfChanged x f unChanged onChange = do
  y <- f x
  if x == y then
    return unChanged
   else
    onChange y

-- | This adds a binding from the variable to itself in the hashtable
-- to ensure it can't be rebound.
recordBoundVar :: PH.HashTable RealWorld (Expr t) (Expr t)
                  -> ExprBoundVar t tp
                  -> IO ()
recordBoundVar tbl v = do
  let e = BoundVarExpr v
  mr <- stToIO $ PH.lookup tbl e
  case mr of
    Just r -> do
      when (r /= e) $ do
        fail $ "Simulator internal error; do not support rebinding variables."
    Nothing -> do
      -- Bind variable to itself to ensure we catch when it is used again.
      stToIO $ PH.insert tbl e e


-- | The CachedSymFn is used during evaluation to store the results of reducing
-- the definitions of symbolic functions.
--
-- For each function it stores a pair containing a 'Bool' that is true if the
-- function changed as a result of evaluating it, and the reduced function
-- after evaluation.
--
-- The second arguments contains the arguments with the return type appended.
data CachedSymFn t c
  = forall a r
    . (c ~ (a ::> r))
    => CachedSymFn Bool (ExprSymFn t (Expr t) a r)

-- | Data structure used for caching evaluation.
data EvalHashTables t
   = EvalHashTables { exprTable :: !(PH.HashTable RealWorld (Expr t) (Expr t))
                    , fnTable  :: !(PH.HashTable RealWorld (Nonce t) (CachedSymFn t))
                    }

-- | Evaluate a simple function.
--
-- This returns whether the function changed as a Boolean and the function itself.
evalSimpleFn :: EvalHashTables t
             -> ExprBuilder t st
             -> ExprSymFn t (Expr t) idx ret
             -> IO (Bool,ExprSymFn t (Expr t) idx ret)
evalSimpleFn tbl sym f =
  case symFnInfo f of
    UninterpFnInfo{} -> return (False, f)
    DefinedFnInfo vars e evalFn -> do
      let n = symFnId f
      let nm = symFnName f
      CachedSymFn changed f' <-
        cachedEval (fnTable tbl) n $ do
          traverseFC_ (recordBoundVar (exprTable tbl)) vars
          e' <- evalBoundVars' tbl sym e
          if e == e' then
            return $! CachedSymFn False f
           else
            CachedSymFn True <$> definedFn sym nm vars e' evalFn
      return (changed, f')
    MatlabSolverFnInfo{} -> return (False, f)

evalBoundVars' :: forall t st ret
               .  EvalHashTables t
               -> ExprBuilder t st
               -> Expr t ret
               -> IO (Expr t ret)
evalBoundVars' tbls sym e0 =
  case e0 of
    SemiRingLiteral{} -> return e0
    StringExpr{} -> return e0
    BoolExpr{} -> return e0
    AppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      let a = appExprApp ae
      a' <- traverseApp (evalBoundVars' tbls sym) a
      if a == a' then
        return e0
       else
        reduceApp sym bvUnary a'
    NonceAppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      case nonceExprApp ae of
        Annotation tpr n a -> do
          a' <- evalBoundVars' tbls sym a
          if a == a' then
            return e0
          else
            sbNonceExpr sym $ Annotation tpr n a'
        Forall v e -> do
          recordBoundVar (exprTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (forallPred sym v)
        Exists v e -> do
          recordBoundVar (exprTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (existsPred sym v)
        ArrayFromFn f -> do
          (changed, f') <- evalSimpleFn tbls sym f
          if not changed then
            return e0
           else
            arrayFromFn sym f'
        MapOverArrays f _ args -> do
          (changed, f') <- evalSimpleFn tbls sym f
          let evalWrapper :: ArrayResultWrapper (Expr t) (idx ::> itp) utp
                          -> IO (ArrayResultWrapper (Expr t) (idx ::> itp) utp)
              evalWrapper (ArrayResultWrapper a) =
                ArrayResultWrapper <$> evalBoundVars' tbls sym a
          args' <- traverseFC evalWrapper args
          if not changed && args == args' then
            return e0
           else
            arrayMap sym f' args'
        ArrayTrueOnEntries f a -> do
          (changed, f') <- evalSimpleFn tbls sym f
          a' <- evalBoundVars' tbls sym a
          if not changed && a == a' then
            return e0
           else
            arrayTrueOnEntries sym f' a'
        FnApp f a -> do
          (changed, f') <- evalSimpleFn tbls sym f
          a' <- traverseFC (evalBoundVars' tbls sym) a
          if not changed && a == a' then
            return e0
           else
            applySymFn sym f' a'

    BoundVarExpr{} -> cachedEval (exprTable tbls) e0 $ return e0

initHashTable :: (HashableF key, TestEquality key)
              => Ctx.Assignment key args
              -> Ctx.Assignment val args
              -> ST s (PH.HashTable s key val)
initHashTable keys vals = do
  let sz = Ctx.size keys
  tbl <- PH.newSized (Ctx.sizeInt sz)
  Ctx.forIndexM sz $ \i -> do
    PH.insert tbl (keys Ctx.! i) (vals Ctx.! i)
  return tbl

-- | This evaluates the term with the given bound variables rebound to
-- the given arguments.
--
-- The algorithm works by traversing the subterms in the term in a bottom-up
-- fashion while using a hash-table to memoize results for shared subterms.  The
-- hash-table is pre-populated so that the bound variables map to the element,
-- so we do not need any extra map lookup when checking to see if a variable is
-- bound.
--
-- NOTE: This function assumes that variables in the substitution are not
-- themselves bound in the term (e.g. in a function definition or quantifier).
-- If this is not respected, then 'evalBoundVars' will call 'fail' with an
-- error message.
evalBoundVars :: ExprBuilder t st
              -> Expr t ret
              -> Ctx.Assignment (ExprBoundVar t) args
              -> Ctx.Assignment (Expr t) args
              -> IO (Expr t ret)
evalBoundVars sym e vars exprs = do
  expr_tbl <- stToIO $ initHashTable (fmapFC BoundVarExpr vars) exprs
  fn_tbl  <- stToIO $ PH.new
  let tbls = EvalHashTables { exprTable = expr_tbl
                            , fnTable  = fn_tbl
                            }
  evalBoundVars' tbls sym e

-- | This attempts to lookup an entry in a symbolic array.
--
-- It patterns maps on the array constructor.
sbConcreteLookup :: forall t st d tp range
                 . ExprBuilder t st
                   -- ^ Simple builder for creating terms.
                 -> Expr t (BaseArrayType (d::>tp) range)
                    -- ^ Array to lookup value in.
                 -> Maybe (Ctx.Assignment IndexLit (d::>tp))
                    -- ^ A concrete index that corresponds to the index or nothing
                    -- if the index is symbolic.
                 -> Ctx.Assignment (Expr t) (d::>tp)
                    -- ^ The index to lookup.
                 -> IO (Expr t range)
sbConcreteLookup sym arr0 mcidx idx
    -- Try looking up a write to a concrete address.
  | Just (ArrayMap _ _ entry_map def) <- asApp arr0
  , Just cidx <- mcidx =
      case AUM.lookup cidx entry_map of
        Just v -> return v
        Nothing -> sbConcreteLookup sym def mcidx idx
    -- Evaluate function arrays on ground values.
  | Just (ArrayFromFn f) <- asNonceApp arr0 = do
      betaReduce sym f idx

    -- Lookups on constant arrays just return value
  | Just (ConstantArray _ _ v) <- asApp arr0 = do
      return v
    -- Lookups on mux arrays just distribute over mux.
  | Just (BaseIte _ _ p x y) <- asApp arr0 = do
      xv <- sbConcreteLookup sym x mcidx idx
      yv <- sbConcreteLookup sym y mcidx idx
      baseTypeIte sym p xv yv
  | Just (MapOverArrays f _ args) <- asNonceApp arr0 = do
      let eval :: ArrayResultWrapper (Expr t) (d::>tp) utp
               -> IO (Expr t utp)
          eval a = sbConcreteLookup sym (unwrapArrayResult a) mcidx idx
      betaReduce sym f =<< traverseFC eval args
    -- Create select index.
  | otherwise = do
    case exprType arr0 of
      BaseArrayRepr _ range ->
        sbMakeExpr sym (SelectArray range arr0 idx)

----------------------------------------------------------------------
-- Expression builder instances

-- | Evaluate a weighted sum of natural number values.
natSum :: ExprBuilder t st -> WeightedSum (Expr t) SR.SemiRingNat -> IO (NatExpr t)
natSum sym s = semiRingSum sym s

-- | Evaluate a weighted sum of integer values.
intSum :: ExprBuilder t st -> WeightedSum (Expr t) SR.SemiRingInteger -> IO (IntegerExpr t)
intSum sym s = semiRingSum sym s

-- | Evaluate a weighted sum of real values.
realSum :: ExprBuilder t st -> WeightedSum (Expr t) SR.SemiRingReal -> IO (RealExpr t)
realSum sym s = semiRingSum sym s

bvSum :: ExprBuilder t st -> WeightedSum (Expr t) (SR.SemiRingBV flv w) -> IO (BVExpr t w)
bvSum sym s = semiRingSum sym s

conjPred :: ExprBuilder t st -> BoolMap (Expr t) -> IO (BoolExpr t)
conjPred sym bm =
  case BM.viewBoolMap bm of
    BoolMapUnit     -> return $ truePred sym
    BoolMapDualUnit -> return $ falsePred sym
    BoolMapTerms ((x,p):|[]) ->
      case p of
        Positive -> return x
        Negative -> notPred sym x
    _ -> sbMakeExpr sym $ ConjPred bm

bvUnary :: (1 <= w) => ExprBuilder t st -> UnaryBV (BoolExpr t) w -> IO (BVExpr t w)
bvUnary sym u
    | Just v <-  UnaryBV.asConstant u =
      bvLit sym (UnaryBV.width u) v
    | otherwise =
      sbMakeExpr sym (BVUnaryTerm u)

asUnaryBV :: (?unaryThreshold :: Int)
          => ExprBuilder t st
          -> BVExpr t n
          -> Maybe (UnaryBV (BoolExpr t) n)
asUnaryBV sym e
  | Just (BVUnaryTerm u) <- asApp e = Just u
  | ?unaryThreshold == 0 = Nothing
  | SemiRingLiteral (SR.SemiRingBVRepr _ w) v _ <- e = Just $ UnaryBV.constant sym w v
  | otherwise = Nothing

-- | This create a unary bitvector representing if the size is not too large.
sbTryUnaryTerm :: (1 <= w, ?unaryThreshold :: Int)
               => ExprBuilder t st
               -> Maybe (IO (UnaryBV (BoolExpr t) w))
               -> IO (BVExpr t w)
               -> IO (BVExpr t w)
sbTryUnaryTerm _sym Nothing fallback = fallback
sbTryUnaryTerm sym (Just mku) fallback =
  do u <- mku
     if UnaryBV.size u < ?unaryThreshold then
       bvUnary sym u
     else
       fallback

semiRingProd ::
  ExprBuilder t st ->
  SemiRingProduct (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingProd sym pd
  | WSum.nullProd pd = semiRingLit sym (WSum.prodRepr pd) (SR.one (WSum.prodRepr pd))
  | Just v <- WSum.asProdVar pd = return v
  | otherwise = sbMakeExpr sym $ SemiRingProd pd

semiRingSum ::
  ExprBuilder t st ->
  WeightedSum (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingSum sym s
    | Just c <- WSum.asConstant s = semiRingLit sym (WSum.sumRepr s) c
    | Just r <- WSum.asVar s      = return r
    | otherwise                   = sum' sym s

sum' ::
  ExprBuilder t st ->
  WeightedSum (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
sum' sym s = sbMakeExpr sym $ SemiRingSum s
{-# INLINE sum' #-}

scalarMul ::
   ExprBuilder t st ->
   SR.SemiRingRepr sr ->
   SR.Coefficient sr ->
   Expr t (SR.SemiRingBase sr) ->
   IO (Expr t (SR.SemiRingBase sr))
scalarMul sym sr c x
  | SR.eq sr (SR.zero sr) c = semiRingLit sym sr (SR.zero sr)
  | SR.eq sr (SR.one sr)  c = return x
  | Just r <- asSemiRingLit sr x =
    semiRingLit sym sr (SR.mul sr c r)
  | Just s <- asSemiRingSum sr x =
    sum' sym (WSum.scale sr c s)
  | otherwise =
    sum' sym (WSum.scaledVar sr c x)

semiRingIte ::
  ExprBuilder t st ->
  SR.SemiRingRepr sr ->
  Expr t BaseBoolType ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingIte sym sr c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotPred c') <- asApp c
  = semiRingIte sym sr c' y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

    -- Try to extract common sum information.
  | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
  , not (WSum.isZero sr z) = do
    xr <- semiRingSum sym x'
    yr <- semiRingSum sym y'
    let sz = 1 + iteSize xr + iteSize yr
    r <- sbMakeExpr sym (BaseIte (SR.semiRingBase sr) sz c xr yr)
    semiRingSum sym $! WSum.addVar sr z r

    -- final fallback, create the ite term
  | otherwise =
      let sz = 1 + iteSize x + iteSize y in
      sbMakeExpr sym (BaseIte (SR.semiRingBase sr) sz c x y)


mkIte ::
  ExprBuilder t st ->
  Expr t BaseBoolType ->
  Expr t bt ->
  Expr t bt ->
  IO (Expr t bt)
mkIte sym c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotPred c') <- asApp c
  = mkIte sym c' y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

  | otherwise =
      let sz = 1 + iteSize x + iteSize y in
      sbMakeExpr sym (BaseIte (exprType x) sz c x y)

semiRingLe ::
  ExprBuilder t st ->
  SR.OrderedSemiRingRepr sr ->
  (Expr t (SR.SemiRingBase sr) -> Expr t (SR.SemiRingBase sr) -> IO (Expr t BaseBoolType))
      {- ^ recursive call for simplifications -} ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t BaseBoolType)
semiRingLe sym osr rec x y
      -- Check for syntactic equality.
    | x == y = return (truePred sym)

      -- Strength reductions on a non-linear constraint to piecewise linear.
    | Just c <- asSemiRingLit sr x
    , SR.eq sr c (SR.zero sr)
    , Just (SemiRingProd pd) <- asApp y
    , Just Refl <- testEquality sr (WSum.prodRepr pd)
    = prodNonneg sym osr pd

      -- Another strength reduction
    | Just c <- asSemiRingLit sr y
    , SR.eq sr c (SR.zero sr)
    , Just (SemiRingProd pd) <- asApp x
    , Just Refl <- testEquality sr (WSum.prodRepr pd)
    = prodNonpos sym osr pd

      -- Push some comparisons under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (BaseIte _ _ c a b) <- asApp y
    = join (itePred sym c <$> rec x a <*> rec x b)

      -- Push some comparisons under if/then/else
    | Just (BaseIte tp _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    , Just Refl <- testEquality tp (SR.semiRingBase sr)
    = join (itePred sym c <$> rec a y <*> rec b y)

      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z) = do
      xr <- semiRingSum sym x'
      yr <- semiRingSum sym y'
      rec xr yr

      -- Default case
    | otherwise = sbMakeExpr sym $ SemiRingLe osr x y

 where sr = SR.orderedSemiRing osr


semiRingEq ::
  ExprBuilder t st ->
  SR.SemiRingRepr sr ->
  (Expr t (SR.SemiRingBase sr) -> Expr t (SR.SemiRingBase sr) -> IO (Expr t BaseBoolType))
    {- ^ recursive call for simplifications -} ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t BaseBoolType)
semiRingEq sym sr rec x y
  -- Check for syntactic equality.
  | x == y = return (truePred sym)

    -- Push some equalities under if/then/else
  | SemiRingLiteral _ _ _ <- x
  , Just (BaseIte _ _ c a b) <- asApp y
  = join (itePred sym c <$> rec x a <*> rec x b)

    -- Push some equalities under if/then/else
  | Just (BaseIte _ _ c a b) <- asApp x
  , SemiRingLiteral _ _ _ <- y
  = join (itePred sym c <$> rec a y <*> rec b y)

  | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
  , not (WSum.isZero sr z) =
    case (WSum.asConstant x', WSum.asConstant y') of
      (Just a, Just b) -> return $! backendPred sym (SR.eq sr a b)
      _ -> do xr <- semiRingSum sym x'
              yr <- semiRingSum sym y'
              sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min xr yr) (max xr yr)

  | otherwise =
    sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min x y) (max x y)

semiRingAdd ::
  forall t st sr.
  ExprBuilder t st ->
  SR.SemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingAdd sym sr x y =
    case (viewSemiRing sr x, viewSemiRing sr y) of
      (SR_Constant c, _) | SR.eq sr c (SR.zero sr) -> return y
      (_, SR_Constant c) | SR.eq sr c (SR.zero sr) -> return x

      (SR_Constant xc, SR_Constant yc) ->
        semiRingLit sym sr (SR.add sr xc yc)

      (SR_Constant xc, SR_Sum ys) ->
        sum' sym (WSum.addConstant sr ys xc)
      (SR_Sum xs, SR_Constant yc) ->
        sum' sym (WSum.addConstant sr xs yc)

      (SR_Constant xc, _)
        | Just (BaseIte _ _ cond a b) <- asApp y
        , isConstantSemiRingExpr a || isConstantSemiRingExpr b -> do
            xa <- semiRingAdd sym sr x a
            xb <- semiRingAdd sym sr x b
            semiRingIte sym sr cond xa xb
        | otherwise ->
            sum' sym (WSum.addConstant sr (WSum.var sr y) xc)

      (_, SR_Constant yc)
        | Just (BaseIte _ _ cond a b) <- asApp x
        , isConstantSemiRingExpr a || isConstantSemiRingExpr b -> do
            ay <- semiRingAdd sym sr a y
            by <- semiRingAdd sym sr b y
            semiRingIte sym sr cond ay by
        | otherwise ->
            sum' sym (WSum.addConstant sr (WSum.var sr x) yc)

      (SR_Sum xs, SR_Sum ys) -> semiRingSum sym (WSum.add sr xs ys)
      (SR_Sum xs, _)         -> semiRingSum sym (WSum.addVar sr xs y)
      (_ , SR_Sum ys)        -> semiRingSum sym (WSum.addVar sr ys x)
      _                      -> semiRingSum sym (WSum.addVars sr x y)
  where isConstantSemiRingExpr :: Expr t (SR.SemiRingBase sr) -> Bool
        isConstantSemiRingExpr (viewSemiRing sr -> SR_Constant _) = True
        isConstantSemiRingExpr _ = False

semiRingMul ::
  ExprBuilder t st ->
  SR.SemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingMul sym sr x y =
  case (viewSemiRing sr x, viewSemiRing sr y) of
    (SR_Constant c, _) -> scalarMul sym sr c y
    (_, SR_Constant c) -> scalarMul sym sr c x

    (SR_Sum (WSum.asAffineVar -> Just (c,x',o)), _) ->
      do cxy <- scalarMul sym sr c =<< semiRingMul sym sr x' y
         oy  <- scalarMul sym sr o y
         semiRingAdd sym sr cxy oy

    (_, SR_Sum (WSum.asAffineVar -> Just (c,y',o))) ->
      do cxy <- scalarMul sym sr c =<< semiRingMul sym sr x y'
         ox  <- scalarMul sym sr o x
         semiRingAdd sym sr cxy ox

    (SR_Prod px, SR_Prod py) -> semiRingProd sym (WSum.prodMul px py)
    (SR_Prod px, _)          -> semiRingProd sym (WSum.prodMul px (WSum.prodVar sr y))
    (_, SR_Prod py)          -> semiRingProd sym (WSum.prodMul (WSum.prodVar sr x) py)
    _                        -> semiRingProd sym (WSum.prodMul (WSum.prodVar sr x) (WSum.prodVar sr y))


prodNonneg ::
  ExprBuilder t st ->
  SR.OrderedSemiRingRepr sr ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType)
prodNonneg sym osr pd =
  do let sr = SR.orderedSemiRing osr
     zero <- semiRingLit sym sr (SR.zero sr)
     fst <$> computeNonnegNonpos sym osr zero pd

prodNonpos ::
  ExprBuilder t st ->
  SR.OrderedSemiRingRepr sr ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType)
prodNonpos sym osr pd =
  do let sr = SR.orderedSemiRing osr
     zero <- semiRingLit sym sr (SR.zero sr)
     snd <$> computeNonnegNonpos sym osr zero pd

computeNonnegNonpos ::
  ExprBuilder t st ->
  SR.OrderedSemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) {- zero element -} ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType, Expr t BaseBoolType)
computeNonnegNonpos sym osr zero pd =
   fromMaybe (truePred sym, falsePred sym) <$> WSum.prodEvalM merge single pd
 where

 single x = (,) <$> reduceApp sym bvUnary (SemiRingLe osr zero x) -- nonnegative
                <*> reduceApp sym bvUnary (SemiRingLe osr x zero) -- nonpositive

 merge (nn1, np1) (nn2, np2) =
   do nn <- join (orPred sym <$> andPred sym nn1 nn2 <*> andPred sym np1 np2)
      np <- join (orPred sym <$> andPred sym nn1 np2 <*> andPred sym np1 nn2)
      return (nn, np)



arrayResultIdxType :: BaseTypeRepr (BaseArrayType (idx ::> itp) d)
                   -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
arrayResultIdxType (BaseArrayRepr idx _) = idx

-- | This decomposes A ExprBuilder array expression into a set of indices that
-- have been updated, and an underlying index.
data ArrayMapView i f tp
   = ArrayMapView { _arrayMapViewIndices :: !(AUM.ArrayUpdateMap f i tp)
                  , _arrayMapViewExpr    :: !(f (BaseArrayType i tp))
                  }

-- | Construct an 'ArrayMapView' for an element.
viewArrayMap :: Expr t (BaseArrayType i tp)
             -> ArrayMapView i (Expr t) tp
viewArrayMap  x
  | Just (ArrayMap _ _ m c) <- asApp x = ArrayMapView m c
  | otherwise = ArrayMapView AUM.empty x

-- | Construct an 'ArrayMapView' for an element.
underlyingArrayMapExpr :: ArrayResultWrapper (Expr t) i tp
                      -> ArrayResultWrapper (Expr t) i tp
underlyingArrayMapExpr x
  | Just (ArrayMap _ _ _ c) <- asApp (unwrapArrayResult x) = ArrayResultWrapper c
  | otherwise = x

-- | Return set of addresss in assignment that are written to by at least one expr
concreteArrayEntries :: forall t i ctx
                     .  Ctx.Assignment (ArrayResultWrapper (Expr t) i) ctx
                     -> Set (Ctx.Assignment IndexLit i)
concreteArrayEntries = foldlFC' f Set.empty
  where f :: Set (Ctx.Assignment IndexLit i)
          -> ArrayResultWrapper (Expr t) i tp
          -> Set (Ctx.Assignment IndexLit i)
        f s e
          | Just (ArrayMap _ _ m _) <- asApp (unwrapArrayResult  e) =
            Set.union s (AUM.keysSet m)
          | otherwise = s

data NatLit tp = (tp ~ BaseNatType) => NatLit Natural

asNatBounds :: Ctx.Assignment (Expr t) idx -> Maybe (Ctx.Assignment NatLit idx)
asNatBounds = traverseFC f
  where f :: Expr t tp -> Maybe (NatLit tp)
        f (SemiRingLiteral SR.SemiRingNatRepr n _) = Just (NatLit n)
        f _ = Nothing

foldBoundLeM :: (r -> Natural -> IO r) -> r -> Natural -> IO r
foldBoundLeM _ r 0 = pure r
foldBoundLeM f r n = do
  r' <- foldBoundLeM f r (n-1)
  f r' n

foldIndicesInRangeBounds :: forall sym idx r
                         .  IsExprBuilder sym
                         => sym
                         -> (r -> Ctx.Assignment (SymExpr sym) idx -> IO r)
                         -> r
                         -> Ctx.Assignment NatLit idx
                         -> IO r
foldIndicesInRangeBounds sym f0 a0 bnds0 = do
  case bnds0 of
    Ctx.Empty -> f0 a0 Ctx.empty
    bnds Ctx.:> NatLit b -> foldIndicesInRangeBounds sym (g f0) a0 bnds
      where g :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseNatType) -> IO r)
              -> r
              -> Ctx.Assignment (SymExpr sym) idx0
              -> IO r
            g f a i = foldBoundLeM (h f i) a b

            h :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseNatType) -> IO r)
              -> Ctx.Assignment (SymExpr sym) idx0
              -> r
              -> Natural
              -> IO r
            h f i a j = do
              je <- natLit sym j
              f a (i Ctx.:> je)

-- | Examine the list of terms, and determine if any one of them
--   appears in the given @BoolMap@ with the same polarity.
checkAbsorption ::
  BoolMap (Expr t) ->
  [(BoolExpr t, Polarity)] ->
  Bool
checkAbsorption _bm [] = False
checkAbsorption bm ((x,p):_)
  | Just p' <- BM.contains bm x, p == p' = True
checkAbsorption bm (_:xs) = checkAbsorption bm xs

-- | If @tryAndAbsorption x y@ returns @True@, that means that @y@
-- implies @x@, so that the conjunction @x AND y = y@. A @False@
-- result gives no information.
tryAndAbsorption ::
  BoolExpr t ->
  BoolExpr t ->
  Bool
tryAndAbsorption (asApp -> Just (NotPred (asApp -> Just (ConjPred as)))) (asConjunction -> bs)
  = checkAbsorption (BM.reversePolarities as) bs
tryAndAbsorption _ _ = False


-- | If @tryOrAbsorption x y@ returns @True@, that means that @x@
-- implies @y@, so that the disjunction @x OR y = y@. A @False@
-- result gives no information.
tryOrAbsorption ::
  BoolExpr t ->
  BoolExpr t ->
  Bool
tryOrAbsorption (asApp -> Just (ConjPred as)) (asDisjunction -> bs)
  = checkAbsorption as bs
tryOrAbsorption _ _ = False


-- | A slightly more aggressive syntactic equality check than testEquality,
--   `sameTerm` will recurse through a small collection of known syntax formers.
sameTerm :: Expr t a -> Expr t b -> Maybe (a :~: b)

sameTerm (asApp -> Just (FloatToBinary fppx x)) (asApp -> Just (FloatToBinary fppy y)) =
  do Refl <- testEquality fppx fppy
     Refl <- sameTerm x y
     return Refl

sameTerm x y = testEquality x y

instance IsExprBuilder (ExprBuilder t st) where
  getConfiguration = sbConfiguration

  setSolverLogListener sb = writeIORef (sbSolverLogger sb)
  getSolverLogListener sb = readIORef (sbSolverLogger sb)

  logSolverEvent sb ev =
    readIORef (sbSolverLogger sb) >>= \case
      Nothing -> return ()
      Just f  -> f ev

  getStatistics sb = do
    allocs <- countNoncesGenerated (exprCounter sb)
    nonLinearOps <- readIORef (sbNonLinearOps sb)
    return $ Statistics { statAllocs = allocs
                        , statNonLinearOps = nonLinearOps }

  annotateTerm sym e =
    case e of
      NonceAppExpr (nonceExprApp -> Annotation _ n _) -> return (n, e)
      _ -> do
        let tpr = exprType e
        n <- sbFreshIndex sym
        e' <- sbNonceExpr sym (Annotation tpr n e)
        return (n, e')

  ----------------------------------------------------------------------
  -- Program location operations

  getCurrentProgramLoc = curProgramLoc
  setCurrentProgramLoc sym l = writeIORef (sbProgramLoc sym) l

  ----------------------------------------------------------------------
  -- Bool operations.

  truePred  = sbTrue
  falsePred = sbFalse

  notPred sym x
    | Just b <- asConstantPred x
    = return (backendPred sym $! not b)

    | Just (NotPred x') <- asApp x
    = return x'

    | otherwise
    = sbMakeExpr sym (NotPred x)

  eqPred sym x y
    | x == y
    = return (truePred sym)

    | Just (NotPred x') <- asApp x
    = xorPred sym x' y

    | Just (NotPred y') <- asApp y
    = xorPred sym x y'

    | otherwise
    = case (asConstantPred x, asConstantPred y) of
        (Just False, _)    -> notPred sym y
        (Just True, _)     -> return y
        (_, Just False)    -> notPred sym x
        (_, Just True)     -> return x
        _ -> sbMakeExpr sym $ BaseEq BaseBoolRepr (min x y) (max x y)

  xorPred sym x y = notPred sym =<< eqPred sym x y

  andPred sym x y =
    case (asConstantPred x, asConstantPred y) of
      (Just True, _)  -> return y
      (Just False, _) -> return x
      (_, Just True)  -> return x
      (_, Just False) -> return y
      _ | x == y -> return x -- and is idempotent
        | otherwise -> go x y

   where
   go a b
     | Just (ConjPred as) <- asApp a
     , Just (ConjPred bs) <- asApp b
     = conjPred sym $ BM.combine as bs

     | tryAndAbsorption a b
     = return b

     | tryAndAbsorption b a
     = return a

     | Just (ConjPred as) <- asApp a
     = conjPred sym $ uncurry BM.addVar (asPosAtom b) as

     | Just (ConjPred bs) <- asApp b
     = conjPred sym $ uncurry BM.addVar (asPosAtom a) bs

     | otherwise
     = conjPred sym $ BM.fromVars [asPosAtom a, asPosAtom b]

  orPred sym x y =
    case (asConstantPred x, asConstantPred y) of
      (Just True, _)  -> return x
      (Just False, _) -> return y
      (_, Just True)  -> return y
      (_, Just False) -> return x
      _ | x == y -> return x -- or is idempotent
        | otherwise -> go x y

   where
   go a b
     | Just (NotPred (asApp -> Just (ConjPred as))) <- asApp a
     , Just (NotPred (asApp -> Just (ConjPred bs))) <- asApp b
     = notPred sym =<< conjPred sym (BM.combine as bs)

     | tryOrAbsorption a b
     = return b

     | tryOrAbsorption b a
     = return a

     | Just (NotPred (asApp -> Just (ConjPred as))) <- asApp a
     = notPred sym =<< conjPred sym (uncurry BM.addVar (asNegAtom b) as)

     | Just (NotPred (asApp -> Just (ConjPred bs))) <- asApp b
     = notPred sym =<< conjPred sym (uncurry BM.addVar (asNegAtom a) bs)

     | otherwise
     = notPred sym =<< conjPred sym (BM.fromVars [asNegAtom a, asNegAtom b])

  itePred sb c x y
      -- ite c c y = c || y
    | c == x = orPred sb c y

      -- ite c x c = c && x
    | c == y = andPred sb c x

      -- ite c x x = x
    | x == y = return x

      -- ite 1 x y = x
    | Just True  <- asConstantPred c = return x

      -- ite 0 x y = y
    | Just False <- asConstantPred c = return y

      -- ite !c x y = ite c y x
    | Just (NotPred c') <- asApp c = itePred sb c' y x

      -- ite c 1 y = c || y
    | Just True  <- asConstantPred x = orPred sb c y

      -- ite c 0 y = !c && y
    | Just False <- asConstantPred x = andPred sb y =<< notPred sb c

      -- ite c x 1 = !c || x
    | Just True  <- asConstantPred y = orPred sb x =<< notPred sb c

      -- ite c x 0 = c && x
    | Just False <- asConstantPred y = andPred sb c x

      -- Default case
    | otherwise =
        let sz = 1 + iteSize x + iteSize y in
        sbMakeExpr sb $ BaseIte BaseBoolRepr sz c x y

  ----------------------------------------------------------------------
  -- Nat operations.

  natLit sym n = semiRingLit sym SR.SemiRingNatRepr n

  natAdd sym x y = semiRingAdd sym SR.SemiRingNatRepr x y

  natSub sym x y = do
    xr <- natToInteger sym x
    yr <- natToInteger sym y
    integerToNat sym =<< intSub sym xr yr

  natMul sym x y = semiRingMul sym SR.SemiRingNatRepr x y

  natDiv sym x y
    | Just m <- asNat x, Just n <- asNat y, n /= 0 = do
      natLit sym (m `div` n)
      -- 0 / y
    | Just 0 <- asNat x = do
      return x
      -- x / 1
    | Just 1 <- asNat y = do
      return x
    | otherwise = do
      sbMakeExpr sym (NatDiv x y)

  natMod sym x y
    | Just m <- asNat x, Just n <- asNat y, n /= 0 = do
      natLit sym (m `mod` n)
    | Just 0 <- asNat x = do
      natLit sym 0
    | Just 1 <- asNat y = do
      natLit sym 0
    | otherwise = do
      sbMakeExpr sym (NatMod x y)

  natIte sym c x y = semiRingIte sym SR.SemiRingNatRepr c x y

  natEq sym x y
    | Just b <- natCheckEq (exprAbsValue x) (exprAbsValue y)
    = return (backendPred sym b)

    | otherwise
    = semiRingEq sym SR.SemiRingNatRepr (natEq sym) x y

  natLe sym x y
    | Just b <- natCheckLe (exprAbsValue x) (exprAbsValue y)
    = return (backendPred sym b)

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingNatRepr (natLe sym) x y

  ----------------------------------------------------------------------
  -- Integer operations.

  intLit sym n = semiRingLit sym SR.SemiRingIntegerRepr n

  intNeg sym x = scalarMul sym SR.SemiRingIntegerRepr (-1) x

  intAdd sym x y = semiRingAdd sym SR.SemiRingIntegerRepr x y

  intMul sym x y = semiRingMul sym SR.SemiRingIntegerRepr x y

  intIte sym c x y = semiRingIte sym SR.SemiRingIntegerRepr c x y

  intEq sym x y
      -- Use range check
    | Just b <- rangeCheckEq (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to bitvector equality, when possible
    | Just (SBVToInteger xbv) <- asApp x
    , Just (SBVToInteger ybv) <- asApp y
    = let wx = bvWidth xbv
          wy = bvWidth ybv
          -- Sign extend to largest bitvector and compare.
       in case compareNat wx wy of
            NatLT _ -> do
              Just LeqProof <- return (testLeq (incNat wx) wy)
              x' <- bvSext sym wy xbv
              bvEq sym x' ybv
            NatEQ ->
              bvEq sym xbv ybv
            NatGT _ -> do
              Just LeqProof <- return (testLeq (incNat wy) wx)
              y' <- bvSext sym wx ybv
              bvEq sym xbv y'

      -- Reduce to bitvector equality, when possible
    | Just (BVToInteger xbv) <- asApp x
    , Just (BVToInteger ybv) <- asApp y
    = let wx = bvWidth xbv
          wy = bvWidth ybv
          -- Zero extend to largest bitvector and compare.
       in case compareNat wx wy of
            NatLT _ -> do
              Just LeqProof <- return (testLeq (incNat wx) wy)
              x' <- bvZext sym wy xbv
              bvEq sym x' ybv
            NatEQ ->
              bvEq sym xbv ybv
            NatGT _ -> do
              Just LeqProof <- return (testLeq (incNat wy) wx)
              y' <- bvZext sym wx ybv
              bvEq sym xbv y'

    | Just (SBVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if yi < minSigned w || yi > maxSigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w yi

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minSigned w || xi > maxSigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w xi

    | Just (BVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if yi < minUnsigned w || yi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w yi

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minUnsigned w || xi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w xi

    | otherwise = semiRingEq sym SR.SemiRingIntegerRepr (intEq sym) x y

  intLe sym x y
      -- Use abstract domains
    | Just b <- rangeCheckLe (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Check with two bitvectors.
    | Just (SBVToInteger xbv) <- asApp x
    , Just (SBVToInteger ybv) <- asApp y
    = do let wx = bvWidth xbv
         let wy = bvWidth ybv
         -- Sign extend to largest bitvector and compare.
         case compareNat wx wy of
           NatLT _ -> do
             Just LeqProof <- return (testLeq (incNat wx) wy)
             x' <- bvSext sym wy xbv
             bvSle sym x' ybv
           NatEQ -> bvSle sym xbv ybv
           NatGT _ -> do
             Just LeqProof <- return (testLeq (incNat wy) wx)
             y' <- bvSext sym wx ybv
             bvSle sym xbv y'

      -- Check with two bitvectors.
    | Just (BVToInteger xbv) <- asApp x
    , Just (BVToInteger ybv) <- asApp y
    = do let wx = bvWidth xbv
         let wy = bvWidth ybv
         -- Zero extend to largest bitvector and compare.
         case compareNat wx wy of
           NatLT _ -> do
             Just LeqProof <- return (testLeq (incNat wx) wy)
             x' <- bvZext sym wy xbv
             bvUle sym x' ybv
           NatEQ -> bvUle sym xbv ybv
           NatGT _ -> do
             Just LeqProof <- return (testLeq (incNat wy) wx)
             y' <- bvZext sym wx ybv
             bvUle sym xbv y'

    | Just (SBVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if | yi < minSigned w -> return (falsePred sym)
         | yi > maxSigned w -> return (truePred sym)
         | otherwise -> join (bvSle sym <$> pure xbv <*> bvLit sym w yi)

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minSigned w -> return (truePred sym)
         | xi > maxSigned w -> return (falsePred sym)
         | otherwise -> join (bvSle sym <$> bvLit sym w xi <*> pure ybv)

    | Just (BVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if | yi < minUnsigned w -> return (falsePred sym)
         | yi > maxUnsigned w -> return (truePred sym)
         | otherwise -> join (bvUle sym <$> pure xbv <*> bvLit sym w yi)

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minUnsigned w -> return (truePred sym)
         | xi > maxUnsigned w -> return (falsePred sym)
         | otherwise -> join (bvUle sym <$> bvLit sym w xi <*> pure ybv)

{-  FIXME? how important are these reductions?

      -- Compare to BV lower bound.
    | Just (SBVToInteger xbv) <- x = do
      let w = bvWidth xbv
      l <- curProgramLoc sym
      b_max <- realGe sym y (SemiRingLiteral SemiRingReal (toRational (maxSigned w)) l)
      b_min <- realGe sym y (SemiRingLiteral SemiRingReal (toRational (minSigned w)) l)
      orPred sym b_max =<< andPred sym b_min =<< (bvSle sym xbv =<< realToSBV sym w y)

      -- Compare to SBV upper bound.
    | SBVToReal ybv <- y = do
      let w = bvWidth ybv
      l <- curProgramLoc sym
      b_min <- realLe sym x (SemiRingLiteral SemiRingReal (toRational (minSigned w)) l)
      b_max <- realLe sym x (SemiRingLiteral SemiRingReal (toRational (maxSigned w)) l)
      orPred sym b_min
        =<< andPred sym b_max
        =<< (\xbv -> bvSle sym xbv ybv) =<< realToSBV sym w x
-}

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingIntegerRepr (intLe sym) x y

  intAbs sym x
    | Just i <- asInteger x = intLit sym (abs i)
    | Just True <- rangeCheckLe (SingleRange 0) (exprAbsValue x) = return x
    | Just True <- rangeCheckLe (exprAbsValue x) (SingleRange 0) = intNeg sym x
    | otherwise = sbMakeExpr sym (IntAbs x)

  intDiv sym x y
      -- Div by 1.
    | Just 1 <- asInteger y = return x
      -- Div 0 by anything is zero.
    | Just 0 <- asInteger x = intLit sym 0
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asInteger y, yi /= 0 =
      if yi >= 0 then
        intLit sym (xi `div` yi)
      else
        intLit sym (negate (xi `div` negate yi))
      -- Return int div
    | otherwise =
        sbMakeExpr sym (IntDiv x y)

  intMod sym x y
      -- Mod by 1.
    | Just 1 <- asInteger y = intLit sym 0
      -- Mod 0 by anything is zero.
    | Just 0 <- asInteger x = intLit sym 0
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asInteger y, yi /= 0 =
        intLit sym (xi `mod` abs yi)
    | Just (SemiRingSum xsum) <- asApp x
    , SR.SemiRingIntegerRepr <- WSum.sumRepr xsum
    , Just yi <- asInteger y
    , yi /= 0 =
        case WSum.reduceIntSumMod xsum (abs yi) of
          xsum' | Just xi <- WSum.asConstant xsum' ->
                    intLit sym xi
                | otherwise ->
                    do x' <- intSum sym xsum'
                       sbMakeExpr sym (IntMod x' y)
      -- Return int mod.
    | otherwise =
        sbMakeExpr sym (IntMod x y)

  intDivisible sym x k
    | k == 0 = intEq sym x =<< intLit sym 0
    | k == 1 = return (truePred sym)
    | Just xi <- asInteger x = return $ backendPred sym (xi `mod` (toInteger k) == 0)
    | Just (SemiRingSum xsum) <- asApp x
    , SR.SemiRingIntegerRepr <- WSum.sumRepr xsum =
        case WSum.reduceIntSumMod xsum (toInteger k) of
          xsum' | Just xi <- WSum.asConstant xsum' ->
                    return $ backendPred sym (xi == 0)
                | otherwise ->
                    do x' <- intSum sym xsum'
                       sbMakeExpr sym (IntDivisible x' k)
    | otherwise =
        sbMakeExpr sym (IntDivisible x k)

  ---------------------------------------------------------------------
  -- Bitvector operations

  bvLit sym w i =
    semiRingLit sym (SR.SemiRingBVRepr SR.BVArithRepr w) (toUnsigned w i)

  bvConcat sym x y =
    case (asUnsignedBV x, asUnsignedBV y) of
      -- both values are constants, just compute the concatenation
      (Just xv, Just yv) -> do
          let shft :: Int
              shft = fromIntegral (natValue (bvWidth y))
          let w' = addNat (bvWidth x) (bvWidth y)
          -- Work around to satisfy GHC typechecker.
          case isPosNat w' of
            Nothing -> fail $ "bvConcat given bad width."
            Just LeqProof -> do
              bvLit sym w' ((xv `Bits.shiftL` shft) Bits..|. yv)
      -- reassociate to combine constants where possible
      (Just _xv, _)
        | Just (BVConcat _w a b) <- asApp y
        , Just _av <- asUnsignedBV a
        , Just Refl <- testEquality (addNat (bvWidth x) (addNat (bvWidth a) (bvWidth b)))
                        (addNat (addNat (bvWidth x) (bvWidth a)) (bvWidth b))
        , Just LeqProof <- isPosNat (addNat (bvWidth x) (bvWidth a)) -> do
            xa <- bvConcat sym x a
            bvConcat sym xa b
      -- concat two adjacent sub-selects just makes a single select
      _ | Just (BVSelect idx1 n1 a) <- asApp x
        , Just (BVSelect idx2 n2 b) <- asApp y
        , Just Refl <- sameTerm a b
        , Just Refl <- testEquality idx1 (addNat idx2 n2)
        , Just LeqProof <- isPosNat (addNat n1 n2)
        , Just LeqProof <- testLeq (addNat idx2 (addNat n1 n2)) (bvWidth a) ->
            bvSelect sym idx2 (addNat n1 n2) a
      -- always reassociate to the right
      _ | Just (BVConcat _w a b) <- asApp x
        , Just _bv <- asUnsignedBV b
        , Just Refl <- testEquality (addNat (bvWidth a) (addNat (bvWidth b) (bvWidth y)))
                        (addNat (addNat (bvWidth a) (bvWidth b)) (bvWidth y))
        , Just LeqProof <- isPosNat (addNat (bvWidth b) (bvWidth y)) -> do
            by <- bvConcat sym b y
            bvConcat sym a by
      -- no special case applies, emit a basic concat expression
      _ -> do
        let wx = bvWidth x
        let wy = bvWidth y
        Just LeqProof <- return (isPosNat (addNat wx wy))
        sbMakeExpr sym $ BVConcat (addNat wx wy) x y

  -- bvSelect has a bunch of special cases that examine the form of the
  -- bitvector being selected from.  This can significantly reduce the size
  -- of expressions that result from the very verbose packing and unpacking
  -- operations that arise from byte-oriented memory models.
  bvSelect sb idx n x
    | Just xv <- asUnsignedBV x = do
      let mask = maxUnsigned n
      let shft = fromIntegral (natValue idx)
      bvLit sb n ((xv `Bits.shiftR` shft) Bits..&. mask)

      -- nested selects can be collapsed
    | Just (BVSelect idx' _n' b) <- asApp x
    , let idx2 = addNat idx idx'
    , Just LeqProof <- testLeq (addNat idx2 n) (bvWidth b) =
      bvSelect sb idx2 n b

      -- select the entire bitvector is the identity function
    | Just _ <- testEquality idx (knownNat :: NatRepr 0)
    , Just Refl <- testEquality n (bvWidth x) =
      return x

    | Just (BVShl w a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq diffRepr idx = do
      Just LeqProof <- return $ testLeq (addNat (subNat idx diffRepr) n) w
      bvSelect sb (subNat idx diffRepr) n a

    | Just (BVShl _w _a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq (addNat idx n) diffRepr =
      bvLit sb n 0

    | Just (BVAshr w a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq (addNat (addNat idx diffRepr) n) w =
      bvSelect sb (addNat idx diffRepr) n a

    | Just (BVLshr w a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq (addNat (addNat idx diffRepr) n) w =
      bvSelect sb (addNat idx diffRepr) n a

    | Just (BVLshr w _a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq w (addNat idx diffRepr) =
      bvLit sb n 0

      -- select from a sign extension
    | Just (BVSext w b) <- asApp x = do
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (bvWidth b) w
      let ext = subNat w (bvWidth b)
      -- Add dynamic check
      Just LeqProof <- return $ isPosNat w
      Just LeqProof <- return $ isPosNat ext
      zeros <- minUnsignedBV sb ext
      ones  <- maxUnsignedBV sb ext
      c     <- bvIsNeg sb b
      hi    <- bvIte sb c ones zeros
      x'    <- bvConcat sb hi b
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (addNat idx n) (addNat ext (bvWidth b))
      bvSelect sb idx n x'

      -- select from a zero extension
    | Just (BVZext w b) <- asApp x = do
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (bvWidth b) w
      let ext = subNat w (bvWidth b)
      Just LeqProof <- return $ isPosNat w
      Just LeqProof <- return $ isPosNat ext
      hi    <- bvLit sb ext 0
      x'    <- bvConcat sb hi b
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (addNat idx n) (addNat ext (bvWidth b))
      bvSelect sb idx n x'

      -- select is entirely within the less-significant bits of a concat
    | Just (BVConcat _w _a b) <- asApp x
    , Just LeqProof <- testLeq (addNat idx n) (bvWidth b) = do
      bvSelect sb idx n b

      -- select is entirely within the more-significant bits of a concat
    | Just (BVConcat _w a b) <- asApp x
    , Just LeqProof <- testLeq (bvWidth b) idx
    , Just LeqProof <- isPosNat idx
    , let diff = subNat idx (bvWidth b)
    , Just LeqProof <- testLeq (addNat diff n) (bvWidth a) = do
      bvSelect sb (subNat idx (bvWidth b)) n a

    -- when the selected region overlaps a concat boundary we have:
    --  select idx n (concat a b) =
    --      concat (select 0 n1 a) (select idx n2 b)
    --   where n1 + n2 = n and idx + n2 = width b
    --
    -- NB: this case must appear after the two above that check for selects
    --     entirely within the first or second arguments of a concat, otherwise
    --     some of the arithmetic checks below may fail
    | Just (BVConcat _w a b) <- asApp x = do
      Just LeqProof <- return $ testLeq idx (bvWidth b)
      let n2 = subNat (bvWidth b) idx
      Just LeqProof <- return $ testLeq n2 n
      let n1 = subNat n n2
      let z  = knownNat :: NatRepr 0

      Just LeqProof <- return $ isPosNat n1
      Just LeqProof <- return $ testLeq (addNat z n1) (bvWidth a)
      a' <- bvSelect sb z   n1 a

      Just LeqProof <- return $ isPosNat n2
      Just LeqProof <- return $ testLeq (addNat idx n2) (bvWidth b)
      b' <- bvSelect sb idx n2 b

      Just Refl <- return $ testEquality (addNat n1 n2) n
      bvConcat sb a' b'

    -- Truncate a weighted sum: Remove terms with coefficients that
    -- would become zero after truncation.
    --
    -- Truncation of w-bit words down to n bits respects congruence
    -- modulo 2^n. Furthermore, w-bit addition and multiplication also
    -- preserve congruence modulo 2^n. This means that it is sound to
    -- replace coefficients in a weighted sum with new masked ones
    -- that are congruent modulo 2^n: the final result after
    -- truncation will be the same.
    --
    -- NOTE: This case is carefully designed to preserve sharing. Only
    -- one App node (the SemiRingSum) is ever deconstructed. The
    -- 'traverseCoeffs' call does not touch any other App nodes inside
    -- the WeightedSum. Finally, we only reconstruct a new SemiRingSum
    -- App node in the event that one of the coefficients has changed;
    -- the writer monad tracks whether a change has occurred.
    | Just (SemiRingSum s) <- asApp x
    , SR.SemiRingBVRepr SR.BVArithRepr _w <- WSum.sumRepr s
    , Just Refl <- testEquality idx (knownNat :: NatRepr 0) =
      do let mask = maxUnsigned n
         let reduce i
               | i Bits..&. mask == 0 = writer (0, Any True)
               | otherwise            = writer (i, Any False)
         let (s', Any changed) = runWriter $ WSum.traverseCoeffs reduce s
         x' <- if changed then sbMakeExpr sb (SemiRingSum s') else return x
         sbMakeExpr sb $ BVSelect idx n x'

{-  Avoid doing work that may lose sharing...

    -- Select from a weighted XOR: push down through the sum
    | Just (SemiRingSum s) <- asApp x
    , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.sumRepr s
    = do let mask = maxUnsigned n
         let shft = fromIntegral (natValue idx)
         s' <- WSum.transformSum (SR.SemiRingBVRepr SR.BVBitsRepr n)
                 (\c -> return ((c `Bits.shiftR` shft)  Bits..&. mask))
                 (bvSelect sb idx n)
                 s
         semiRingSum sb s'

    -- Select from a AND: push down through the AND
    | Just (SemiRingProd pd) <- asApp x
    , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr pd
    = do pd' <- WSum.prodEvalM
                   (bvAndBits sb)
                   (bvSelect sb idx n)
                   pd
         maybe (bvLit sb n (maxUnsigned n)) return pd'

    -- Select from an OR: push down through the OR
    | Just (BVOrBits pd) <- asApp x
    = do pd' <- WSum.prodEvalM
                   (bvOrBits sb)
                   (bvSelect sb idx n)
                   pd
         maybe (bvLit sb n 0) return pd'
-}

    -- Truncate from a unary bitvector
    | Just (BVUnaryTerm u) <- asApp x
    , Just Refl <- testEquality idx (knownNat @0) =
      bvUnary sb =<< UnaryBV.trunc sb u n

      -- if none of the above apply, produce a basic select term
    | otherwise = sbMakeExpr sb $ BVSelect idx n x

  testBitBV sym i y
    | i < 0 || i >= natValue (bvWidth y) =
      fail $ "Illegal bit index."

      -- Constant evaluation
    | Just yc <- asUnsignedBV y
    , i <= fromIntegral (maxBound :: Int)
    = return $! backendPred sym (yc `Bits.testBit` fromIntegral i)

    | Just (BVZext _w y') <- asApp y
    = if i >= natValue (bvWidth y') then
        return $ falsePred sym
      else
        testBitBV sym i y'

    | Just (BVSext _w y') <- asApp y
    = if i >= natValue (bvWidth y') then
        testBitBV sym (natValue (bvWidth y') - 1) y'
      else
        testBitBV sym i y'

    | Just (BVFill _ p) <- asApp y
    = return p

    | Just b <- BVD.testBit (bvWidth y) (exprAbsValue y) i
    = return $! backendPred sym b

    | Just (BaseIte _ _ c a b) <- asApp y
    , isJust (asUnsignedBV a) || isJust (asUnsignedBV b) -- NB avoid losing sharing
    = do a' <- testBitBV sym i a
         b' <- testBitBV sym i b
         itePred sym c a' b'

{- These rewrites can sometimes yield significant simplifications, but
   also may lead to loss of sharing, so they are disabled...

    | Just ws <- asSemiRingSum (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth y)) y
    = let smul c x
           | Bits.testBit c (fromIntegral i) = testBitBV sym i x
           | otherwise                       = return (falsePred sym)
          cnst c = return $! backendPred sym (Bits.testBit c (fromIntegral i))
       in WSum.evalM (xorPred sym) smul cnst ws

    | Just pd <- asSemiRingProd (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth y)) y
    = fromMaybe (truePred sym) <$> WSum.prodEvalM (andPred sym) (testBitBV sym i) pd

    | Just (BVOrBits pd) <- asApp y
    = fromMaybe (falsePred sym) <$> WSum.prodEvalM (orPred sym) (testBitBV sym i) pd
-}

    | otherwise = sbMakeExpr sym $ BVTestBit i y

  bvFill sym w p
    | Just True  <- asConstantPred p = bvLit sym w (maxUnsigned w)
    | Just False <- asConstantPred p = bvLit sym w 0
    | otherwise = sbMakeExpr sym $ BVFill w p

  bvIte sym c x y
    | Just (BVFill w px) <- asApp x
    , Just (BVFill _w py) <- asApp y =
      do z <- itePred sym c px py
         bvFill sym w z

    | Just (BVZext w  x') <- asApp x
    , Just (BVZext w' y') <- asApp y
    , Just Refl <- testEquality (bvWidth x') (bvWidth y')
    , Just Refl <- testEquality w w' =
      do z <- bvIte sym c x' y'
         bvZext sym w z

    | Just (BVSext w  x') <- asApp x
    , Just (BVSext w' y') <- asApp y
    , Just Refl <- testEquality (bvWidth x') (bvWidth y')
    , Just Refl <- testEquality w w' =
      do z <- bvIte sym c x' y'
         bvSext sym w z

    | Just (FloatToBinary fpp1 x') <- asApp x
    , Just (FloatToBinary fpp2 y') <- asApp y
    , Just Refl <- testEquality fpp1 fpp2 =
      floatToBinary sym =<< floatIte sym c x' y'

    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           sbTryUnaryTerm sym
             (do ux <- asUnaryBV sym x
                 uy <- asUnaryBV sym y
                 return (UnaryBV.mux sym c ux uy))
             (case inSameBVSemiRing x y of
                Just (Some flv) ->
                  semiRingIte sym (SR.SemiRingBVRepr flv (bvWidth x)) c x y
                Nothing ->
                  mkIte sym c x y)

  bvEq sym x y
    | x == y = return $! truePred sym

    | Just (BVFill _ px) <- asApp x
    , Just (BVFill _ py) <- asApp y =
      eqPred sym px py

    | Just b <- BVD.eq (exprAbsValue x) (exprAbsValue y) = do
      return $! backendPred sym b

    -- Push some equalities under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (BaseIte _ _ c a b) <- asApp y
    = join (itePred sym c <$> bvEq sym x a <*> bvEq sym x b)

    -- Push some equalities under if/then/else
    | Just (BaseIte _ _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    = join (itePred sym c <$> bvEq sym a y <*> bvEq sym b y)

    | Just (Some flv) <- inSameBVSemiRing x y
    , let sr = SR.SemiRingBVRepr flv (bvWidth x)
    , (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z) =
        case (WSum.asConstant x', WSum.asConstant y') of
          (Just a, Just b) -> return $! backendPred sym (SR.eq sr a b)
          _ -> do xr <- semiRingSum sym x'
                  yr <- semiRingSum sym y'
                  sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min xr yr) (max xr yr)

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.eq sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BaseEq (BaseBVRepr (bvWidth x)) (min x y) (max x y)

  bvSlt sym x y
    | Just xc <- asSignedBV x
    , Just yc <- asSignedBV y =
      return $! backendPred sym (xc < yc)
    | Just b <- BVD.slt (bvWidth x) (exprAbsValue x) (exprAbsValue y) =
      return $! backendPred sym b
    | x == y = return (falsePred sym)

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.slt sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BVSlt x y

  bvUlt sym x y
    | Just xc <- asUnsignedBV x
    , Just yc <- asUnsignedBV y = do
      return $! backendPred sym (xc < yc)
    | Just b <- BVD.ult (exprAbsValue x) (exprAbsValue y) =
      return $! backendPred sym b
    | x == y =
      return $! falsePred sym

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.ult sym ux uy

           | otherwise
           -> sbMakeExpr sym $ BVUlt x y

  bvShl sym x y
   -- shift by 0 is the identity function
   | Just 0 <- asUnsignedBV y
   = pure x

   -- shift by more than word width returns 0
   | let (lo, _hi) = BVD.ubounds (exprAbsValue y)
   , lo >= intValue (bvWidth x)
   = bvLit sym (bvWidth x) 0

   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) (Bits.shiftL i (fromIntegral n))

   | otherwise
   = sbMakeExpr sym $ BVShl (bvWidth x) x y

  bvLshr sym x y
   -- shift by 0 is the identity function
   | Just 0 <- asUnsignedBV y
   = pure x

   -- shift by more than word width returns 0
   | let (lo, _hi) = BVD.ubounds (exprAbsValue y)
   , lo >= intValue (bvWidth x)
   = bvLit sym (bvWidth x) 0

   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) $ Bits.shiftR i (fromIntegral n)

   | otherwise
   = sbMakeExpr sym $ BVLshr (bvWidth x) x y

  bvAshr sym x y
   -- shift by 0 is the identity function
   | Just 0 <- asUnsignedBV y
   = pure x

   -- shift by more than word width returns either 0 (if x is nonnegative)
   -- or 1 (if x is negative)
   | let (lo, _hi) = BVD.ubounds (exprAbsValue y)
   , lo >= intValue (bvWidth x)
   = bvFill sym (bvWidth x) =<< bvIsNeg sym x

   | Just i <- asSignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) (Bits.shiftR i (fromIntegral n))

   | otherwise
   = sbMakeExpr sym $ BVAshr (bvWidth x) x y

  bvRol sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) $ rotateLeft (bvWidth x) i n

   | Just n <- asUnsignedBV y
   , n `rem` intValue (bvWidth x) == 0
   = return x

   | Just (BVRol w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvAdd sym n y
        bvRol sym x' z

   | Just (BVRol w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' y'
        bvRol sym x' z

   | Just (BVRor w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvSub sym n y
        bvRor sym x' z

   | Just (BVRor w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        y' <- bvUrem sym y wbv
        n' <- bvUrem sym n wbv
        z <- bvAdd sym n' =<< bvSub sym wbv y'
        bvRor sym x' z

   | otherwise
   = let w = bvWidth x in
     sbMakeExpr sym $ BVRol w x y

  bvRor sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) $ rotateRight (bvWidth x) i n

   | Just n <- asUnsignedBV y
   , n `rem` intValue (bvWidth x) == 0
   = return x

   | Just (BVRor w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvAdd sym n y
        bvRor sym x' z

   | Just (BVRor w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' y'
        bvRor sym x' z

   | Just (BVRol w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvSub sym n y
        bvRol sym x' z

   | Just (BVRol w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' =<< bvSub sym wbv y'
        bvRol sym x' z

   | otherwise
   = let w = bvWidth x in
     sbMakeExpr sym $ BVRor w x y

  bvZext sym w x
    | Just i <- asUnsignedBV x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvLit sym w i

      -- Concatenate unsign extension.
    | Just (BVZext _ y) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym $ BVZext w y

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.uext u w

    | otherwise = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym $ BVZext w x

  bvSext sym w x
    | Just i <- asSignedBV x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvLit sym w i

      -- Concatenate sign extension.
    | Just (BVSext _ y) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym (BVSext w y)

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.sext u w

    | otherwise = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym (BVSext w x)

  bvXorBits sym x y
    | x == y = bvLit sym (bvWidth x) 0  -- special case: x `xor` x = 0
    | otherwise
    = let sr = SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x)
       in semiRingAdd sym sr x y

  bvAndBits sym x y
    | x == y = return x -- Special case: idempotency of and

    | Just (BVOrBits _ bs) <- asApp x
    , bvOrContains y bs
    = return y -- absorption law

    | Just (BVOrBits _ bs) <- asApp y
    , bvOrContains x bs
    = return x -- absorption law

    | otherwise
    = let sr = SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x)
       in semiRingMul sym sr x y

  -- XOR by the all-1 constant of the bitwise semiring.
  -- This is equivalant to negation
  bvNotBits sym x
    | Just i <- asUnsignedBV x
    = bvLit sym (bvWidth x) $ i `Bits.xor` (maxUnsigned (bvWidth x))

    | otherwise
    = let sr = (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x))
       in semiRingSum sym $ WSum.addConstant sr (asWeightedSum sr x) (maxUnsigned (bvWidth x))

  bvOrBits sym x y =
    case (asUnsignedBV x, asUnsignedBV y) of
      (Just xi, Just yi) -> bvLit sym (bvWidth x) (xi Bits..|. yi)
      (Just xi , _)
        | xi == 0 -> return y
        | xi == maxUnsigned (bvWidth x) -> return x
      (_, Just yi)
        | yi == 0 -> return x
        | yi == maxUnsigned (bvWidth x) -> return y

      _
        | x == y
        -> return x -- or is idempotent

        | Just (SemiRingProd xs) <- asApp x
        , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr xs
        , WSum.prodContains xs y
        -> return y   -- absorption law

        | Just (SemiRingProd ys) <- asApp y
        , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr ys
        , WSum.prodContains ys x
        -> return x   -- absorption law

        | Just (BVOrBits w xs) <- asApp x
        , Just (BVOrBits _ ys) <- asApp y
        -> sbMakeExpr sym $ BVOrBits w $ bvOrUnion xs ys

        | Just (BVOrBits w xs) <- asApp x
        -> sbMakeExpr sym $ BVOrBits w $ bvOrInsert y xs

        | Just (BVOrBits w ys) <- asApp y
        -> sbMakeExpr sym $ BVOrBits w $ bvOrInsert x ys

        | otherwise
        -> sbMakeExpr sym $ BVOrBits (bvWidth x) $ bvOrInsert x $ bvOrSingleton y

  bvAdd sym x y = semiRingAdd sym sr x y
     where sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)

  bvMul sym x y = semiRingMul sym sr x y
     where sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)

  bvNeg sym x
    | Just i <- asSignedBV x = bvLit sym (bvWidth x) (-i)
    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           sbTryUnaryTerm sym
             (do ux <- asUnaryBV sym x
                 Just (UnaryBV.neg sym ux))
             (do let sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)
                 scalarMul sym sr (toUnsigned (bvWidth x) (-1)) x)

  bvIsNonzero sym x
    | Just (BaseIte _ _ p t f) <- asApp x
    , isJust (asUnsignedBV t) || isJust (asUnsignedBV f) -- NB, avoid losing possible sharing
    = do  t' <- bvIsNonzero sym t
          f' <- bvIsNonzero sym f
          itePred sym p t' f'
    | Just (BVConcat _ a b) <- asApp x
    , isJust (asUnsignedBV a) || isJust (asUnsignedBV b) -- NB, avoid losing possible sharing
    =  do pa <- bvIsNonzero sym a
          pb <- bvIsNonzero sym b
          orPred sym pa pb
    | Just (BVZext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVSext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVFill _ p) <- asApp x =
          return p
    | Just (BVUnaryTerm ubv) <- asApp x =
          UnaryBV.sym_evaluate
            (\i -> return $! backendPred sym (i/=0))
            (itePred sym)
            ubv
    | otherwise = do
          let w = bvWidth x
          zro <- bvLit sym w 0
          notPred sym =<< bvEq sym x zro

  bvUdiv = bvBinDivOp quot BVUdiv
  bvUrem sym x y
    | Just True <- BVD.ult (exprAbsValue x) (exprAbsValue y) = return x
    | otherwise = bvBinDivOp rem BVUrem sym x y
  bvSdiv = bvSignedBinDivOp quot BVSdiv
  bvSrem = bvSignedBinDivOp rem BVSrem

  bvPopcount sym x
    | Just i <- asUnsignedBV x = bvLit sym w (toInteger (Bits.popCount i))
    | otherwise = sbMakeExpr sym $ BVPopcount w x
   where w = bvWidth x

  bvCountTrailingZeros sym x
    | Just i <- asUnsignedBV x = bvLit sym w (ctz w i)
    | otherwise = sbMakeExpr sym $ BVCountTrailingZeros w x
   where w = bvWidth x

  bvCountLeadingZeros sym x
    | Just i <- asUnsignedBV x = bvLit sym w (clz w i)
    | otherwise = sbMakeExpr sym $ BVCountLeadingZeros w x
   where w = bvWidth x

  mkStruct sym args = do
    sbMakeExpr sym $ StructCtor (fmapFC exprType args) args

  structField sym s i
    | Just (StructCtor _ args) <- asApp s = return $! args Ctx.! i
    | otherwise = do
      case exprType s of
        BaseStructRepr flds ->
          sbMakeExpr sym $ StructField s i (flds Ctx.! i)

  structIte sym p x y
    | Just True  <- asConstantPred p = return x
    | Just False <- asConstantPred p = return y
    | x == y                         = return x
    | otherwise                      = mkIte sym p x y

  --------------------------------------------------------------------
  -- String operations

  stringEmpty sym si = stringLit sym (stringLitEmpty si)

  stringLit sym s =
    do l <- curProgramLoc sym
       return $! StringExpr s l

  stringEq sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (isJust (testEquality x' y'))
  stringEq sym x y
    = sbMakeExpr sym $ BaseEq (BaseStringRepr (stringInfo x)) x y

  stringIte _sym c x y
    | Just c' <- asConstantPred c
    = if c' then return x else return y
  stringIte _sym _c x y
    | Just x' <- asString x
    , Just y' <- asString y
    , isJust (testEquality x' y')
    = return x
  stringIte sym c x y
    = mkIte sym c x y

  stringIndexOf sym x y k
    | Just x' <- asString x
    , Just y' <- asString y
    , Just k' <- asNat k
    = intLit sym $! stringLitIndexOf x' y' k'
  stringIndexOf sym x y k
    = sbMakeExpr sym $ StringIndexOf x y k

  stringContains sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitContains x' y')
    | Just b <- stringAbsContains (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b
    | otherwise
    = sbMakeExpr sym $ StringContains x y

  stringIsPrefixOf sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitIsPrefixOf x' y')

    | Just b <- stringAbsIsPrefixOf (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b

    | otherwise
    = sbMakeExpr sym $ StringIsPrefixOf x y

  stringIsSuffixOf sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitIsSuffixOf x' y')

    | Just b <- stringAbsIsSuffixOf (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b

    | otherwise
    = sbMakeExpr sym $ StringIsSuffixOf x y

  stringSubstring sym x off len
    | Just x' <- asString x
    , Just off' <- asNat off
    , Just len' <- asNat len
    = stringLit sym $! stringLitSubstring x' off' len'

    | otherwise
    = sbMakeExpr sym $ StringSubstring (stringInfo x) x off len

  stringConcat sym x y
    | Just x' <- asString x, stringLitNull x'
    = return y

    | Just y' <- asString y, stringLitNull y'
    = return x

    | Just x' <- asString x
    , Just y' <- asString y
    = stringLit sym (x' <> y')

    | Just (StringAppend si xs) <- asApp x
    , Just (StringAppend _  ys) <- asApp y
    = sbMakeExpr sym $ StringAppend si (SSeq.append xs ys)

    | Just (StringAppend si xs) <- asApp x
    = sbMakeExpr sym $ StringAppend si (SSeq.append xs (SSeq.singleton si y))

    | Just (StringAppend si ys) <- asApp y
    = sbMakeExpr sym $ StringAppend si (SSeq.append (SSeq.singleton si x) ys)

    | otherwise
    = let si = stringInfo x in
      sbMakeExpr sym $ StringAppend si (SSeq.append (SSeq.singleton si x) (SSeq.singleton si y))

  stringLength sym x
    | Just x' <- asString x
    = natLit sym (stringLitLength x')

    | Just (StringAppend _si xs) <- asApp x
    = do let f sm (SSeq.StringSeqLiteral l) = natAdd sym sm =<< natLit sym (stringLitLength l)
             f sm (SSeq.StringSeqTerm t)    = natAdd sym sm =<< sbMakeExpr sym (StringLength t)
         z  <- natLit sym 0
         foldM f z (SSeq.toList xs)

    | otherwise
    = sbMakeExpr sym $ StringLength x

  --------------------------------------------------------------------
  -- Symbolic array operations

  constantArray sym idxRepr v =
    sbMakeExpr sym $ ConstantArray idxRepr (exprType v) v

  arrayFromFn sym fn = do
    sbNonceExpr sym $ ArrayFromFn fn

  arrayMap sym f arrays
      -- Cancel out integerToReal (realToInteger a)
    | Just IntegerToRealFn  <- asMatlabSolverFn f
    , Just (MapOverArrays g _ args) <- asNonceApp (unwrapArrayResult (arrays^._1))
    , Just RealToIntegerFn <- asMatlabSolverFn g =
      return $! unwrapArrayResult (args^._1)
      -- Cancel out realToInteger (integerToReal a)
    | Just RealToIntegerFn  <- asMatlabSolverFn f
    , Just (MapOverArrays g _ args) <- asNonceApp (unwrapArrayResult (arrays^._1))
    , Just IntegerToRealFn <- asMatlabSolverFn g =
      return $! unwrapArrayResult (args^._1)

    -- When the array is an update of concrete entries, map over the entries.
    | s <- concreteArrayEntries arrays
    , not (Set.null s) = do
        -- Distribute over base values.
        --
        -- The underlyingArrayMapElf function strings a top-level arrayMap value.
        --
        -- It is ok because we don't care what the value of base is at any index
        -- in s.
        base <- arrayMap sym f (fmapFC underlyingArrayMapExpr arrays)
        BaseArrayRepr _ ret <- return (exprType base)

        -- This lookups a given index in an array used as an argument.
        let evalArgs :: Ctx.Assignment IndexLit (idx ::> itp)
                        -- ^ A representatio of the concrete index (if defined).
                        -> Ctx.Assignment (Expr t)  (idx ::> itp)
                           -- ^ The index to use.
                        -> ArrayResultWrapper (Expr t) (idx ::> itp) d
                           -- ^ The array to get the value at.
                        -> IO (Expr t d)
            evalArgs const_idx sym_idx a = do
              sbConcreteLookup sym (unwrapArrayResult a) (Just const_idx) sym_idx
        let evalIndex :: ExprSymFn t (Expr t) ctx ret
                      -> Ctx.Assignment (ArrayResultWrapper (Expr t) (i::>itp)) ctx
                      -> Ctx.Assignment IndexLit (i::>itp)
                      -> IO (Expr t ret)
            evalIndex g arrays0 const_idx = do
              sym_idx <- traverseFC (indexLit sym) const_idx
              applySymFn sym g =<< traverseFC (evalArgs const_idx sym_idx) arrays0
        m <- AUM.fromAscList ret <$> mapM (\k -> (k,) <$> evalIndex f arrays k) (Set.toAscList s)
        arrayUpdateAtIdxLits sym m base
      -- When entries are constants, then just evaluate constant.
    | Just cns <-  traverseFC (\a -> asConstantArray (unwrapArrayResult a)) arrays = do
      r <- betaReduce sym f cns
      case exprType (unwrapArrayResult (Ctx.last arrays)) of
        BaseArrayRepr idxRepr _ -> do
          constantArray sym idxRepr r

    | otherwise = do
      let idx = arrayResultIdxType (exprType (unwrapArrayResult (Ctx.last arrays)))
      sbNonceExpr sym $ MapOverArrays f idx arrays

  arrayUpdate sym arr i v
      -- Update at concrete index.
    | Just ci <- asConcreteIndices i =
      case asApp arr of
        Just (ArrayMap idx tp m def) -> do
          let new_map =
                case asApp def of
                  Just (ConstantArray _ _ cns) | v == cns -> AUM.delete ci m
                  _ -> AUM.insert tp ci v m
          sbMakeExpr sym $ ArrayMap idx tp new_map def
        _ -> do
          let idx = fmapFC exprType  i
          let bRepr = exprType v
          let new_map = AUM.singleton bRepr ci v
          sbMakeExpr sym $ ArrayMap idx bRepr new_map arr
    | otherwise = do
      let bRepr = exprType v
      sbMakeExpr sym (UpdateArray bRepr (fmapFC exprType i)  arr i v)

  arrayLookup sym arr idx =
    sbConcreteLookup sym arr (asConcreteIndices idx) idx

  -- | Create an array from a map of concrete indices to values.
  arrayUpdateAtIdxLits sym m def_map = do
    BaseArrayRepr idx_tps baseRepr <- return $ exprType def_map
    let new_map
          | Just (ConstantArray _ _ default_value) <- asApp def_map =
            AUM.filter (/= default_value) m
          | otherwise = m
    if AUM.null new_map then
      return def_map
     else
      sbMakeExpr sym $ ArrayMap idx_tps baseRepr new_map def_map

  arrayIte sym p x y
       -- Extract all concrete updates out.
     | ArrayMapView mx x' <- viewArrayMap x
     , ArrayMapView my y' <- viewArrayMap y
     , not (AUM.null mx) || not (AUM.null my) = do
       case exprType x of
         BaseArrayRepr idxRepr bRepr -> do
           let both_fn _ u v = baseTypeIte sym p u v
               left_fn idx u = do
                 v <- sbConcreteLookup sym y' (Just idx) =<< symbolicIndices sym idx
                 both_fn idx u v
               right_fn idx v = do
                 u <- sbConcreteLookup sym x' (Just idx) =<< symbolicIndices sym idx
                 both_fn idx u v
           mz <- AUM.mergeM bRepr both_fn left_fn right_fn mx my
           z' <- arrayIte sym p x' y'

           sbMakeExpr sym $ ArrayMap idxRepr bRepr mz z'

     | otherwise = mkIte sym p x y

  arrayEq sym x y
    | x == y =
      return $! truePred sym
    | otherwise =
      sbMakeExpr sym $! BaseEq (exprType x) x y

  arrayTrueOnEntries sym f a
    | Just True <- exprAbsValue a =
      return $ truePred sym
    | Just (IndicesInRange _ bnds) <- asMatlabSolverFn f
    , Just v <- asNatBounds bnds = do
      let h :: Expr t (BaseArrayType (i::>it) BaseBoolType)
            -> BoolExpr t
            -> Ctx.Assignment (Expr t) (i::>it)
            -> IO (BoolExpr t)
          h a0 p i = andPred sym p =<< arrayLookup sym a0 i
      foldIndicesInRangeBounds sym (h a) (truePred sym) v

    | otherwise =
      sbNonceExpr sym $! ArrayTrueOnEntries f a

  ----------------------------------------------------------------------
  -- Lossless (injective) conversions

  natToInteger sym x
    | SemiRingLiteral SR.SemiRingNatRepr n l <- x = return $! SemiRingLiteral SR.SemiRingIntegerRepr (toInteger n) l
    | Just (IntegerToNat y) <- asApp x = return y
    | otherwise = sbMakeExpr sym (NatToInteger x)

  integerToNat sb x
    | SemiRingLiteral SR.SemiRingIntegerRepr i l <- x
    , 0 <= i
    = return $! SemiRingLiteral SR.SemiRingNatRepr (fromIntegral i) l
    | Just (NatToInteger y) <- asApp x = return y
    | otherwise =
      sbMakeExpr sb (IntegerToNat x)

  integerToReal sym x
    | SemiRingLiteral SR.SemiRingIntegerRepr i l <- x = return $! SemiRingLiteral SR.SemiRingRealRepr (toRational i) l
    | Just (RealToInteger y) <- asApp x = return y
    | otherwise  = sbMakeExpr sym (IntegerToReal x)

  realToInteger sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $! SemiRingLiteral SR.SemiRingIntegerRepr (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | otherwise =
      sbMakeExpr sym (RealToInteger x)

  bvToNat sym x
    | Just i <- asUnsignedBV x =
      natLit sym (fromInteger i)
    | otherwise = sbMakeExpr sym (BVToNat x)

  bvToInteger sym x
    | Just i <- asUnsignedBV x =
      intLit sym i
      -- bvToInteger (integerToBv x w) == mod x (2^w)
    | Just (IntegerToBV xi w) <- asApp x =
      intMod sym xi =<< intLit sym (2^natValue w)
    | otherwise =
      sbMakeExpr sym (BVToInteger x)

  sbvToInteger sym x
    | Just i <- asSignedBV x =
      intLit sym i
      -- sbvToInteger (integerToBv x w) == mod (x + 2^(w-1)) (2^w) - 2^(w-1)
    | Just (IntegerToBV xi w) <- asApp x =
      do halfmod <- intLit sym (2 ^ (natValue w - 1))
         modulus <- intLit sym (2 ^ natValue w)
         x'      <- intAdd sym xi halfmod
         z       <- intMod sym x' modulus
         intSub sym z halfmod
    | otherwise =
      sbMakeExpr sym (SBVToInteger x)

  predToBV sym p w
    | Just b <- asConstantPred p =
        if b then bvLit sym w 1 else bvLit sym w 0
    | otherwise =
       case compareNat w (knownNat @1) of
         NatEQ   -> sbMakeExpr sym (BVFill (knownNat @1) p)
         NatGT _ -> bvZext sym w =<< sbMakeExpr sym (BVFill (knownNat @1) p)
         NatLT _ -> fail "impossible case in predToBV"

  integerToBV sym xr w
    | SemiRingLiteral SR.SemiRingIntegerRepr i _ <- xr =
      bvLit sym w i

    | Just (BVToInteger r) <- asApp xr =
      case compareNat (bvWidth r) w of
        NatLT _ -> bvZext sym w r
        NatEQ   -> return r
        NatGT _ -> bvTrunc sym w r

    | Just (SBVToInteger r) <- asApp xr =
      case compareNat (bvWidth r) w of
        NatLT _ -> bvSext sym w r
        NatEQ   -> return r
        NatGT _ -> bvTrunc sym w r

    | otherwise =
      sbMakeExpr sym (IntegerToBV xr w)

  realRound sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (roundAway r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (RoundReal x)

  realFloor sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (FloorReal x)

  realCeil sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (ceiling r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (CeilReal x)

  ----------------------------------------------------------------------
  -- Real operations

  realLit sb r = do
    l <- curProgramLoc sb
    return (SemiRingLiteral SR.SemiRingRealRepr r l)

  realZero = sbZero

  realEq sym x y
      -- Use range check
    | Just b <- ravCheckEq (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to integer equality, when possible
    | Just (IntegerToReal xi) <- asApp x
    , Just (IntegerToReal yi) <- asApp y
    = intEq sym xi yi

    | Just (IntegerToReal xi) <- asApp x
    , SemiRingLiteral SR.SemiRingRealRepr yr _ <- y
    = if denominator yr == 1
         then intEq sym xi =<< intLit sym (numerator yr)
         else return (falsePred sym)

    | SemiRingLiteral SR.SemiRingRealRepr xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = if denominator xr == 1
         then intEq sym yi =<< intLit sym (numerator xr)
         else return (falsePred sym)

    | otherwise
    = semiRingEq sym SR.SemiRingRealRepr (realEq sym) x y

  realLe sym x y
      -- Use range check
    | Just b <- ravCheckLe (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to integer inequality, when possible
    | Just (IntegerToReal xi) <- asApp x
    , Just (IntegerToReal yi) <- asApp y
    = intLe sym xi yi

      -- if the upper range is a constant, do an integer comparison
      -- with @floor(y)@
    | Just (IntegerToReal xi) <- asApp x
    , SemiRingLiteral SR.SemiRingRealRepr yr _ <- y
    = join (intLe sym <$> pure xi <*> intLit sym (floor yr))

      -- if the lower range is a constant, do an integer comparison
      -- with @ceiling(x)@
    | SemiRingLiteral SR.SemiRingRealRepr xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = join (intLe sym <$> intLit sym (ceiling xr) <*> pure yi)

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingRealRepr (realLe sym) x y

  realIte sym c x y = semiRingIte sym SR.SemiRingRealRepr c x y

  realNeg sym x = scalarMul sym SR.SemiRingRealRepr (-1) x

  realAdd sym x y = semiRingAdd sym SR.SemiRingRealRepr x y

  realMul sym x y = semiRingMul sym SR.SemiRingRealRepr x y

  realDiv sym x y
    | Just 0 <- asRational x =
      return x
    | Just xd <- asRational x, Just yd <- asRational y, yd /= 0 = do
      realLit sym (xd / yd)
      -- Handle division by a constant.
    | Just yd <- asRational y, yd /= 0 = do
      scalarMul sym SR.SemiRingRealRepr (1 / yd) x
    | otherwise =
      sbMakeExpr sym $ RealDiv x y

  isInteger sb x
    | Just r <- asRational x = return $ backendPred sb (denominator r == 1)
    | Just b <- ravIsInteger (exprAbsValue x) = return $ backendPred sb b
    | otherwise = sbMakeExpr sb $ RealIsInteger x

  realSqrt sym x = do
    let sqrt_dbl :: Double -> Double
        sqrt_dbl = sqrt
    case x of
      SemiRingLiteral SR.SemiRingRealRepr r _
        | r <= 0 -> realLit sym 0
        | Just w <- tryRationalSqrt r -> realLit sym w
        | sbFloatReduce sym -> realLit sym (toRational (sqrt_dbl (fromRational r)))
      _ -> sbMakeExpr sym (RealSqrt x)

  realPi sym = do
    if sbFloatReduce sym then
      realLit sym (toRational (pi :: Double))
     else
      sbMakeExpr sym Pi

  realSin sym x =
    case asRational x of
      Just 0 -> realLit sym 0
      Just c | sbFloatReduce sym -> realLit sym (toRational (sin (toDouble c)))
      _ -> sbMakeExpr sym (RealSin x)

  realCos sym x =
    case asRational x of
      Just 0 -> realLit sym 1
      Just c | sbFloatReduce sym -> realLit sym (toRational (cos (toDouble c)))
      _ -> sbMakeExpr sym (RealCos x)

  realAtan2 sb y x = do
    case (asRational y, asRational x) of
      (Just 0, _) -> realLit sb 0
      (Just yc, Just xc) | sbFloatReduce sb -> do
        realLit sb (toRational (atan2 (toDouble yc) (toDouble xc)))
      _ -> sbMakeExpr sb (RealATan2 y x)

  realSinh sb x =
    case asRational x of
      Just 0 -> realLit sb 0
      Just c | sbFloatReduce sb -> realLit sb (toRational (sinh (toDouble c)))
      _ -> sbMakeExpr sb (RealSinh x)

  realCosh sb x =
    case asRational x of
      Just 0 -> realLit sb 1
      Just c | sbFloatReduce sb -> realLit sb (toRational (cosh (toDouble c)))
      _ -> sbMakeExpr sb (RealCosh x)

  realExp sym x
    | Just 0 <- asRational x = realLit sym 1
    | Just c <- asRational x, sbFloatReduce sym = realLit sym (toRational (exp (toDouble c)))
    | otherwise = sbMakeExpr sym (RealExp x)

  realLog sym x =
    case asRational x of
      Just c | sbFloatReduce sym -> realLit sym (toRational (log (toDouble c)))
      _ -> sbMakeExpr sym (RealLog x)

  ----------------------------------------------------------------------
  -- IEEE-754 floating-point operations
  floatPZero = floatIEEEArithCt FloatPZero
  floatNZero = floatIEEEArithCt FloatNZero
  floatNaN = floatIEEEArithCt FloatNaN
  floatPInf = floatIEEEArithCt FloatPInf
  floatNInf = floatIEEEArithCt FloatNInf
  floatLit sym fpp x = realToFloat sym fpp RNE =<< realLit sym x
  floatNeg = floatIEEEArithUnOp FloatNeg
  floatAbs = floatIEEEArithUnOp FloatAbs
  floatSqrt = floatIEEEArithUnOpR FloatSqrt
  floatAdd = floatIEEEArithBinOpR FloatAdd
  floatSub = floatIEEEArithBinOpR FloatSub
  floatMul = floatIEEEArithBinOpR FloatMul
  floatDiv = floatIEEEArithBinOpR FloatDiv
  floatRem = floatIEEEArithBinOp FloatRem
  floatMin = floatIEEEArithBinOp FloatMin
  floatMax = floatIEEEArithBinOp FloatMax
  floatFMA sym r x y z =
    let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ FloatFMA fpp r x y z
  floatEq sym x y
    | x == y = return $! truePred sym
    | otherwise = floatIEEELogicBinOp (BaseEq (exprType x)) sym x y
  floatNe sym x y = notPred sym =<< floatEq sym x y
  floatFpEq sym x y
    | x == y = notPred sym =<< floatIsNaN sym x
    | otherwise = floatIEEELogicBinOp FloatFpEq sym x y
  floatFpNe sym x y
    | x == y = return $ falsePred sym
    | otherwise = floatIEEELogicBinOp FloatFpNe sym x y
  floatLe sym x y
    | x == y = notPred sym =<< floatIsNaN sym x
    | otherwise = floatIEEELogicBinOp FloatLe sym x y
  floatLt sym x y
    | x == y = return $ falsePred sym
    | otherwise = floatIEEELogicBinOp FloatLt sym x y
  floatGe sym x y = floatLe sym y x
  floatGt sym x y = floatLt sym y x
  floatIte sym c x y = mkIte sym c x y
  floatIsNaN = floatIEEELogicUnOp FloatIsNaN
  floatIsInf = floatIEEELogicUnOp FloatIsInf
  floatIsZero = floatIEEELogicUnOp FloatIsZero
  floatIsPos = floatIEEELogicUnOp FloatIsPos
  floatIsNeg = floatIEEELogicUnOp FloatIsNeg
  floatIsSubnorm = floatIEEELogicUnOp FloatIsSubnorm
  floatIsNorm = floatIEEELogicUnOp FloatIsNorm
  floatCast sym fpp r x
    | FloatingPointPrecisionRepr eb sb <- fpp
    , Just (FloatCast (FloatingPointPrecisionRepr eb' sb') _ fval) <- asApp x
    , natValue eb <= natValue eb'
    , natValue sb <= natValue sb'
    , Just Refl <- testEquality (BaseFloatRepr fpp) (exprType fval)
    = return fval
    | otherwise = sbMakeExpr sym $ FloatCast fpp r x
  floatRound = floatIEEEArithUnOpR FloatRound
  floatFromBinary sym fpp x
    | Just (FloatToBinary fpp' fval) <- asApp x
    , Just Refl <- testEquality fpp fpp'
    = return fval
    | otherwise = sbMakeExpr sym $ FloatFromBinary fpp x
  floatToBinary sym x = case exprType x of
    BaseFloatRepr fpp | LeqProof <- lemmaFloatPrecisionIsPos fpp ->
      sbMakeExpr sym $ FloatToBinary fpp x
  bvToFloat sym fpp r = sbMakeExpr sym . BVToFloat fpp r
  sbvToFloat sym fpp r = sbMakeExpr sym . SBVToFloat fpp r
  realToFloat sym fpp r = sbMakeExpr sym . RealToFloat fpp r
  floatToBV sym w r = sbMakeExpr sym . FloatToBV w r
  floatToSBV sym w r = sbMakeExpr sym . FloatToSBV w r
  floatToReal sym = sbMakeExpr sym . FloatToReal

  ----------------------------------------------------------------------
  -- Cplx operations

  mkComplex sym c = sbMakeExpr sym (Cplx c)

  getRealPart _ e
    | Just (Cplx (r :+ _)) <- asApp e = return r
  getRealPart sym x =
    sbMakeExpr sym (RealPart x)

  getImagPart _ e
    | Just (Cplx (_ :+ i)) <- asApp e = return i
  getImagPart sym x =
    sbMakeExpr sym (ImagPart x)

  cplxGetParts _ e
    | Just (Cplx c) <- asApp e = return c
  cplxGetParts sym x =
    (:+) <$> sbMakeExpr sym (RealPart x)
         <*> sbMakeExpr sym (ImagPart x)



inSameBVSemiRing :: Expr t (BaseBVType w) -> Expr t (BaseBVType w) -> Maybe (Some SR.BVFlavorRepr)
inSameBVSemiRing x y
  | Just (SemiRingSum s1) <- asApp x
  , Just (SemiRingSum s2) <- asApp y
  , SR.SemiRingBVRepr flv1 _w <- WSum.sumRepr s1
  , SR.SemiRingBVRepr flv2 _w <- WSum.sumRepr s2
  , Just Refl <- testEquality flv1 flv2
  = Just (Some flv1)

  | otherwise
  = Nothing

floatIEEEArithBinOp
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> e (BaseFloatType fpp)
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithBinOp ctor sym x y =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp x y
floatIEEEArithBinOpR
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> RoundingMode
     -> e (BaseFloatType fpp)
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st
  -> RoundingMode
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithBinOpR ctor sym r x y =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp r x y
floatIEEEArithUnOp
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithUnOp ctor sym x =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp x
floatIEEEArithUnOpR
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> RoundingMode
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st
  -> RoundingMode
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithUnOpR ctor sym r x =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp r x
floatIEEEArithCt
  :: (e ~ Expr t)
  => (FloatPrecisionRepr fpp -> App e (BaseFloatType fpp))
  -> ExprBuilder t st
  -> FloatPrecisionRepr fpp
  -> IO (e (BaseFloatType fpp))
floatIEEEArithCt ctor sym fpp = sbMakeExpr sym $ ctor fpp
floatIEEELogicBinOp
  :: (e ~ Expr t)
  => (e (BaseFloatType fpp) -> e (BaseFloatType fpp) -> App e BaseBoolType)
  -> ExprBuilder t st
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e BaseBoolType)
floatIEEELogicBinOp ctor sym x y = sbMakeExpr sym $ ctor x y
floatIEEELogicUnOp
  :: (e ~ Expr t)
  => (e (BaseFloatType fpp) -> App e BaseBoolType)
  -> ExprBuilder t st
  -> e (BaseFloatType fpp)
  -> IO (e BaseBoolType)
floatIEEELogicUnOp ctor sym x = sbMakeExpr sym $ ctor x




instance IsSymExprBuilder (ExprBuilder t st) where
  freshConstant sym nm tp = do
    v <- sbMakeBoundVar sym nm tp UninterpVarKind Nothing
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarExpr v

  freshBoundedBV sym nm w Nothing Nothing = freshConstant sym nm (BaseBVRepr w)
  freshBoundedBV sym nm w mlo mhi =
    do v <- sbMakeBoundVar sym nm (BaseBVRepr w) UninterpVarKind (Just $! (BVD.range w lo hi))
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   lo = maybe (minUnsigned w) toInteger mlo
   hi = maybe (maxUnsigned w) toInteger mhi

  freshBoundedSBV sym nm w Nothing Nothing = freshConstant sym nm (BaseBVRepr w)
  freshBoundedSBV sym nm w mlo mhi =
    do v <- sbMakeBoundVar sym nm (BaseBVRepr w) UninterpVarKind (Just $! (BVD.range w lo hi))
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   lo = fromMaybe (minSigned w) mlo
   hi = fromMaybe (maxSigned w) mhi

  freshBoundedInt sym nm mlo mhi =
    do v <- sbMakeBoundVar sym nm BaseIntegerRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! MultiRange (Inclusive lo) Unbounded
   absVal Nothing (Just hi) = Just $! MultiRange Unbounded (Inclusive hi)
   absVal (Just lo) (Just hi) = Just $! MultiRange (Inclusive lo) (Inclusive hi)

  freshBoundedReal sym nm mlo mhi =
    do v <- sbMakeBoundVar sym nm BaseRealRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! RAV (MultiRange (Inclusive lo) Unbounded) Nothing
   absVal Nothing (Just hi) = Just $! RAV (MultiRange Unbounded (Inclusive hi)) Nothing
   absVal (Just lo) (Just hi) = Just $! RAV (MultiRange (Inclusive lo) (Inclusive hi)) Nothing

  freshBoundedNat sym nm mlo mhi =
    do v <- sbMakeBoundVar sym nm BaseNatRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! natRange lo Unbounded
   absVal Nothing (Just hi) = Just $! natRange 0 (Inclusive hi)
   absVal (Just lo) (Just hi) = Just $! natRange lo (Inclusive hi)

  freshLatch sym nm tp = do
    v <- sbMakeBoundVar sym nm tp LatchVarKind Nothing
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarExpr v

  freshBoundVar sym nm tp =
    sbMakeBoundVar sym nm tp QuantifierVarKind Nothing

  varExpr _ = BoundVarExpr

  forallPred sym bv e = sbNonceExpr sym $ Forall bv e

  existsPred sym bv e = sbNonceExpr sym $ Exists bv e

  ----------------------------------------------------------------------
  -- SymFn operations.

  -- | Create a function defined in terms of previous functions.
  definedFn sym fn_name bound_vars result policy = do
    l <- curProgramLoc sym
    n <- sbFreshSymFnNonce sym
    let fn = ExprSymFn { symFnId   = n
                         , symFnName = fn_name
                         , symFnInfo = DefinedFnInfo bound_vars result policy
                         , symFnLoc  = l
                         }
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  freshTotalUninterpFn sym fn_name arg_types ret_type = do
    n <- sbFreshSymFnNonce sym
    l <- curProgramLoc sym
    let fn = ExprSymFn { symFnId = n
                         , symFnName = fn_name
                         , symFnInfo = UninterpFnInfo arg_types ret_type
                         , symFnLoc = l
                         }
    seq fn $ do
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  asFnApp _ x =
    case asNonceApp x of
      Just (FnApp fn args) -> SomeFnApp fn args
      _ -> NoFnApp 

  applySymFn sym fn args = do
   case symFnInfo fn of
     DefinedFnInfo bound_vars e policy
       | shouldUnfold policy args ->
           evalBoundVars sym e bound_vars args
     MatlabSolverFnInfo f _ _ -> do
       evalMatlabSolverFn f sym args
     _ -> sbNonceExpr sym $! FnApp fn args

  symFnByName sym name arg_types ret_type =
    cachedUninterpFn sym name arg_types ret_type freshTotalUninterpFn

--------------------------------------------------------------------------------
-- MatlabSymbolicArrayBuilder instance

instance MatlabSymbolicArrayBuilder (ExprBuilder t st) where
  mkMatlabSolverFn sym fn_id = do
    let key = MatlabFnWrapper fn_id
    mr <- stToIO $ PH.lookup (sbMatlabFnCache sym) key
    case mr of
      Just (ExprSymFnWrapper f) -> return f
      Nothing -> do
        let tps = matlabSolverArgTypes fn_id
        vars <- traverseFC (freshBoundVar sym emptySymbol) tps
        r <- evalMatlabSolverFn fn_id sym (fmapFC BoundVarExpr vars)
        l <- curProgramLoc sym
        n <- sbFreshSymFnNonce sym
        let f = ExprSymFn { symFnId   = n
                            , symFnName = emptySymbol
                            , symFnInfo = MatlabSolverFnInfo fn_id vars r
                            , symFnLoc  = l
                            }
        updateVarBinding sym emptySymbol (FnSymbolBinding f)
        stToIO $ PH.insert (sbMatlabFnCache sym) key (ExprSymFnWrapper f)
        return f

cachedUninterpFn
  :: (sym ~ ExprBuilder t st)
  => sym
  -> String
  -> Ctx.Assignment BaseTypeRepr args
  -> BaseTypeRepr ret
  -> (  sym
     -> SolverSymbol
     -> Ctx.Assignment BaseTypeRepr args
     -> BaseTypeRepr ret
     -> IO (SymFn sym args ret)
     )
  -> IO (SymFn sym args ret)
cachedUninterpFn sym fn_name arg_types ret_type handler = do
  fn_cache <- readIORef $ sbUninterpFnCache sym
  case Map.lookup fn_key fn_cache of
    Just (SomeSymFn fn)
      | Just Refl <- testEquality (fnArgTypes fn) arg_types
      , Just Refl <- testEquality (fnReturnType fn) ret_type
      -> return fn
      | otherwise
      -> fail "Duplicate uninterpreted function declaration."
    Nothing -> do
      fn <- handler sym fn_symbol arg_types ret_type
      modifyIORef' (sbUninterpFnCache sym) (Map.insert fn_key (SomeSymFn fn))
      return fn
  where
  fn_key = (fn_symbol, Some (arg_types Ctx.:> ret_type))
  fn_symbol = systemSymbol ("fn!"++fn_name)


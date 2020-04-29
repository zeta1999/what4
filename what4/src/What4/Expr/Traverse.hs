{-|
Module      : What4.Expr.Traverse
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : rdockins@galois.com

This module provides utility operations for traversing What4 terms.
It is very important that term evaluation functions are memoized,
otherwise it is easy to accidentally fall into exponential slowdowns
as shared subterms are reevalauted many times.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.Traverse
  ( -- * IdxCache
    IdxCache
  , newIdxCache
  , lookupIdx
  , lookupIdxValue
  , insertIdxValue
  , deleteIdxValue
  , clearIdxCache
  , idxCacheEval
  , idxCacheEval'

    -- * Term traversal
  , memoTraversal
  , traverseExpr
  ) where

import           Control.Monad.IO.Class
import           Data.IORef
import           Data.Kind
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Map as PM

import What4.BaseTypes
import What4.Expr.Builder

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


-- | Traverse an expression and memoize intermediate results.
traverseExpr ::
  MonadIO m =>
  Expr t tp {- ^ The term to traverse -}->
  ((Expr t tp -> m (f tp)) -> Expr t tp -> m (f tp)) {- ^ the traversal action -} ->
  m (f tp)
traverseExpr e action =
  do f <- memoTraversal action
     f e

-- | Memoize the result of a term traversal.  Use this
--   combinator if the same traversal will be applied to
--   several terms and it is desirable to share intermediate
--   evaluations.  Calls to the returned evaluation function
--   will share the same memo table.
memoTraversal ::
  MonadIO m =>
  ((Expr t tp -> m (f tp)) -> Expr t tp -> m (f tp)) {- ^ the traversal action -} ->
  m (Expr t tp -> m (f tp))
memoTraversal action =
  do cache <- liftIO newIdxCache
     return (doEval cache)

 where
 doEval cache e =
   case exprMaybeId e of
     Nothing -> action (doEval cache) e
     Just e_id -> idxCacheEval' cache e_id (action (doEval cache) e)

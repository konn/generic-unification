{-# LANGUAGE AllowAmbiguousTypes, DataKinds, DeriveFoldable, DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric, DeriveTraversable, DerivingStrategies          #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, InstanceSigs   #-}
{-# LANGUAGE KindSignatures, LambdaCase, ScopedTypeVariables               #-}
{-# LANGUAGE TemplateHaskell, TypeApplications, TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances                                          #-}
module Data.Unification.Variable
  ( Variable(..), emptyTable, OrdVar(..), substitute
  ) where
import           Control.Arrow        (first)
import           Data.Coerce          (coerce)
import           Data.Deriving.Via
import           Data.Functor.Classes
import           Data.Functor.Compose
import           Data.Hashable        (Hashable)
import qualified Data.HashMap.Strict  as HM
import qualified Data.IntMap.Strict   as IM
import           Data.Kind
import qualified Data.Map.Strict      as M
import           Data.Maybe           (maybeToList)
import           Data.Proxy           (Proxy (..))
import           GHC.Generics         (Generic)
import           Prelude              hiding (lookup)

class Traversable (Table v) => Variable v where
  type Table v :: * -> *
  emptyTable' :: Proxy v ->  Table v a
  singleton  :: v -> a -> Table v a
  insert     :: v -> a -> Table v a -> Table v a
  lookup     :: v -> Table v a -> Maybe a
  fromList   :: forall a. [(v, a)] -> Table v a
  fromList   = foldr (uncurry insert) (emptyTable @v @a)
  {-# INLINE fromList #-}
  toList :: Table v a -> [(v, a)]

emptyTable :: forall v a. Variable v => Table v a
emptyTable = emptyTable' (Proxy @v)
{-# INLINE emptyTable #-}

newtype OrdVar v = OrdVar { runOrdVar :: v }
  deriving (Ord, Eq, Generic)

instance (Ord v) => Variable (OrdVar v) where
  type Table (OrdVar v) = M.Map v
  emptyTable' _ = M.empty
  {-# INLINE emptyTable' #-}
  singleton = M.singleton . runOrdVar
  {-# INLINE singleton #-}
  insert = M.insert . runOrdVar
  {-# INLINE insert #-}
  lookup = M.lookup . runOrdVar
  {-# INLINE lookup #-}
  fromList = M.fromList . coerce
  {-# INLINE fromList #-}
  toList = coerce . M.toList
  {-# INLINE toList #-}

instance Variable Int where
  type Table Int = IM.IntMap
  emptyTable' _ = IM.empty
  {-# INLINE emptyTable' #-}
  singleton = IM.singleton
  {-# INLINE singleton #-}
  insert = IM.insert
  {-# INLINE insert #-}
  lookup = IM.lookup
  {-# INLINE lookup #-}
  fromList = IM.fromList
  {-# INLINE fromList #-}
  toList = IM.toList
  {-# INLINE toList #-}

newtype HashVar v = HashVar { runHashVar :: v }
  deriving (Eq, Generic)
  deriving newtype (Hashable)

instance (Eq v, Hashable v) => Variable (HashVar v) where
  type Table (HashVar v) = HM.HashMap v
  emptyTable' _ = HM.empty
  {-# INLINE emptyTable' #-}
  singleton = HM.singleton . runHashVar
  {-# INLINE singleton #-}
  insert = HM.insert . runHashVar
  {-# INLINE insert #-}
  lookup = HM.lookup . runHashVar
  {-# INLINE lookup #-}
  fromList = HM.fromList . coerce
  {-# INLINE fromList #-}
  toList = coerce . HM.toList
  {-# INLINE toList #-}

newtype BoolDic a = BoolDic (Maybe a, Maybe a)
  deriving (Read, Show, Eq, Ord, Foldable, Functor, Traversable)

instance Show1 BoolDic where
  liftShowsPrec s _ d (BoolDic (a, b)) =
    showParen (d > 9) $
      showString "BoolDic ("
    . maybe id ((showString "False -> " .) . s 10) a
    . maybe id ((showString ", True -> " .) . s 10) b
    . showChar ')'

instance Variable Bool where
  type Table Bool = BoolDic
  emptyTable' _ = BoolDic (Nothing, Nothing)
  {-# INLINE emptyTable' #-}
  singleton False a = BoolDic (Just a, Nothing)
  singleton True  a = BoolDic (Nothing, Just a)
  {-# INLINE singleton #-}
  insert False a (BoolDic (_, c)) = BoolDic (Just a, c)
  insert True  a (BoolDic (c, _)) = BoolDic (c, Just a)
  {-# INLINE insert #-}
  lookup False (BoolDic (a, _)) = a
  lookup True  (BoolDic (_, a)) = a
  {-# INLINE lookup #-}
  toList (BoolDic (a, b)) =
    maybe id ((:) . (,) False) a $ maybe [] ((:[]) . (,) True) b
  {-# INLINE toList #-}

instance Variable () where
  type Table () = Maybe
  emptyTable' _ = Nothing
  {-# INLINE emptyTable' #-}
  singleton = const Just
  {-# INLINE singleton #-}
  insert _ a = const $ Just a
  {-# INLINE insert #-}
  lookup _ c = c
  {-# INLINE lookup #-}
  toList = maybeToList . fmap ((,) ())
  {-# INLINE toList #-}

type family ProdTable (vs :: [Type]) where
  ProdTable '[v]      = Table v
  ProdTable (x ': vs) = Compose (Table x) (ProdTable vs)

instance (Variable a, Variable b) => Variable (a, b) where
  type Table (a, b) = ProdTable '[a, b]
  emptyTable' _ = Compose $ emptyTable @a
  {-# INLINE emptyTable' #-}
  singleton (a, b) v = Compose $ singleton a $ singleton b v
  {-# INLINE singleton #-}
  insert (a, b) v (Compose dic) =
    case lookup a dic of
      Nothing   -> Compose $ insert a (singleton b v) dic
      Just bDic -> Compose $ insert a (insert b v bDic) dic
  {-# INLINE insert #-}
  lookup (a, b) (Compose dic) = lookup b =<< lookup a dic
  {-# INLINE lookup #-}
  toList (Compose dic) =
    [ ((a, b), v)
    | (a, aDic) <- toList dic
    , (b, v) <- toList aDic
    ]
  {-# INLINE toList #-}

instance (Variable a, Variable b, Variable c) => Variable (a, b, c) where
  type Table (a, b, c) = ProdTable '[a, b, c]
  emptyTable' _ = Compose $ emptyTable @a
  {-# INLINE emptyTable' #-}
  singleton (a, b, c) v = Compose $ singleton a $ singleton (b, c) v
  {-# INLINE singleton #-}
  insert (a, b, c) v (Compose dic) =
    case lookup a dic of
      Nothing   -> Compose $ insert a (singleton (b, c) v) dic
      Just aDic -> Compose $ insert a (insert (b, c) v aDic) dic
  {-# INLINE insert #-}
  lookup (a, b, c) (Compose dic) = lookup (b, c) =<< lookup a dic
  {-# INLINE lookup #-}
  toList (Compose dic) =
    [ ((a, b, c), v)
    | (a, aDic) <- toList dic
    , ((b, c), v) <- toList aDic
    ]
  {-# INLINE toList #-}

instance (Variable a, Variable b, Variable c, Variable d)
      => Variable (a, b, c, d) where
  type Table (a, b, c, d) = ProdTable '[a, b, c, d]
  emptyTable' _ = Compose $ emptyTable @a
  {-# INLINE emptyTable' #-}
  singleton (a, b, c, d) v = Compose $ singleton a $ singleton (b, c, d) v
  {-# INLINE singleton #-}
  insert (a, b, c, d) v (Compose dic) =
    case lookup a dic of
      Nothing   -> Compose $ insert a (singleton (b, c, d) v) dic
      Just aDic -> Compose $ insert a (insert (b, c, d) v aDic) dic
  {-# INLINE insert #-}
  lookup (a, b, c, d) (Compose dic) = lookup (b, c, d) =<< lookup a dic
  {-# INLINE lookup #-}
  toList (Compose dic) =
    [ ((a, b, c, d), v)
    | (a, aDic) <- toList dic
    , ((b, c, d), v) <- toList aDic
    ]
  {-# INLINE toList #-}

instance (Variable a, Variable b, Variable c, Variable d, Variable e)
  => Variable (a, b, c, d, e) where
  type Table (a, b, c, d, e) = ProdTable '[a, b, c, d, e]
  emptyTable' _ = Compose $ emptyTable @a
  {-# INLINE emptyTable' #-}
  singleton (a, b, c, d, e) v = Compose $ singleton a $ singleton (b, c, d, e) v
  {-# INLINE singleton #-}
  insert (a, b, c, d, e) v (Compose dic) =
    case lookup a dic of
      Nothing   -> Compose $ insert a (singleton (b, c, d, e) v) dic
      Just aDic -> Compose $ insert a (insert (b, c, d, e) v aDic) dic
  {-# INLINE insert #-}
  lookup (a, b, c, d, e) (Compose dic) = lookup (b, c, d, e) =<< lookup a dic
  {-# INLINE lookup #-}
  toList (Compose dic) =
    [ ((a, b, c, d, e), v)
    | (a, aDic) <- toList dic
    , ((b, c, d, e), v) <- toList aDic
    ]
  {-# INLINE toList #-}

deriveVia [t| Variable String `Via` HashVar String |]

substitute :: (Monad m, Variable a) => Table a (m a) -> m a -> m a
substitute dic e = e >>= \v -> fromMaybe (return v) (lookup v dic)


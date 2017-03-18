{-# LANGUAGE DeriveTraversable, EmptyCase, FlexibleInstances, InstanceSigs #-}
{-# LANGUAGE LambdaCase, PolyKinds, RankNTypes, ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving, TupleSections, TypeApplications           #-}
{-# LANGUAGE UndecidableInstances, ViewPatterns                            #-}
module Data.Unification.Generic
       ( -- $doc

         -- * Basic Classes
         HasVar(..), Unifiable(..)
       ) where
import           Control.Monad       (join)
import           Control.Monad.Free
import           Control.Monad.ST    (ST, runST)
import           Control.Monad.State (StateT, gets, lift, modify, runStateT)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as M
import           Data.Maybe          (fromJust)
import           Data.UnionFind.ST   (Point, descriptor, equivalent, fresh)
import           Data.UnionFind.ST   (setDescriptor, union)
import           GHC.Generics        ((:*:) (..), (:+:) (..), Generic1 (..))
import           GHC.Generics        (K1 (..), M1 (..), Par1 (..), Rec1 (..))
import           GHC.Generics        (Rep1 (..), U1 (..), V1, from1, to1)

data UnificationStatus f a =
  Success (f a) (Map a (f a))  | Failed (UnificationError f a)
  deriving (Read, Show, Eq, Ord)

data UnificationError f a = OccursCheck (f a) (f a)
                          deriving (Read, Show, Eq, Ord)
type Term = Free

newtype Var f s a =
  Var { runVar :: Point s (Maybe (Term f (Var f s a))) }
  deriving (Eq)

-- | Traversable functor with distinguishable /variable/ term.
--    
--   Default instance for @'HasVar' t@ considers every unary data constructor
--   of form @Ctor v@ as variable term.
class Traversable f => HasVar f where
  -- | @'takeVar' t@ returns @'Just' v@ if @t@ represents variable @v@,
  --   @'Nothing'@ otherwise.
  takeVar :: f a -> Maybe a

  default takeVar :: (Generic1 f, GHasVar (Rep1 f)) => f a -> Maybe a
  takeVar = gTakeVar . from1

class GHasVar f where
  gTakeVar :: f a -> Maybe a

instance HasVar f => GHasVar (Rec1 f) where
  gTakeVar (Rec1 p) = takeVar p

instance GHasVar Par1 where
  gTakeVar (Par1 v) = Just v

instance GHasVar f => GHasVar (M1 i c f) where
  gTakeVar (M1 p) = gTakeVar p

instance GHasVar (f :*: g) where
  gTakeVar _ = Nothing

instance (GHasVar f, GHasVar g) => GHasVar (f :+: g) where
  gTakeVar (L1 f) = gTakeVar f
  gTakeVar (R1 f) = gTakeVar f

instance GHasVar U1 where
  gTakeVar _ = Nothing

instance GHasVar V1 where
  gTakeVar _ = Nothing

instance GHasVar (K1 i c) where
  gTakeVar _ = Nothing

activateVars :: HasVar f => Free f a -> Free f a
activateVars (Pure a) = Pure a
activateVars (Free x) =
  case takeVar x of
    Nothing -> Free $ fmap (activateVars) x
    Just a  -> activateVars a

abstractOrd :: (HasVar f, Ord a)
            => Term f a
            -> StateT (Map a (Var f s a)) (ST s) (Term f (Var f s a))
abstractOrd = mapM $ \v -> do
  mvar <- gets (M.lookup v)
  case mvar of
    Nothing -> do
      ref <- lift $ Var <$> fresh Nothing
      modify $ M.insert v ref
      return ref
    Just c  -> return c

retrieve :: (Traversable f, Monad f, Ord a)
         => Map a (Var f s a)
         -> Var f s a
         -> ST s (Term f a)
retrieve dic = loop
  where
    loop (Var pt) = descriptor pt >>= \case
      Nothing -> return $ Pure $ fromJust $ lookup (Var pt) [ (v, k) | (k, v) <- M.toList dic ]
      Just t  -> join <$> mapM (retrieve dic) t

-- | Unifiable functors.
--
--   A 'Monad' with assignment as its bind @('>>=')@ can be automatically unified.
class Functor f => Unifiable f where
  unify :: Ord a => f a -> f a -> Maybe (f a, Map a (f a))

  default unify :: (Generic1 f, HasVar f, Monad f, GUnify f (Rep1 f), Ord a)
                => f a -> f a -> Maybe (f a, Map a (f a))
  unify = unifyOrd

unifyOrd :: (HasVar f, Monad f, Ord a, Generic1 f, GUnify f (Rep1 f))
         => f a -> f a -> Maybe (f a, Map a (f a))
unifyOrd l0 r0 = runST $ do
  let (l, r) = (activateVars $ liftF l0, activateVars $ liftF r0)
  ((l',r'), dic) <- runStateT ((,) <$> abstractOrd l <*> abstractOrd r) M.empty
  mans <- unify' l' r'
  result <- mapM (fmap (retract . join) . mapM (retrieve dic)) mans
  asig   <- mapM (fmap retract . retrieve dic) dic
  return ((, asig) <$> result)

class (Functor f, Functor c) => GUnify f c where
  gunify :: c (Free f (Var f s a)) -> c (Free f (Var f s a))
         -> ST s (Maybe (c (Free f (Var f s a))))

instance GUnify f c => GUnify f (M1 i d c) where
  gunify (M1 l) (M1 r) = fmap M1 <$> gunify l r

instance Functor f => GUnify f U1 where
  gunify U1 U1 = return $ Just U1

instance Functor f => GUnify f V1 where
  gunify v = case v of {}

instance (Functor f, Eq c) => GUnify f (K1 i c) where
  gunify (K1 l) (K1 r) =
    if l == r
    then return $ Just (K1 r)
    else return Nothing

instance (Generic1 f, HasVar f, Monad f, GUnify f (Rep1 f)) => GUnify f (Rec1 f) where
  gunify (Rec1 l) (Rec1 r) = fmap (Rec1 . return) <$> unify' (activateVars $ wrap l) (activateVars $ wrap r)

instance (GUnify f c, GUnify f d) => GUnify f (c :*: d) where
  gunify (l :*: r) (l' :*: r') = do
    ml <- gunify l l'
    mr <- gunify r r'
    return $ (:*:) <$> ml <*> mr

instance (GUnify f c, GUnify f d) => GUnify f (c :+: d) where
  gunify (L1 l) (L1 l') = fmap L1 <$> gunify l l'
  gunify (R1 r) (R1 r') = fmap R1 <$> gunify r r'
  gunify _ _ = return Nothing

instance (Generic1 f, HasVar f, Monad f, GUnify f (Rep1 f)) => GUnify f Par1 where
  gunify (Par1 l) (Par1 r) = fmap Par1 <$> unify' (activateVars l) (activateVars r)

occurs :: Traversable f => Var f s a -> f (Term f (Var f s a)) -> ST s Bool
occurs (Var v) t = or <$> mapM (fmap or . mapM (equivalent v . runVar)) t

readVar :: Var f s a -> ST s (Maybe (Term f (Var f s a)))
readVar = descriptor . runVar

assign :: Var t1 s t -> Term t1 (Var t1 s t) -> ST s (Maybe (Term t1 (Var t1 s t)))
assign (Var v) t = setDescriptor v (Just t) >> return (Just t)

equate :: Var t s a -> Var t s a -> ST s ()
equate (Var v) (Var u) = union v u

equiv :: Var t s a -> Var t s a -> ST s Bool
equiv (Var v) (Var u) = equivalent v u

unify' :: forall f a s. (Generic1 f, HasVar f, Monad f, GUnify f (Rep1 f))
       => Free f (Var f s a)
       -> Free f (Var f s a)
       -> ST s (Maybe (Term f (Var f s a)))
unify' (Free t) (Free s) = do
  let tRep = from1 t
      sRep = from1 s
  fmap (wrap . to1) <$> gunify tRep sRep
unify' (Free t) (Pure v) = do
  occ <- occurs v t
  readVar v >>= \case
    Nothing | not occ -> assign v (Free t)
            | otherwise -> return Nothing
    Just u -> unify' (Free t) u >>= \case
      Nothing  -> return Nothing
      (Just u') -> assign v u'
unify' (Pure v) (Free s)  = unify' (Free s) (Pure v)
unify' (Pure u) (Pure v) = do
  eq <- equiv u v
  if eq
    then return (Just (Pure u))
    else do
      u' <- readVar u
      v' <- readVar v
      equate u v
      match u' v'
  where
    match Nothing Nothing   = return (Just $ Pure u)
    match Nothing (Just t)  = unify' (Pure u) t
    match (Just s) Nothing  = unify' (Pure v) s
    match (Just t) (Just s) = unify' t s

{-$doc

= Introduction: Substitution and Monad

The aim of this package is to provide the handy way to derive
unification algorithm for arbitrary data-types.

To that end, we exploit the parametricity and GHC's generic deriving mechanism.

In particular, we adopt /parametric/ representation of variables;
for example, consider the following simple syntax tree for additive expressions:

@
/&#x7b;-\# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable \#-&#x7d;/
__import__ Data.Foldable    ('Foldable')
__import__ Data.Traversable ('Traversable')

__data__ Expr /v/ = Var /v/ | Lit 'Int' | Expr /v/ :+ Expr /v/
              __deriving__ (Show, Eq, Ord, /'Functor'/, /'Foldable'/, /'Traversable'/)
@

Here, type parameter /@v@/ in @Expr /v/@ corresponds to the /name/ of each variable.
We can use /'Functor'/, /'Foldable'/ and /'Traversable'/ instances
for @Expr@ to manipulate variables in @Expr@.
For example, we can collect all occurence of variables in @t@ by @'Data.Foldable.toList' t@,
uniform variable renaming by @'mapM' rename t@, etc.
Fortunately, we can derive these instances for free thanks to GHC's @Derive\*@ language extensions.

To handle unification, we have to /substitute/ a variable by other term.
We use /'Monad'/ instance for such a purpose; unfortunately, we have to supply
@'Monad'@ (and @'Applicative'@) instance by hand.
But it's not so diffcult to write; it's just a /substitution/:

@
__instance__ 'Monad' Expr __where__
  'return' = Var
  Var x    '>>=' f = f x
  Lit i    '>>=' _ = Lit i
  (l :+ r) '>>=' f = (l '>>=' f) :+ (l '>>=' r)
 
__instance__ 'Applicative' Expr __where__
  'pure'  = return
  ('<*>') = 'Control.Monad.ap'
@

Why @'Monad'@s corresponds to substitution?
To answer that question, it is helpful to consider @'fmap'@ and @'join'@
instead of @'return'@ and @('>>=')@.
As noted earlier, we view a type @t v@ as "a term with variable labeled by @v@";
this can be rephrased as "a term with holes substituted with type @v@".
Then, type @t (t v)@ can be viewed as "a term with variable virtually substituded by term itself".
Under this interpretation, @'join' :: t (t v) -> t v@ can be considered as a "substitute and evaulate" operator.

= Unification for Free!
So it is left to derive unification.
To that end, we use GHC's <https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#generic-programming Generic Deriving mechanism>.

What we need to get unification for free is just add /three/ classes to deriving clause:
@'Generic1'@, @'HasVar'@ and @'Unifiable'@.

@
-- Add these pragmas at the top of module:
/&#x7b;-\# LANGUAGE DeriveAnyClass, DeriveGeneric \#-&#x7d;/

__data__ Expr /v/ = Var /v/ | Lit 'Int' | Expr /v/ :+ Expr /v/
              __deriving__ (..., __'Generic1'__, __'HasVar'__, __'Unifiable'__)
@

Then we can freely use @'unify'@ function of @'Unifiable'@ class for @Expr@s!

>>> unify ((Num 1 :+ Var "X") :+ Var "X") (Var "Y" :+ Num 2)
Just ((Num 1 :+ Num 2) :+ Num 2,fromList [("X",Num 2),("Y",Num 1 :+ Num 2)])
>>> unify (Var "X" :+ Var "Y") (Var "Y")
Nothing

== What's behind the scene?

In the code above, @'Generic1'@ instance is needed to derive @'HasVar'@ and @'Unifiable'@ instances.
This package implements the mechanism to automatically generate boilerplate code for unification,
utilizing the generic (sum-of-products) representation of given @'Functor'@ instance provided by
GHC's Generic Deriving Mechanism.

Roughly speaking, unification process is really a boilerplate: just to pattern-match on constructor
and instantiate variables by concrete terms consistenly.
In this process, we have to distinguish two kinds of term construtor: variable terms and ordinary terms.
The @'takeVar'@ function of @'HasVar'@ type-class does exactly this.
By default, @'takeVar'@ considers every unary data-constructor of @t v@ with argument of type @v@ as a variable term.

For example, @Var v@ of our @Expr@ type is considered as variable term by the library generated code.
If one need more flexible control over this distinction process, one can remove @'HasType'@
from derivation list and implement the custom instance for it.

One can implement @'Unifiable'@ instance by hand for the sake of efficiency, of course.
-}
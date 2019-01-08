{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Main where
import Control.Monad            (ap)
import Data.Unification.Generic (HasVar, Unifiable, unify)
import GHC.Generics             (Generic1)

data Expr v = Num Int | Var v | Expr v :+ Expr v | Neg (Expr v)
            deriving (Read, Show, Eq, Ord, Generic1,
                      Functor, Foldable, Traversable,
                      HasVar, Unifiable)

infixl 6 :+

instance Applicative Expr where
  (<*>) = ap
  pure  = return

instance Monad Expr where
  return         = Var
  Var x    >>= f = f x
  Num i    >>= _ = Num i
  (l :+ r) >>= f = (l >>= f) :+ (r >>= f)
  Neg e    >>= f = Neg (e >>= f)

main :: IO ()
main = do
  print $ unify (Var "x") (Num 5 :+ Var "y")
  print $ unify (Var "x" :+ Num 2) (Num 2 :+ Var "x")
  print $ unify (Var "x" :+ Num 2) (Num 3 :+ Var "x")
  print $ unify (Var "x" :+ Num 2) (Var "y" :+ Var "x")

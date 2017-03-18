# Introduction: Substitution and Monad

The aim of this package is to provide the handy way to derive
unification algorithm for arbitrary data-types.

To that end, we exploit the parametricity and GHC's generic deriving mechanism.

In particular, we adopt *parametric* representation of variables;
for example, consider the following simple syntax tree for additive expressions:

```haskell
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
import Data.Foldable    (Foldable)
import Data.Traversable (Traversable)

data Expr v = Var v | Lit Int | Expr v :+ Expr v
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
```

Here, type parameter *`v`* in `Expr v` corresponds to the *name* of each variable.
We can use *Functor*, *Foldable* and *Traversable* instances
for `Expr` to manipulate variables in `Expr`.
For example, we can collect all occurence of variables in `t` by `Data.Foldable.toList t`,
uniform variable renaming by `mapM rename t`, etc.
Fortunately, we can derive these instances for free thanks to GHCs `Derive*` language extensions.

To handle unification, we have to *substitute* a variable by other term.
We use *Monad* instance for such a purpose; unfortunately, we have to supply
`Monad` (and `Applicative`) instance by hand.
But its not so diffcult to write; its just a *substitution*:

```haskell
instance Monad Expr where
  return = Var
  Var x    >>= f = f x
  Lit i    >>=  = Lit i
  (l :+ r) >>= f = (l >>= f) :+ (l >>= r)
 
instance Applicative Expr where
  pure  = return
  (<*>) = Control.Monad.ap
```

Why `Monad`s corresponds to substitution?
To answer that question, it is helpful to consider `fmap` and `join`
instead of `return` and `(>>=)`.
As noted earlier, we view a type `t v` as "a term with variable labeled by `v`";
this can be rephrased as "a term with holes substituted with type `v`".
Then, type `t (t v)` can be viewed as "a term with variable virtually substituded by term itself".
Under this interpretation, `join :: t (t v) -> t v` can be considered as a "substitute and evaulate" operator.

# Unification for Free!

So it is left to derive unification.
To that end, we use GHCs [Generic Deriving Mechanism](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#generic-programming).

What we need to get unification for free is just add *three* classes to deriving clause:
`Generic1`, `HasVar` and `Unifiable`.

```haskell
-- Add these pragmas at the top of module:
{-# LANGUAGE DeriveAnyClass, DeriveGeneric #-}

data Expr v = Var v | Lit Int | Expr v :+ Expr v
              deriving (..., Generic1, HasVar, Unifiable)
```

Then we can freely use `unify` function of `Unifiable` class for `Expr`s!

```haskell
ghci> unify ((Num 1 :+ Var "X") :+ Var "X") (Var "Y" :+ Num 2)
Just ((Num 1 :+ Num 2) :+ Num 2,fromList [("X",Num 2),("Y",Num 1 :+ Num 2)])

ghci> unify (Var "X" :+ Var "Y") (Var "Y")
Nothing
```

## Whats behind the scene?

In the code above, `Generic1` instance is needed to derive `HasVar` and `Unifiable` instances.
This package implements the mechanism to automatically generate boilerplate code for unification,
utilizing the generic (sum-of-products) representation of given `Functor` instance provided by
GHCs Generic Deriving Mechanism.

Roughly speaking, unification process is really a boilerplate: just to pattern-match on constructor
and instantiate variables by concrete terms consistenly.
In this process, we have to distinguish two kinds of term construtor: variable terms and ordinary terms.
The `takeVar` function of `HasVar` type-class does exactly this.
By default, `takeVar` considers every unary data-constructor of `t v` with argument of type `v` as a variable term.

For example, `Var v` of our `Expr` type is considered as variable term by the library generated code.
If one need more flexible control over this distinction process, one can remove `HasType`
from derivation list and implement the custom instance for it.

One can implement `Unifiable` instance by hand for the sake of efficiency, of course.

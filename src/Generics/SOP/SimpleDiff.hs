{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.SOP.SimpleDiff where

import Data.Coerce
import Data.List
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Generics.SOP
import qualified GHC.Generics as GHC

type EqDiff a = a
type GDiff a = SOP WDiff (Code a)

data WDiff a =
    Changed a a
  | Enter (Diff a)

data DiffStyle =
    ToDel
  | ToAdd

del :: Doc DiffStyle -> Doc DiffStyle
del = annotate ToDel

add :: Doc DiffStyle -> Doc DiffStyle
add = annotate ToAdd

diffToAnsi :: Doc DiffStyle -> Doc AnsiStyle
diffToAnsi = reAnnotate go
  where
    go :: DiffStyle -> AnsiStyle
    go ToDel = bgColor Red
    go ToAdd = bgColor Green

class (Show a, Eq a) => Diffable a where
  type Diff a
  type Diff a = GDiff a
  diff :: a -> a -> WDiff a
  default diff ::
    (Generic a, All2 Diffable (Code a), Diff a ~ GDiff a) => a -> a -> WDiff a
  diff = gDiff

  renderPrec :: Int -> WDiff a -> Doc DiffStyle
  default renderPrec ::
    (Generic a, HasDatatypeInfo a, All2 Diffable (Code a), Diff a ~ GDiff a)
    => Int -> WDiff a -> Doc DiffStyle
  renderPrec = gRenderPrec

eqDiff :: (Eq a, Diff a ~ EqDiff a) => a -> a -> WDiff a
eqDiff x y
  | x == y    = Enter x
  | otherwise = Changed x y

gDiff ::
  (Generic a, All2 Diffable (Code a), Diff a ~ GDiff a) => a -> a -> WDiff a
gDiff x y =
  case go (unSOP (from x)) (unSOP (from y)) of
    Nothing -> Changed x y
    Just d  -> Enter (SOP d)
  where
    go :: All2 Diffable xss => NS (NP I) xss -> NS (NP I) xss -> Maybe (NS (NP WDiff) xss)
    go (Z xs) (Z ys) = Just (Z (hczipWith (Proxy @Diffable) (coerce diff) xs ys))
    go (S x ) (S y ) = S <$> go x y
    go _      _      = Nothing

showRenderPrec :: (Show a, Diff a ~ EqDiff a) => Int -> WDiff a -> Doc DiffStyle
showRenderPrec p (Enter a) = pretty (showsPrec p a "")
showRenderPrec p (Changed x y) = renderChange p x y

renderChange :: Show a => Int -> a -> a -> Doc DiffStyle
renderChange p x y =
     del (pretty (showsPrec p x ""))
  <> add (pretty (showsPrec p y ""))

{-
renderChangeAnsi :: Show a => Int -> a -> a -> IO ()
renderChangeAnsi p x y = do
  setSGR [SetColor Background Vivid Red]
  putStr (showsPrec p x "")
  setSGR [SetColor Background Vivid Green]
  putStr (showsPrec p y "")
  setSGR [Reset]
-}

gRenderPrec ::
  forall a . (Generic a, Show a, HasDatatypeInfo a, All2 Diffable (Code a), Diff a ~ GDiff a)
  => Int -> WDiff a -> Doc DiffStyle
gRenderPrec p (Enter d) = renderSOP (Proxy :: Proxy a) p d
gRenderPrec p (Changed x y) = renderChange p x y

renderSOP ::
  (Generic a, HasDatatypeInfo a, All2 Diffable (Code a))
  => Proxy a -> Int -> SOP WDiff (Code a) -> Doc DiffStyle
renderSOP p d x =
    hcollapse
  $ hczipWith (Proxy @(All Diffable)) (renderConstructor d)
      (constructorInfo (datatypeInfo p))
      (unSOP x)

renderParen :: Bool -> Doc DiffStyle -> Doc DiffStyle
renderParen True  x = parens x
renderParen False x = x

renderConstructor ::
  (All Diffable xs) => Int -> ConstructorInfo xs -> NP WDiff xs -> K (Doc DiffStyle) xs
renderConstructor d i =
  case i of
    Constructor n -> \ x -> K
      $ renderParen (d > app_prec)
      $ hsep
      $ pretty n : renderConstructorArgs (app_prec + 1) x
    Infix n _ prec -> \ (l :* r :* Nil) -> K
      $ renderParen (d > prec)
      $ renderPrec (prec + 1) l
      <+> pretty n
      <+> renderPrec (prec + 1) r
    Record n fi -> \ x -> K
      $ renderParen (d > app_prec) -- could be even higher, but seems to match GHC behaviour
      $ pretty n
      <+> braces (renderRecordArgs fi x)

renderConstructorArgs ::
  (All Diffable xs) => Int -> NP WDiff xs -> [Doc DiffStyle]
renderConstructorArgs d x =
    hcollapse
  $ hcmap (Proxy @Diffable) (K . renderPrec d) x

renderRecordArgs ::
  (All Diffable xs) => NP FieldInfo xs -> NP WDiff xs -> Doc DiffStyle
renderRecordArgs fi x =
    hsep
  $ punctuate comma
  $ hcollapse
  $ hczipWith (Proxy @Diffable)
      (\ (FieldInfo l) y -> K (pretty l <+> equals <+> renderPrec 0 y))
      fi x

renderTuple ::
  (IsProductType a xs, Show a, All Diffable xs, Diff a ~ GDiff a) => Int -> WDiff a -> Doc DiffStyle
renderTuple p (Enter d) = renderTuple' (unZ (unSOP d))
renderTuple p (Changed x y) = renderChange p x y

renderTuple' ::
  (All Diffable xs) => NP WDiff xs -> Doc DiffStyle
renderTuple' x =
    renderParen True
  $ hcat
  $ punctuate comma
  $ hcollapse
  $ hcmap (Proxy @Diffable) (K . renderPrec 0) x

app_prec :: Int
app_prec = 10

instance Diffable () where
  type Diff () = EqDiff ()
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Int where
  type Diff Int = EqDiff Int
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Char where
  type Diff Char = EqDiff Char
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Bool

instance Diffable Text where
  type Diff Text = EqDiff Text
  diff = eqDiff
  renderPrec = showRenderPrec

instance (Diffable a, Diffable b) => Diffable (a, b) where
  diff = gDiff
  renderPrec = renderTuple

instance (Diffable a, Diffable b, Diffable c) => Diffable (a, b, c) where
  diff = gDiff
  renderPrec = renderTuple


instance Diffable a => Diffable (Maybe a)
instance (Diffable a, Diffable b) => Diffable (Either a b)
instance Diffable Ordering

renderDiff :: Diffable a => a -> a -> IO ()
renderDiff x y =
  putDoc (diffToAnsi (renderPrec 0 (diff x y) <> line))

data Foo = MkFoo { x :: Text, y :: Bool }
  deriving (GHC.Generic, Eq, Show)

instance Generic Foo
instance HasDatatypeInfo Foo
instance Diffable Foo

data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving (GHC.Generic, Eq, Show, Functor)

instance Generic (Tree a)
instance HasDatatypeInfo (Tree a)
instance Diffable a => Diffable (Tree a)

buildTree :: Int -> Tree ()
buildTree 0 = Leaf ()
buildTree n =
  let
    t = buildTree (n - 1)
  in
    Node t t

example1 :: IO ()
example1 =
  renderDiff 'x' 'x'

example2 :: IO ()
example2 =
  renderDiff 'x' 'y'

example3 :: IO ()
example3 =
  renderDiff (MkFoo "foo" True) (MkFoo "bar" True)

example4 :: IO ()
example4 =
  renderDiff (MkFoo "foo" True) (MkFoo "foo" False)

example5 :: IO ()
example5 =
  renderDiff (buildTree 2) (buildTree 3)

example6 :: IO ()
example6 =
  renderDiff (False <$ buildTree 2) (True <$ buildTree 2)

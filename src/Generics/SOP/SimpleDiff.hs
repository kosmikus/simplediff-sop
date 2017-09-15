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
import Generics.SOP
import qualified GHC.Generics as GHC
import System.Console.ANSI

data Diff a where
  Unchanged :: a -> Diff a
  Changed   :: a -> a -> Diff a
  Enter     :: SOP Diff (Code a) -> Diff a

deriving instance
  (Show a, All (Compose Show (NP Diff)) (Code a)) => Show (Diff a)

class (Show a, Eq a) => Diffable a where
  diff :: a -> a -> Diff a
  default diff ::
    (Generic a, All2 Diffable (Code a)) => a -> a -> Diff a
  diff = gDiff

  renderPrec :: Int -> Diff a -> IO ()
  default renderPrec ::
    (Generic a, HasDatatypeInfo a, All2 Diffable (Code a))
    => Int -> Diff a -> IO ()
  renderPrec = gRenderPrec

eqDiff :: Eq a => a -> a -> Diff a
eqDiff x y
  | x == y    = Unchanged x
  | otherwise = Changed x y

gDiff ::
  (Generic a, All2 Diffable (Code a)) => a -> a -> Diff a
gDiff x y =
  case go (unSOP (from x)) (unSOP (from y)) of
    Nothing -> Changed x y
    Just d  -> Enter (SOP d)
  where
    go :: All2 Diffable xss => NS (NP I) xss -> NS (NP I) xss -> Maybe (NS (NP Diff) xss)
    go (Z xs) (Z ys) = Just (Z (hczipWith (Proxy @Diffable) (coerce diff) xs ys))
    go (S x ) (S y ) = S <$> go x y
    go _      _      = Nothing

showRenderPrec :: (Show a) => Int -> Diff a -> IO ()
showRenderPrec p (Unchanged a) = putStr (showsPrec p a "")
showRenderPrec p (Changed x y) = do
  setSGR [SetColor Background Vivid Red]
  putStr (showsPrec p x "")
  setSGR [SetColor Background Vivid Green]
  putStr (showsPrec p y "")
  setSGR [Reset]

gRenderPrec :: forall a . (Generic a, Show a, HasDatatypeInfo a, All2 Diffable (Code a)) => Int -> Diff a -> IO ()
gRenderPrec p (Enter d) = renderSOP (Proxy :: Proxy a) p d
gRenderPrec p d         = showRenderPrec p d

renderSOP ::
  (Generic a, HasDatatypeInfo a, All2 Diffable (Code a)) => Proxy a -> Int -> SOP Diff (Code a) -> IO ()
renderSOP p d x =
    hcollapse
  $ hczipWith (Proxy @(All Diffable)) (renderConstructor d)
      (constructorInfo (datatypeInfo p))
      (unSOP x)

renderParen :: Bool -> IO () -> IO ()
renderParen True  x = putStr "(" >> x >> putStr ")"
renderParen False x = x

renderConstructor ::
  forall xs . (All Diffable xs) => Int -> ConstructorInfo xs -> NP Diff xs -> K (IO ()) xs
renderConstructor d i =
  case i of
    Constructor n -> \ x -> K
      $ renderParen (d > app_prec)
      $ putStr (n ++ " ") >> renderConstructorArgs (app_prec + 1) x
    Infix n _ prec -> \ (l :* r :* Nil) -> K
      $ renderParen (d > prec)
      $ renderPrec (prec + 1) l
      >> putStr (" " ++ n ++ " ")
      >> renderPrec (prec + 1) r
    Record n fi -> \ x -> K
      $ renderParen (d > app_prec) -- could be even higher, but seems to match GHC behaviour
      $ putStr (n ++ " {") >> renderRecordArgs fi x >> putStr "}"

renderConstructorArgs ::
  (All Diffable xs) => Int -> NP Diff xs -> IO ()
renderConstructorArgs d x =
  sequence_ $ intersperse (putStr " ") $ hcollapse $ hcmap (Proxy @Diffable) (K . renderPrec d) x

renderRecordArgs ::
  (All Diffable xs) => NP FieldInfo xs -> NP Diff xs -> IO ()
renderRecordArgs fi x =
    sequence_
  $ intersperse (putStr ", ")
  $ hcollapse
  $ hczipWith (Proxy @Diffable)
      (\ (FieldInfo l) y -> K (putStr (l ++ " = ") >> renderPrec 0 y))
      fi x

renderTuple ::
  (IsProductType a xs, Show a, All Diffable xs) => Int -> Diff a -> IO ()
renderTuple _ (Enter d) = renderTuple' (unZ (unSOP d))
renderTuple p d         = showRenderPrec p d

renderTuple' ::
  (All Diffable xs) => NP Diff xs -> IO ()
renderTuple' x =
    renderParen True
  $ sequence_
  $ intersperse (putStr ",")
  $ hcollapse
  $ hcmap (Proxy @Diffable) (K . renderPrec 0) x

app_prec :: Int
app_prec = 10

instance Diffable () where
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Int where
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Char where
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Bool where
  diff = eqDiff
  renderPrec = showRenderPrec

instance Diffable Text where
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
  renderPrec 0 (diff x y) >> putStrLn ""

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

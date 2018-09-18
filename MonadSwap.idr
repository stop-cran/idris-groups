module MonadSwap

import Interfaces.Verified
import Pruviloj.Core
import Pruviloj.Induction
import Language.Reflection.Elab
import Data.Morphisms

%access public export
%default total


interface Monad m => MonadSwap (m : Type -> Type) where
    swap : VerifiedMonad n => m (n a) -> n (m a)

MonadSwap Maybe where
    swap Nothing = pure Nothing
    swap (Just x) = map Just x 

MonadSwap (Either a) where
    swap x@(Left _) = pure x
    swap (Right x) = map Right x
    
MonadSwap List where
    swap [] = pure []
    swap (x :: xs) = [| x :: swap xs |]

interface (MonadSwap m, VerifiedMonad m) => VerifiedMonadSwap (m : Type -> Type) where
    swapIdentity : VerifiedMonad n => (x : a) -> (y : a) -> x = y -> swap (pure (pure x)) = pure {f=n} (pure {f=m} y)
    swapMap : VerifiedMonad n => (f : a -> b) -> (x : m (n a)) -> swap (map (map f) x) = map (map f) (swap x)
    --swapIdempotent : VerifiedMonad n => Idempotent (swap . swap)

applicativeMapPure : VerifiedApplicative f => (x : a) -> (g : a -> b) ->
                     map {f} g (pure x) = pure (g x)
applicativeMapPure {f} x g = trans
    (applicativeMap {f} (pure x) g)
    (applicativeHomomorphism {f} x g)

functorCong : Functor f =>
              {g1 : a -> b} -> {g2 : a -> b} ->
              ((x : a) -> g1 x = g2 x) ->
              (y : f a) -> map g1 y = map g2 y
functorCong pr x = ?hfunctorCong

applicativeLiftA2Pure : VerifiedApplicative f => (g : a -> b -> c) -> (x : a) -> (y : b) ->
                        ((<*>) {f} (pure g <*> pure x) (pure y)) = pure (g x y)
applicativeLiftA2Pure {f} g x y = trans
                                  (sym $ cong {f=(\x => (<*>) {f} x (pure {f} y))} $ sym $ applicativeHomomorphism {f} x g)
                                  (applicativeHomomorphism {f} y (g x))

applicativePureComposition : VerifiedApplicative f => (x : f a) ->
                             (g1 : a -> b) -> (g2 : b -> c) ->
                             map (g2 . g1) x = (pure g2 <*> map g1 x)
applicativePureComposition {f} x g1 g2 = trans (functorComposition {f} x g1 g2) (applicativeMap {f} (map {f} g1 x) g2)

VerifiedMonadSwap Maybe where
    swapIdentity x y eq = trans (applicativeMapPure x Just) (cong {f = pure . Just} eq)
    swapMap {n} g Nothing = sym (applicativeMapPure {f=n} Nothing (map g))
    swapMap g (Just x) = trans (sym $ functorComposition x g Just) (functorComposition x Just (map g))

VerifiedMonadSwap (Either a) where
    swapIdentity {n} x y eq = trans (applicativeMapPure {f=n} x Right) (cong {f = pure {f=n} . Right} eq)
    swapMap {n} g x@(Left _) = sym (applicativeMapPure {f=n} x (map {f=Either a} g))
    swapMap g (Right x) = trans (sym $ functorComposition x g Right) (functorComposition x Right (\meth => Functor.map {f=Either a} g meth))

VerifiedMonadSwap List where
    swapIdentity {n} x y eq = trans (applicativeLiftA2Pure {f=n} (::) x []) (cong {f=pure . pure} eq)
    swapMap {n} g [] = sym (applicativeMapPure {f=n} [] (map {f=List} g))
    swapMap {n} {a} {b} g (x :: xs) = ?hswapMap (cong {f=ff} $ swapMap {n} g xs) (sym $ applicativePureComposition {f=n} {c=List b -> List b} x g (::)) where
        ff : n (List b) -> n (List b)
        ff l = pure (::) <*> map g x <*> l
    
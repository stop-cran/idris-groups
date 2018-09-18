module Oriented

import MonadSwap
import MonadComposition
import Interfaces.Verified

%access public export
%default total


data Oriented : a -> Type where
    Gen : a -> Oriented a
    Inv : a -> Oriented a

Eq a => Eq (Oriented a) where
    (Gen x) == (Gen y) = x == y
    (Inv x) == (Inv y) = x == y
    _ == _ = False

Ord a => Ord (Oriented a) where
    compare (Gen x) (Gen y) = compare x y
    compare (Inv x) (Inv y) = compare x y
    compare (Gen _) (Inv _) = GT
    compare (Inv _) (Gen _) = LT

Show a => Show (Oriented a) where
    show (Gen x) = "Gen " ++ show x
    show (Inv x) = "Inv " ++ show x

Uninhabited a => Uninhabited (Oriented a) where
    uninhabited (Gen x) = uninhabited x
    uninhabited (Inv x) = uninhabited x

Functor Oriented where
    map f (Gen x) = Gen $ f x
    map f (Inv x) = Inv $ f x

Applicative Oriented where
    pure = Gen
    (Gen f) <*> (Gen x) = Gen $ f x
    (Inv f) <*> (Gen x) = Inv $ f x
    (Gen f) <*> (Inv x) = Inv $ f x
    (Inv f) <*> (Inv x) = Gen $ f x

Monad Oriented where
    join (Gen (Gen x)) = Gen x
    join (Gen (Inv x)) = Inv x
    join (Inv (Gen x)) = Inv x
    join (Inv (Inv x)) = Gen x

MonadSwap Oriented where
    swap (Gen x) = map Gen x
    swap (Inv x) = map Inv x

VerifiedFunctor Oriented where
    functorIdentity _ proofId (Gen x) = rewrite proofId x in Refl
    functorIdentity _ proofId (Inv x) = rewrite proofId x in Refl
    functorComposition (Gen _) _ _ = Refl
    functorComposition (Inv _) _ _ = Refl

VerifiedApplicative Oriented where
    applicativeMap (Gen _) _ = Refl
    applicativeMap (Inv _) _ = Refl
    applicativeIdentity (Gen _) = Refl
    applicativeIdentity (Inv _) = Refl
    applicativeComposition (Gen _) (Gen _) (Gen _) = Refl
    applicativeComposition (Gen _) (Gen _) (Inv _) = Refl
    applicativeComposition (Gen _) (Inv _) (Gen _) = Refl
    applicativeComposition (Gen _) (Inv _) (Inv _) = Refl
    applicativeComposition (Inv _) (Gen _) (Gen _) = Refl
    applicativeComposition (Inv _) (Gen _) (Inv _) = Refl
    applicativeComposition (Inv _) (Inv _) (Gen _) = Refl
    applicativeComposition (Inv _) (Inv _) (Inv _) = Refl
    applicativeHomomorphism _ _ = Refl
    applicativeInterchange _ (Gen _) = Refl
    applicativeInterchange _ (Inv _) = Refl

VerifiedMonad Oriented where
    monadApplicative (Gen _) (Gen _) = Refl
    monadApplicative (Gen _) (Inv _) = Refl
    monadApplicative (Inv _) (Gen _) = Refl
    monadApplicative (Inv _) (Inv _) = Refl
    monadLeftIdentity x f with (f x)
        | (Gen _) = Refl
        | (Inv _) = Refl
    monadRightIdentity (Gen _) = Refl
    monadRightIdentity (Inv _) = Refl
    monadAssociativity (Gen x) f g with (f x)
        | (Gen y) with (g y)
            | (Gen _) = Refl
            | (Inv _) = Refl
        | (Inv y) with (g y)
            | (Gen _) = Refl
            | (Inv _) = Refl
    monadAssociativity (Inv x) f g with (f x)
        | (Gen y) with (g y)
            | (Gen _) = Refl
            | (Inv _) = Refl
        | (Inv y) with (g y)
            | (Gen _) = Refl
            | (Inv _) = Refl

VerifiedMonadSwap Oriented where
    swapIdentity x y eq = trans (applicativeMapPure x Gen) (cong {f=pure . Gen} eq)
    swapMap g (Gen x) = trans (sym $ functorComposition x g Gen) (functorComposition x Gen (map g))
    swapMap g (Inv x) = trans (sym $ functorComposition x g Inv) (functorComposition x Inv (map g))

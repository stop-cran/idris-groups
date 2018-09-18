module FreeGroup

import MonadSwap
import MonadComposition
import Oriented
import Control.Algebra
import Control.Monad.Trans
import Data.Fin
import Data.ZZ
import MorphismEqual
import Interfaces.Verified

%access public export
%default total


using (a : Type, b : Type, m : Type -> Type)
    data Kleislimorphism2 : (Monad m, Alternative m) => (m : Type -> Type) -> a -> b -> Type where
        Kleisli2 : (Monad m, Alternative m) => (kleisli : b -> m a) -> (t_action : m a -> b) ->
                   MorphismEqual (t_action . kleisli) Basics.id ->
                   MorphismEqual (kleisli . t_action . pure {f=m}) (Applicative.pure {f=m}) ->
                   kleisli (t_action (empty {f=m})) = empty {f=m} ->
                   Kleislimorphism2 m a b

    applyKleisli : (Monad m, Alternative m) => Kleislimorphism2 m a b -> b -> m a
    applyKleisli (Kleisli2 f _ _ _ _) = f

    unapplyKleisli : (Monad m, Alternative m) => Kleislimorphism2 m a b -> m a -> b
    unapplyKleisli (Kleisli2 _ f _ _ _) = f

    structureMap : (Monad m, Alternative m) => Kleislimorphism2 m a b -> m b -> b
    structureMap f = unapplyKleisli f . (>>= applyKleisli f)

    presentationMap : (Monad m, Alternative m) => Kleislimorphism2 m a b -> m a -> m a
    presentationMap f = applyKleisli f . unapplyKleisli f

    data TAlgebra : (Monad m, Alternative m) => (m : Type -> Type) -> a -> Type where
        MkAlgebra : (Monad m, Alternative m) => (m a -> a) -> TAlgebra m a

    kleisli2ToTAlgebra : (Monad m, Alternative m) => Kleislimorphism2 m a b -> TAlgebra m b
    kleisli2ToTAlgebra = MkAlgebra . structureMap

    data TPresentation : (Monad m, Alternative m) => (m : Type -> Type) -> a -> Type where
        MkPresentation : (Monad m, Alternative m) => (m a -> m a) -> TPresentation m a

    kleisli2ToTPresentation : (Monad m, Alternative m) => Kleislimorphism2 m a b -> TPresentation m a
    kleisli2ToTPresentation = MkPresentation . presentationMap

    groupOp : (Monad m, Alternative m) => Kleislimorphism2 m a b -> b -> b -> b
    groupOp k x y = structureMap k $ pure x <|> pure y

    groupNeutral : (Monad m, Alternative m) => Kleislimorphism2 m a b -> b
    groupNeutral k = structureMap k empty

    groupInvert : (VerifiedMonad m, Alternative m) => Kleislimorphism2 (MonadComposition Oriented m) a b -> b -> b
    groupInvert k = structureMap k . (mapMonadCompose $ map ((Inv id) <*>)) . pure

    groupOpTrans : (Monad m, Alternative m) => (k : Kleislimorphism2 m a b) ->
                   (x1 : b) -> (x2 : b) -> (x3 : b) ->
                   groupOp k x1 (groupOp k x2 x3) = groupOp k (groupOp k x1 x2) x3
    groupOpTrans k x1 x2 x3 = ?hgroupOpTrans

    groupLeftUnit : (Monad m, Alternative m) => (k : Kleislimorphism2 m a b) -> (x : b) ->
                    groupOp k (groupNeutral k) x = x
    groupLeftUnit k x = ?hgroupLeftUnit

    groupRightUnit : (Monad m, Alternative m) => (k : Kleislimorphism2 m a b) -> (x : b) ->
                     groupOp k x (groupNeutral k) = x
    groupRightUnit k x = ?hgroupLeftUnit

    groupLeftInvert : (VerifiedMonad m, Alternative m) => (k : Kleislimorphism2 (MonadComposition Oriented m) a b) -> (x : b) ->
                      groupOp k (groupInvert k x) x = groupNeutral k
    groupLeftInvert k x = ?hgroupLeftInvert

    groupRightInvert : (VerifiedMonad m, Alternative m) => (k : Kleislimorphism2 (MonadComposition Oriented m) a b) -> (x : b) ->
                       groupOp k x (groupInvert k x) = groupNeutral k
    groupRightInvert k x = ?hgroupLeftInvert

fromZZOrientedNat : ZZ -> Oriented Nat
fromZZOrientedNat (Pos n) = Gen n
fromZZOrientedNat (NegS n) = Inv n

groupZKleisli : ZZ -> MonadComposition Oriented List Unit
groupZKleisli = MonadCompose . swap . map (`replicate` ()) . fromZZOrientedNat

fromOrientedUnitZZ : Oriented Unit -> ZZ
fromOrientedUnitZZ (Gen ()) = Pos 1
fromOrientedUnitZZ (Inv ()) = NegS 1

groupZAction : MonadComposition Oriented List Unit -> ZZ
groupZAction (MonadCompose x) = sum (map fromOrientedUnitZZ x)

swapEq1 : {x : a} -> {y : a} -> x = y -> y = x
swapEq1 eq = rewrite eq in Refl

prZZSSum : (n : Nat) -> plusZ (Pos 1) (Pos n) = Pos (S n)
prZZSSum Z = Refl
prZZSSum (S n) = cong {f=Pos . S . absZ} (prZZSSum n)

prSumReplicate : (n : Nat) -> sum (replicate n (Pos 1)) = Pos n
prSumReplicate Z = Refl
prSumReplicate (S n) = cong {f=plusZ (Pos 1)} (prSumReplicate n)

congTrans1 : (f : a -> b) -> (g : a -> b) -> (x : a) -> (y : a) -> x = y -> f x = g x -> f x = g y
congTrans1 f g x y eq eqFG = rewrite eqFG in (cong {f=g} eq)

congTrans : (f : a -> b) -> (g : a -> b) -> (h : a -> b) -> (x : a) -> f x = g x -> f x = h x -> g x = h x
congTrans f g h x eqFG eqFH = trans (sym eqFG) eqFH

prSumReplicate2 : (x : Nat) -> (y : Nat) -> x = y -> sum (replicate x (Pos 1)) = Pos y
prSumReplicate2 x y eq = congTrans1 (\x => sum (replicate x (Pos 1))) Pos x y eq (prSumReplicate x)

prReplicateMap : (n : Nat) -> (x : a) -> (g : a -> b) -> map g (replicate n x) = replicate n (g x)
prReplicateMap Z _ _ = Refl
prReplicateMap (S n) x g = (cong {f=((::) (g x))} (prReplicateMap n x g))

prReplicateUnitMap : (n : Nat) -> map (\x1 => fromOrientedUnitZZ (Gen x1)) (replicate n ()) = replicate n (Pos 1)
prReplicateUnitMap n = prReplicateMap n () (fromOrientedUnitZZ . Gen)

congAbsZ : {x : Nat} -> {y : Nat} -> Pos x = Pos y -> x = y
congAbsZ eq = cong {f=absZ} eq

groupZprId : (x : ZZ) -> (y : ZZ) -> x = y ->
             sum (map FreeGroup.fromOrientedUnitZZ (MonadSwap.swap $ map (`replicate` ()) (fromZZOrientedNat x))) = y
groupZprId (Pos x) (Pos y) eq = ?hgroupZprId1 (prReplicateUnitMap x) (functorComposition (replicate x ()) Gen fromOrientedUnitZZ)
groupZprId (NegS x) (Pos y) eq = ?hgroupZprId2
groupZprId (Pos x) (NegS y) eq = ?hgroupZprId3
groupZprId (NegS x) (NegS y) eq = ?hgroupZprId4

groupZ : Kleislimorphism2 (MonadComposition Oriented List) Unit ZZ
groupZ = Kleisli2 groupZKleisli groupZAction (MorphismEq {f1=groupZAction . groupZKleisli} {f2=id} groupZprId) ?hhgroupZ1 ?hhgroupZ2

freeGroupReduce: Eq a => List (Oriented a) -> List (Oriented a)
freeGroupReduce [] = []
freeGroupReduce (Gen x :: xs) with (freeGroupReduce xs)
    | [] = [Gen x]
    | (Inv y :: ys) = if x == y then ys else Gen x :: Inv y :: ys
    | (Gen y :: ys) = Gen x :: Gen y :: ys
freeGroupReduce (Inv x :: xs) with (freeGroupReduce xs)
    | [] = [Inv x]
    | (Gen y :: ys) = if x == y then ys else Inv x :: Gen y :: ys
    | (Inv y :: ys) = Inv x :: Inv y :: ys

freeMonoid : Eq a => Kleislimorphism2 (MonadComposition Oriented List) a (List (Oriented a))
freeMonoid = Kleisli2 MonadCompose runMonadCompose (MorphismEq prId) (MorphismEq prPure) Refl where
    prId _ _ = id
    prPure _ _ = cong {f=pure}

freeGroup : Eq a => Kleislimorphism2 (MonadComposition Oriented List) a (List (Oriented a))
freeGroup = Kleisli2 (MonadCompose . freeGroupReduce) (freeGroupReduce . runMonadCompose) ?hfreeGroup ?hfreeGroup1 ?hfreeGroup2

freeGroupN : (n : Nat) -> Kleislimorphism2 (MonadComposition Oriented List) (Fin n) (List (Oriented (Fin n)))
freeGroupN n = freeGroup {a=Fin n}

functionIntoGroupKleisli : (VerifiedMonad m, Alternative m) => Kleislimorphism2 (MonadComposition Oriented m) a b -> (c -> b) -> (MonadComposition Oriented m) (c -> m (Oriented a))
functionIntoGroupKleisli (Kleisli2 f _ _ _ _) arr = pure $ runMonadCompose . f . arr

functionIntoGroupAction : (VerifiedMonad m, Alternative m) => Kleislimorphism2 (MonadComposition Oriented m) a b -> (MonadComposition Oriented m) (c -> m (Oriented a)) -> (c -> b)
functionIntoGroupAction (Kleisli2 _ g _ _ _) arr = g . join . map MonadCompose . (<*>) arr . pure

functionIntoGroup : (VerifiedMonad m, Alternative m) => Kleislimorphism2 (MonadComposition Oriented m) a b -> Kleislimorphism2 (MonadComposition Oriented m) (c -> m (Oriented a)) (c -> b)
functionIntoGroup k@(Kleisli2 f g prId prPure prEmpty) = Kleisli2 (functionIntoGroupKleisli k) (functionIntoGroupAction k) (MorphismEq {f1=(functionIntoGroupAction k) . (functionIntoGroupKleisli k)} {f2=id} ?hfunctionIntoGroup) ?hfunctionIntoGroup1 ?hfunctionIntoGroup2

--groupRelations : (Monad m, Alternative m) => (f : Kleislimorphism2 m a b) -> Kleislimorphism2 m a (x : m b ** ((presentationMap f x) = empty {f=m}))
--groupRelations (Kleisli2 f g) = Kleisli2 f' g' where
--    f' x = ?h1
--    g' y = ?h2

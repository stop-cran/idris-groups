module MonadComposition

import MonadSwap
import Control.Monad.Identity
import Control.Monad.Trans
import Interfaces.Verified

%access public export
%default total


data MonadComposition : (m : Type -> Type) -> (n: Type -> Type) -> a -> Type where
    MonadCompose : (VerifiedMonadSwap m, VerifiedMonad n) => n (m a) -> MonadComposition m n a

runMonadCompose : MonadComposition m n a -> n (m a)
runMonadCompose (MonadCompose x) = x

mapMonadCompose : (VerifiedMonadSwap m, VerifiedMonad n) => (n (m a) -> n (m b)) -> MonadComposition m n a -> MonadComposition m n b
mapMonadCompose f (MonadCompose x) = MonadCompose $ f x

Eq (n (m a)) => Eq (MonadComposition m n a) where
    (MonadCompose x) == (MonadCompose y) = x == y

Ord (n (m a)) => Ord (MonadComposition m n a) where
    compare (MonadCompose x) (MonadCompose y) = compare x y
    
(VerifiedMonadSwap m, VerifiedMonad n) => Functor (MonadComposition m n) where
    map = mapMonadCompose . map . map

(VerifiedMonadSwap m, VerifiedMonad n) => Applicative (MonadComposition m n) where
    pure = MonadCompose . pure . pure
    (<*>) (MonadCompose f) = mapMonadCompose $ liftA2 (<*>) f

(VerifiedMonadSwap m, VerifiedMonad n) => Monad (MonadComposition m n) where
    join = mapMonadCompose $ map join . flip (>>=) swap . map (map runMonadCompose)

(VerifiedMonadSwap m, VerifiedMonad n) => VerifiedFunctor (MonadComposition m n) where
    functorIdentity g prId (MonadCompose x) = cong (functorIdentity (map g) (\y => functorIdentity g prId y) x)
    functorComposition (MonadCompose x) g1 g2 = cong {f=MonadCompose {m} {n}} $ trans
        (functorCong {f=n} {g1=map {f=m} (g2 . g1)} {g2=map {f=m} g2 . map {f=m} g1} (\z => functorComposition {f=m} z g1 g2) x)
        (functorComposition {f=n} x (map g1) (map g2))

(VerifiedMonadSwap m, VerifiedMonad n) => VerifiedApplicative (MonadComposition m n) where
    applicativeMap (MonadCompose x) g = ?happlicativeMapMC
    applicativeIdentity (MonadCompose x) = ?happlicativeIdentityMC
    applicativeComposition (MonadCompose x) (MonadCompose y) (MonadCompose z) = ?happlicativeCompositionMC
    applicativeHomomorphism x g = ?happlicativeHomomorphismMC
    applicativeInterchange x (MonadCompose y) = ?happlicativeInterchangeMC

(VerifiedMonadSwap m, VerifiedMonad n) => VerifiedMonad (MonadComposition m n) where
    monadApplicative (MonadCompose f) (MonadCompose x) = ?hmonadApplicativeC
    monadLeftIdentity x f = ?hmonadLeftIdentityC
    monadRightIdentity (MonadCompose x) = ?hmonadRightIdentityC
    monadAssociativity (MonadCompose x) f g = ?hmonadAssociativityC

--VerifiedMonadSwap m => MonadTrans (MonadComposition m) where
    --lift = MonadCompose . swap . pure

(VerifiedMonadSwap m, VerifiedMonad n, Alternative n) => Alternative (MonadComposition m n) where
    (MonadCompose x) <|> (MonadCompose y) = MonadCompose $ x <|> y
    empty = MonadCompose empty
    
functorIdentityCompose : (VerifiedFunctor f1, VerifiedFunctor f2) =>
    (g : a -> a) -> ((v : a) -> g v = v) ->
    (x : f2 (f1 a)) -> map (map g) x = x
functorIdentityCompose fnId prId x =
    functorIdentity (map fnId) (\y => functorIdentity fnId prId y) x

(VerifiedMonadSwap m, VerifiedMonad k) => MonadSwap (MonadComposition m k) where
    swap x = ?hswapC

(VerifiedMonadSwap m, VerifiedMonad n) => VerifiedMonadSwap (MonadComposition m n) where
    swapIdentity x y eq = ?hswapIdentity1 -- (trans (applicativeMapPure x pure) (cong {f = pure . pure} eq))
    swapMap g (MonadCompose x) = ?hswapMapCompose
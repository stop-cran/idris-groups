module Monomorphism

import Control.Isomorphism
import MorphismEqual

%access public export
%default total

data Monomorphism : a -> b -> Type where
    Mono : (f : a -> b) -> ((c : Type) -> (d : Type) -> {g2 : c -> a} -> {g1 : d -> a} -> MorphismEqual (f . g1) (f . g2) -> MorphismEqual g1 g2) -> Monomorphism a b

monomorphismId : {a : Type} -> Monomorphism a a
monomorphismId = Mono id prF where
    prF _ _ = id

monomorphismCompose : Monomorphism b c -> Monomorphism a b -> Monomorphism a c
monomorphismCompose (Mono f prF) (Mono g prG) = Mono (f . g) prFG where
    prFG t1 t2 = ?hhh
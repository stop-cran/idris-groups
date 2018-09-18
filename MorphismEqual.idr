module MorphismEqual
import Control.Isomorphism

%access public export
%default total


data MorphismEqual : (f1 : a -> b) -> (f2 : c -> d) -> Type where
    MorphismEq : ((x : a) -> (y : c) -> x = y -> f1 x = f2 y) -> MorphismEqual f1 f2

reflFn : (f : a -> b) -> MorphismEqual f f
reflFn _ = MorphismEq pr where
    pr _ _ eq = cong eq

congFn : MorphismEqual f1 f2 -> MorphismEqual g1 g2 -> MorphismEqual (g1 . f1) (g2 . f2)
congFn (MorphismEq prF) (MorphismEq prG) = MorphismEq prGF where
    prGF x y eq = prG (f1 x) (f2 y) (prF x y eq)

transFn : {a1 : Type} -> {b1 : Type} -> {a2 : Type} -> {b2 : Type} -> {a3 : Type} -> {b3 : Type} ->
          {f1 : a1 -> b1} -> {f2 : a2 -> b2} -> {f3 : a3 -> b3} ->
          MorphismEqual f1 f2 -> MorphismEqual f2 f3 -> MorphismEqual f1 f3
transFn (MorphismEq prF12) (MorphismEq prF23) = MorphismEq prF13 where
    prF13 : (x : a1) -> (y : a3) -> (x = y) -> (f1 x = f3 y)
    prF13 x y eq = ?htransFn prF12
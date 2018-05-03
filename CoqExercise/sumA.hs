{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module SumA where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

pred :: Prelude.Int -> Prelude.Int
pred n =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\u -> u)
    n

add :: Prelude.Int -> Prelude.Int -> Prelude.Int
add n m =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> Prelude.succ (add p m))
    n

mul :: Prelude.Int -> Prelude.Int -> Prelude.Int
mul n m =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> add m (mul p m))
    n

sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
sub n m =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub k l)
      m)
    n

data Reflect =
   ReflectT
 | ReflectF

iffP :: Prelude.Bool -> Reflect -> Reflect
iffP _ pb =
  let {_evar_0_ = \_ _ _ -> ReflectT} in
  let {_evar_0_0 = \_ _ _ -> ReflectF} in
  case pb of {
   ReflectT -> _evar_0_ __ __ __;
   ReflectF -> _evar_0_0 __ __ __}

idP :: Prelude.Bool -> Reflect
idP b1 =
  case b1 of {
   Prelude.True -> ReflectT;
   Prelude.False -> ReflectF}

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

type Axiom t = t -> t -> Reflect

data Mixin_of t =
   Mixin (Rel t) (Axiom t)

op :: (Mixin_of a1) -> Rel a1
op m =
  case m of {
   Mixin op0 _ -> op0}

type Type = Mixin_of Any
  -- singleton inductive, whose constructor was Pack
  
type Sort = Any

class0 :: Type -> Mixin_of Sort
class0 cT =
  cT

eq_op :: Type -> Rel Sort
eq_op t =
  op (class0 t)

eqn :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqn m n =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      n)
    (\m' ->
    (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\n' -> eqn m' n')
      n)
    m

eqnP :: Axiom Prelude.Int
eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

nat_eqMixin :: Mixin_of Prelude.Int
nat_eqMixin =
  Mixin eqn eqnP

nat_eqType :: Type
nat_eqType =
  unsafeCoerce nat_eqMixin

addn_rec :: Prelude.Int -> Prelude.Int -> Prelude.Int
addn_rec =
  add

addn :: Prelude.Int -> Prelude.Int -> Prelude.Int
addn =
  addn_rec

subn_rec :: Prelude.Int -> Prelude.Int -> Prelude.Int
subn_rec =
  sub

subn :: Prelude.Int -> Prelude.Int -> Prelude.Int
subn =
  subn_rec

leq :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leq m n =
  eq_op nat_eqType (unsafeCoerce subn m n) (unsafeCoerce 0)

muln_rec :: Prelude.Int -> Prelude.Int -> Prelude.Int
muln_rec =
  mul

muln :: Prelude.Int -> Prelude.Int -> Prelude.Int
muln =
  muln_rec

edivn_rec :: Prelude.Int -> Prelude.Int -> Prelude.Int -> Prod Prelude.Int
             Prelude.Int
edivn_rec d m q =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ -> Pair q m)
    (\m' -> edivn_rec d m' (Prelude.succ q))
    (subn m d)

edivn :: Prelude.Int -> Prelude.Int -> Prod Prelude.Int Prelude.Int
edivn m d =
  case leq (Prelude.succ 0) d of {
   Prelude.True -> edivn_rec (pred d) m 0;
   Prelude.False -> Pair 0 m}

divn :: Prelude.Int -> Prelude.Int -> Prelude.Int
divn m d =
  fst (edivn m d)

sumA :: Prelude.Int -> Prelude.Int
sumA n =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> addn (Prelude.succ p) (sumA p))
    n

sumB :: Prelude.Int -> Prelude.Int
sumB n =
  divn (muln n (Prelude.succ n)) (Prelude.succ (Prelude.succ 0))


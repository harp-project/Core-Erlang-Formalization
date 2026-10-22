{-# LANGUAGE StrictData, StandaloneDeriving #-}
module RocqExtraction where

import qualified Prelude
import qualified Data.Bits
import qualified Data.Char
import qualified Data.HashMap.Strict
import qualified Data.Hashable
import qualified Data.HashSet
import qualified Data.List
import qualified GHC.Base
import Control.DeepSeq

data Uint =
   Nil
 | D0 Uint
 | D1 Uint
 | D2 Uint
 | D3 Uint
 | D4 Uint
 | D5 Uint
 | D6 Uint
 | D7 Uint
 | D8 Uint
 | D9 Uint

data Signed_int =
   Pos Uint
 | Neg Uint

revapp :: Uint -> Uint -> Uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Uint -> Uint
rev d =
  revapp d Nil

double :: Uint -> Uint
double d =
  case d of {
   Nil -> Nil;
   D0 d0 -> D0 (double d0);
   D1 d0 -> D2 (double d0);
   D2 d0 -> D4 (double d0);
   D3 d0 -> D6 (double d0);
   D4 d0 -> D8 (double d0);
   D5 d0 -> D0 (succ_double d0);
   D6 d0 -> D2 (succ_double d0);
   D7 d0 -> D4 (succ_double d0);
   D8 d0 -> D6 (succ_double d0);
   D9 d0 -> D8 (succ_double d0)}

succ_double :: Uint -> Uint
succ_double d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 (double d0);
   D1 d0 -> D3 (double d0);
   D2 d0 -> D5 (double d0);
   D3 d0 -> D7 (double d0);
   D4 d0 -> D9 (double d0);
   D5 d0 -> D1 (succ_double d0);
   D6 d0 -> D3 (succ_double d0);
   D7 d0 -> D5 (succ_double d0);
   D8 d0 -> D7 (succ_double d0);
   D9 d0 -> D9 (succ_double d0)}

pred :: Prelude.Integer -> Prelude.Integer
pred = (\n -> Prelude.max 0 (Prelude.pred n))

data N =
   N0
 | Npos Prelude.Integer

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x =
  g (f x)

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb n m =
  (Prelude.<=) (Prelude.succ n) m

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

pred_N :: Prelude.Integer -> N
pred_N x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> Npos ((\x -> 2 Prelude.* x) p))
    (\p -> Npos (pred_double p))
    (\_ -> N0)
    x

iter :: (a1 -> a1) -> a1 -> Prelude.Integer -> a1
iter f x n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\n' -> f (iter f (iter f x n') n'))
    (\n' -> iter f (iter f x n') n')
    (\_ -> f x)
    n

div2 :: Prelude.Integer -> Prelude.Integer
div2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> p0)
    (\p0 -> p0)
    (\_ -> 1)
    p

div2_up :: Prelude.Integer -> Prelude.Integer
div2_up p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> (Prelude.+ 1) p0)
    (\p0 -> p0)
    (\_ -> 1)
    p

compare_cont :: Prelude.Ordering -> Prelude.Integer -> Prelude.Integer ->
                Prelude.Ordering
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Prelude.GT p q)
      (\_ -> Prelude.GT)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Prelude.LT p q)
      (\q -> compare_cont r p q)
      (\_ -> Prelude.GT)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Prelude.LT)
      (\_ -> Prelude.LT)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare =
  compare_cont Prelude.EQ

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) (lor p0 q0))
      (\_ -> p)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x) (lor p0 q0))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> q)
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) q0)
      (\_ -> q)
      q)
    p

land :: Prelude.Integer -> Prelude.Integer -> N
land p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> nsucc_double (land p0 q0))
      (\q0 -> ndouble (land p0 q0))
      (\_ -> Npos 1)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (land p0 q0))
      (\q0 -> ndouble (land p0 q0))
      (\_ -> N0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Npos 1)
      (\_ -> N0)
      (\_ -> Npos 1)
      q)
    p

ldiff :: Prelude.Integer -> Prelude.Integer -> N
ldiff p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (ldiff p0 q0))
      (\q0 -> nsucc_double (ldiff p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x) p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (ldiff p0 q0))
      (\q0 -> ndouble (ldiff p0 q0))
      (\_ -> Npos p)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> N0)
      (\_ -> Npos 1)
      (\_ -> N0)
      q)
    p

iter0 :: (a1 -> a1) -> a1 -> Prelude.Integer -> a1
iter0 f x n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\n' -> f (iter0 f (iter0 f x n') n'))
    (\n' -> iter0 f (iter0 f x n') n')
    (\_ -> f x)
    n

to_little_uint :: Prelude.Integer -> Uint
to_little_uint p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> succ_double (to_little_uint p0))
    (\p0 -> double (to_little_uint p0))
    (\_ -> D1 Nil)
    p

to_uint :: Prelude.Integer -> Uint
to_uint p =
  rev (to_little_uint p)

succ_pos :: N -> Prelude.Integer
succ_pos n =
  case n of {
   N0 -> 1;
   Npos p -> (Prelude.+ 1) p}

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> ldiff p q}}

succ_double0 :: N -> N
succ_double0 x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

double0 :: N -> N
double0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

compare0 :: N -> N -> Prelude.Ordering
compare0 n m =
  case n of {
   N0 -> case m of {
          N0 -> Prelude.EQ;
          Npos _ -> Prelude.LT};
   Npos n' -> case m of {
               N0 -> Prelude.GT;
               Npos m' -> compare n' m'}}

leb :: N -> N -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

pos_div_eucl :: Prelude.Integer -> N -> (,) N N
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double0 r} in
      case leb b r' of {
       Prelude.True -> (,) (succ_double0 q)
        ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
          r' b);
       Prelude.False -> (,) (double0 q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double0 r} in
      case leb b r' of {
       Prelude.True -> (,) (succ_double0 q)
        ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
          r' b);
       Prelude.False -> (,) (double0 q) r'}})
    (\_ ->
    case b of {
     N0 -> (,) N0 (Npos 1);
     Npos p ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\_ -> (,) N0 (Npos 1))
        (\_ -> (,) N0 (Npos 1))
        (\_ -> (,) (Npos 1) N0)
        p})
    a

add :: N -> N -> N
add n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos ((Prelude.+) p q)}}

mul :: N -> N -> N
mul n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> Npos ((Prelude.*) p q)}}

eqb :: N -> N -> Prelude.Bool
eqb n m =
  case n of {
   N0 -> case m of {
          N0 -> Prelude.True;
          Npos _ -> Prelude.False};
   Npos p -> case m of {
              N0 -> Prelude.False;
              Npos q -> (Prelude.==) p q}}

ltb0 :: N -> N -> Prelude.Bool
ltb0 x y =
  case compare0 x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

div_eucl :: N -> N -> (,) N N
div_eucl a b =
  case a of {
   N0 -> (,) N0 N0;
   Npos na -> case b of {
               N0 -> (,) N0 a;
               Npos _ -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  Prelude.fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  Prelude.snd (div_eucl a b)

to_nat :: N -> Prelude.Integer
to_nat a =
  case a of {
   N0 -> 0;
   Npos p -> (Prelude.id) p}

of_nat :: Prelude.Integer -> N
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> N0)
    (\n' -> Npos ((Prelude.+ 1) n'))
    n

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\x0 -> Prelude.negate x0)
    (\x0 -> (\x -> x) x0)
    x

pow_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow_pos z =
  iter ((Prelude.*) z) ((\x -> x) 1)

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> pow_pos x p)
    (\_ -> 0)
    y

of_N :: N -> Prelude.Integer
of_N n =
  case n of {
   N0 -> 0;
   Npos p -> (\x -> x) p}

div0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div0 = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo0 = (\n m -> if m Prelude.== 0 then n else Prelude.mod n m)

quot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
quot = (\n m -> if m Prelude.== 0 then 0 else Prelude.quot n m)

rem :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
rem = (\n m -> if m Prelude.== 0 then 0 else Prelude.rem n m)

div1 :: Prelude.Integer -> Prelude.Integer
div1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> (\x -> x) (div2 p))
      (\_ -> (\x -> x) (div2 p))
      (\_ -> 0)
      p)
    (\p -> Prelude.negate (div2_up p))
    z

shiftl :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl a n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> a)
    (\p ->
    iter ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a p)
    (\p -> iter div1 a p)
    n

shiftr :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr a n =
  shiftl a (opp n)

lor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> (\x -> x) (lor a0 b0))
      (\b0 -> Prelude.negate (succ_pos (ldiff0 (pred_N b0) (Npos a0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N a0) (Npos b0))))
      (\b0 -> Prelude.negate (succ_pos (land0 (pred_N a0) (pred_N b0))))
      b)
    a

land1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> 0)
      (\b0 -> of_N (land a0 b0))
      (\b0 -> of_N (ldiff0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> 0)
      (\b0 -> of_N (ldiff0 (Npos b0) (pred_N a0)))
      (\b0 -> Prelude.negate (succ_pos (lor0 (pred_N a0) (pred_N b0))))
      b)
    a

pred0 :: Prelude.Integer -> Prelude.Integer
pred0 x =
  (Prelude.+) x (Prelude.negate 1)

abs_N :: Prelude.Integer -> N
abs_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> N0)
    (\p -> Npos p)
    (\p -> Npos p)
    z

to_N :: Prelude.Integer -> N
to_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> N0)
    (\p -> Npos p)
    (\_ -> N0)
    z

to_int :: Prelude.Integer -> Signed_int
to_int n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Pos (D0 Nil))
    (\p -> Pos (to_uint p))
    (\p -> Neg (to_uint p))
    n

iter1 :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> x)
    (\p -> iter0 f x p)
    (\_ -> x)
    n

ones :: Prelude.Integer -> Prelude.Integer
ones n =
  pred0 (shiftl ((\x -> x) 1) n)

nth :: Prelude.Integer -> (([]) a1) -> a1 -> a1
nth n l default0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case l of {
            ([]) -> default0;
            (:) x _ -> x})
    (\m -> case l of {
            ([]) -> default0;
            (:) _ l' -> nth m l' default0})
    n

nth_error :: (([]) a1) -> Prelude.Integer -> Prelude.Maybe a1
nth_error l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) x _ -> Prelude.Just x})
    (\n0 ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) _ l' -> nth_error l' n0})
    n

rev_append :: (([]) a1) -> (([]) a1) -> ([]) a1
rev_append l l' =
  case l of {
   ([]) -> l';
   (:) a l0 -> rev_append l0 ((:) a l')}

zero :: Prelude.Char
zero =
  '\000'

one :: Prelude.Char
one =
  '\001'

shift :: Prelude.Bool -> Prelude.Char -> Prelude.Char
shift c a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a1 a2 a3 a4 a5 a6 a7 _ ->
    (\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr (
      (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+
      (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+
      (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+
      (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+
      (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+
      (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+
      (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+
      (if b7 then Data.Bits.shiftL 1 7 else 0)))
    c a1 a2 a3 a4 a5 a6 a7)
    a

ascii_of_pos :: Prelude.Integer -> Prelude.Char
ascii_of_pos =
  let {
   loop n p =
     (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
       (\_ -> zero)
       (\n' ->
       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
         (\p' -> shift Prelude.True (loop n' p'))
         (\p' -> shift Prelude.False (loop n' p'))
         (\_ -> one)
         p)
       n}
  in loop (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
       (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))

ascii_of_N :: N -> Prelude.Char
ascii_of_N n =
  case n of {
   N0 -> zero;
   Npos p -> ascii_of_pos p}

ascii_of_nat :: Prelude.Integer -> Prelude.Char
ascii_of_nat a =
  ascii_of_N (of_nat a)

n_of_digits :: (([]) Prelude.Bool) -> N
n_of_digits l =
  case l of {
   ([]) -> N0;
   (:) b l' ->
    add (case b of {
          Prelude.True -> Npos 1;
          Prelude.False -> N0})
      (mul (Npos ((\x -> 2 Prelude.* x) 1)) (n_of_digits l'))}

n_of_ascii :: Prelude.Char -> N
n_of_ascii a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits ((:) a0 ((:) a1 ((:) a2 ((:) a3 ((:) a4 ((:) a5 ((:) a6 ((:)
      a7 ([]))))))))))
    a

nat_of_ascii :: Prelude.Char -> Prelude.Integer
nat_of_ascii a =
  to_nat (n_of_ascii a)

compare1 :: Prelude.Char -> Prelude.Char -> Prelude.Ordering
compare1 a b =
  compare0 (n_of_ascii a) (n_of_ascii b)

compare2 :: Prelude.String -> Prelude.String -> Prelude.Ordering
compare2 s1 s2 =
  case s1 of {
   ([]) -> case s2 of {
            ([]) -> Prelude.EQ;
            (:) _ _ -> Prelude.LT};
   (:) c1 s1' ->
    case s2 of {
     ([]) -> Prelude.GT;
     (:) c2 s2' ->
      case compare1 c1 c2 of {
       Prelude.EQ -> compare2 s1' s2';
       x -> x}}}

string_of_list_ascii :: (([]) Prelude.Char) -> Prelude.String
string_of_list_ascii s =
  case s of {
   ([]) -> "";
   (:) ch s0 -> (:) ch (string_of_list_ascii s0)}





prod_map :: (a1 -> a2) -> (a3 -> a4) -> ((,) a1 a3) -> (,) a2 a4
prod_map f g p =
  (,) (f (Prelude.fst p)) (g (Prelude.snd p))





reverse :: (([]) a1) -> ([]) a1
reverse l =
  rev_append l ([])

z_to_little_endian :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
                      -> ([]) Prelude.Integer
z_to_little_endian m n =
  iter1 m (\rec0 z -> (:) (land1 z (ones n)) (rec0 (shiftr z n))) (\_ ->
    ([]))

little_endian_to_Z :: Prelude.Integer -> (([]) Prelude.Integer) ->
                      Prelude.Integer
little_endian_to_Z n bs =
  case bs of {
   ([]) -> 0;
   (:) b bs0 -> lor1 b (shiftl (little_endian_to_Z n bs0) n)}

bv_modulus :: N -> Prelude.Integer
bv_modulus n =
  pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) (of_N n)

bv_half_modulus :: N -> Prelude.Integer
bv_half_modulus n =
  div0 (bv_modulus n) ((\x -> x) ((\x -> 2 Prelude.* x) 1))

bv_wrap :: N -> Prelude.Integer -> Prelude.Integer
bv_wrap n z =
  modulo0 z (bv_modulus n)

bv_swrap :: N -> Prelude.Integer -> Prelude.Integer
bv_swrap n z =
  (Prelude.-) (bv_wrap n ((Prelude.+) z (bv_half_modulus n)))
    (bv_half_modulus n)

type Bv = Prelude.Integer
  -- singleton inductive, whose constructor was BV
  
bv_unsigned :: N -> Bv -> Prelude.Integer
bv_unsigned _ b =
  b

bv_signed :: N -> Bv -> Prelude.Integer
bv_signed n b =
  bv_swrap n (bv_unsigned n b)

z_to_bv :: N -> Prelude.Integer -> Bv
z_to_bv =
  bv_wrap

bv_extract :: N -> N -> N -> Bv -> Bv
bv_extract n s l b =
  z_to_bv l (shiftr (bv_unsigned n b) (of_N s))

bv_concat :: N -> N -> N -> Bv -> Bv -> Bv
bv_concat n n1 n2 b1 b2 =
  z_to_bv n (lor1 (shiftl (bv_unsigned n1 b1) (of_N n2)) (bv_unsigned n2 b2))

data Bvn =
   Bv_to_bvn N Bv

bvn_n :: Bvn -> N
bvn_n b =
  case b of {
   Bv_to_bvn bvn_n0 _ -> bvn_n0}

bvn_val :: Bvn -> Bv
bvn_val b =
  case b of {
   Bv_to_bvn _ bvn_val0 -> bvn_val0}

bvn_unsigned :: Bvn -> Prelude.Integer
bvn_unsigned b =
  bv_unsigned (bvn_n b) (bvn_val b)

null :: (([]) a1) -> Prelude.Bool
null l =
  case l of {
   ([]) -> Prelude.True;
   (:) _ _ -> Prelude.False}

replace_nth_error :: (([]) a1) -> Prelude.Integer -> a1 -> Prelude.Maybe
                     (([]) a1)
replace_nth_error l i e =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) _ xs -> Prelude.Just ((:) e xs)})
    (\n ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) x xs ->
      case replace_nth_error xs n e of {
       Prelude.Just l' -> Prelude.Just ((:) x l');
       Prelude.Nothing -> Prelude.Nothing}})
    i

type PID = Prelude.Integer

data Lit =
   Atom Prelude.String
 | Integer Prelude.Integer

data BinType =
   IntType
 | FloatType
 | BinaryType
 | BitstringType
 | Utf8Type
 | Utf16Type
 | Utf32Type

data BinSign =
   Signed
 | Unsigned

data BinEnd =
   BigEndian
 | LittleEndian
 | NativeEndian

data Segment t1 t2 =
   Build_Segment t1 t2 Prelude.Integer BinType BinSign BinEnd

val :: (Segment a1 a2) -> a1
val s =
  case s of {
   Build_Segment val0 _ _ _ _ _ -> val0}

size :: (Segment a1 a2) -> a2
size s =
  case s of {
   Build_Segment _ size0 _ _ _ _ -> size0}

unit0 :: (Segment a1 a2) -> Prelude.Integer
unit0 s =
  case s of {
   Build_Segment _ _ unit1 _ _ _ -> unit1}

type0 :: (Segment a1 a2) -> BinType
type0 s =
  case s of {
   Build_Segment _ _ _ type1 _ _ -> type1}

sign :: (Segment a1 a2) -> BinSign
sign s =
  case s of {
   Build_Segment _ _ _ _ sign0 _ -> sign0}

endian :: (Segment a1 a2) -> BinEnd
endian s =
  case s of {
   Build_Segment _ _ _ _ _ endian0 -> endian0}

type FunId = (,) Prelude.Integer Prelude.Integer

type Var = Prelude.Integer

data Exp =
   VVal Val
 | EExp NonVal
data Val =
   VNil
 | VLit Lit
 | VPid PID
 | VCons Val Val
 | VTuple (([]) Val)
 | VMap (([]) ((,) Val Val))
 | VVar Var
 | VFunId FunId
 | VClos (([]) ((,) ((,) Prelude.Integer Prelude.Integer) Exp)) Prelude.Integer 
 Prelude.Integer Exp
 | VBitstring Bvn
data NonVal =
   EFun Prelude.Integer Exp
 | EValues (([]) Exp)
 | ECons Exp Exp
 | ETuple (([]) Exp)
 | EMap (([]) ((,) Exp Exp))
 | ECall Exp Exp (([]) Exp)
 | EPrimOp Prelude.String (([]) Exp)
 | EApp Exp (([]) Exp)
 | ECase Exp (([]) ((,) ((,) (([]) Pat) Exp) Exp))
 | ELet Prelude.Integer Exp Exp
 | ESeq Exp Exp
 | ELetRec (([]) ((,) Prelude.Integer Exp)) Exp
 | ETry Exp Prelude.Integer Exp Prelude.Integer Exp
 | EBin (([]) Exp)
 | ESeg (Segment Exp Exp)
data Pat =
   PVar
 | PLit Lit
 | PCons Pat Pat
 | PTuple (([]) Pat)
 | PMap (([]) ((,) Pat Pat))
 | PNil
 | PBin (([]) (Segment Pat Val))

errorVal :: Val
errorVal =
  VLit (Atom "error")

data ExcClass =
   Error
 | Throw
 | Exit

exclass_to_value :: ExcClass -> Val
exclass_to_value ex =
  case ex of {
   Error -> VLit (Atom "error");
   Throw -> VLit (Atom "throw");
   Exit -> VLit (Atom "exit")}

type Exception = (,) ((,) ExcClass Val) Val

badarith :: Val -> Exception
badarith v =
  (,) ((,) Error (VLit (Atom "badarith"))) v

badarg :: Val -> Exception
badarg v =
  (,) ((,) Error (VLit (Atom "badarg"))) v

badmap :: Val -> Exception
badmap v =
  (,) ((,) Error (VLit (Atom "badmap"))) v

badkey :: Val -> Exception
badkey v =
  (,) ((,) Error (VLit (Atom "badkey"))) v

undef :: Val -> Exception
undef v =
  (,) ((,) Error (VLit (Atom "undef"))) v

badfun :: Val -> Exception
badfun v =
  (,) ((,) Error (VLit (Atom "badfun"))) v

badarity :: Val -> Exception
badarity v =
  (,) ((,) Error (VLit (Atom "badarity"))) v

if_clause :: Exception
if_clause =
  (,) ((,) Error (VLit (Atom "if_clause"))) errorVal

timeout_value :: Val -> Exception
timeout_value v =
  (,) ((,) Error (VLit (Atom "timeout_value"))) v

type ValSeq = ([]) Val

data Redex =
   RExp Exp
 | RValSeq ValSeq
 | RExc Exception
 | RBox

convert_to_closlist :: (([]) ((,) ((,) Prelude.Integer Prelude.Integer) Exp))
                       -> ([]) Val
convert_to_closlist l =
  (Prelude.map) (\pat ->
    case pat of {
     (,) y e -> case y of {
                 (,) id vc -> VClos l id vc e}})
    l

patVars :: Pat -> Prelude.Integer
patVars p =
  case p of {
   PVar -> Prelude.succ 0;
   PCons hd tl -> (Prelude.+) (patVars hd) (patVars tl);
   PTuple l -> Prelude.foldr (\x y -> (Prelude.+) (patVars x) y) 0 l;
   PMap l ->
    Prelude.foldr (\pat y ->
      case pat of {
       (,) a b -> (Prelude.+) ((Prelude.+) (patVars a) (patVars b)) y}) 0 l;
   PBin l ->
    Prelude.foldr (\seg acc -> (Prelude.+) (patVars (val seg)) acc) 0 l;
   _ -> 0}

patListVars :: (([]) Pat) -> Prelude.Integer
patListVars pl =
  Prelude.foldr (\x y -> (Prelude.+) (patVars x) y) 0 pl

type Renaming = Prelude.Integer -> Prelude.Integer

upren :: Renaming -> Renaming
upren _UU03c1_ n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' -> Prelude.succ (_UU03c1_ n'))
    n

iterate :: (a1 -> a1) -> Prelude.Integer -> a1 -> a1
iterate f n a =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> a)
    (\n' -> f (iterate f n' a))
    n

rename :: Renaming -> Exp -> Exp
rename _UU03c1_ ex =
  case ex of {
   VVal e -> VVal (renameVal _UU03c1_ e);
   EExp e -> EExp (renameNonVal _UU03c1_ e)}

renameVal :: Renaming -> Val -> Val
renameVal _UU03c1_ ex =
  case ex of {
   VCons hd tl -> VCons (renameVal _UU03c1_ hd) (renameVal _UU03c1_ tl);
   VTuple l -> VTuple ((Prelude.map) (renameVal _UU03c1_) l);
   VMap l -> VMap
    ((Prelude.map) (prod_map (renameVal _UU03c1_) (renameVal _UU03c1_)) l);
   VVar n -> VVar (_UU03c1_ n);
   VFunId n0 -> case n0 of {
                 (,) n a -> VFunId ((,) (_UU03c1_ n) a)};
   VClos ext id vl e -> VClos
    ((Prelude.map) (\pat ->
      case pat of {
       (,) y x ->
        case y of {
         (,) i ls -> (,) ((,) i ls)
          (rename
            (iterate upren ((Prelude.+) ((Data.List.genericLength) ext) ls)
              _UU03c1_)
            x)}})
      ext)
    id vl
    (rename
      (iterate upren ((Prelude.+) ((Data.List.genericLength) ext) vl)
        _UU03c1_)
      e);
   VBitstring b -> VBitstring b;
   _ -> ex}

renameNonVal :: Renaming -> NonVal -> NonVal
renameNonVal _UU03c1_ ex =
  case ex of {
   EFun vl e -> EFun vl (rename (iterate upren vl _UU03c1_) e);
   EValues el -> EValues ((Prelude.map) (rename _UU03c1_) el);
   ECons hd tl -> ECons (rename _UU03c1_ hd) (rename _UU03c1_ tl);
   ETuple l -> ETuple ((Prelude.map) (rename _UU03c1_) l);
   EMap l -> EMap
    ((Prelude.map) (prod_map (rename _UU03c1_) (rename _UU03c1_)) l);
   ECall m f l -> ECall (rename _UU03c1_ m) (rename _UU03c1_ f)
    ((Prelude.map) (rename _UU03c1_) l);
   EPrimOp f l -> EPrimOp f ((Prelude.map) (rename _UU03c1_) l);
   EApp e l -> EApp (rename _UU03c1_ e) ((Prelude.map) (rename _UU03c1_) l);
   ECase e l -> ECase (rename _UU03c1_ e)
    ((Prelude.map) (\pat ->
      case pat of {
       (,) y0 y ->
        case y0 of {
         (,) p x -> (,) ((,) ((Prelude.map) (renamePat _UU03c1_) p)
          (rename (iterate upren (patListVars p) _UU03c1_) x))
          (rename (iterate upren (patListVars p) _UU03c1_) y)}})
      l);
   ELet l e1 e2 -> ELet l (rename _UU03c1_ e1)
    (rename (iterate upren l _UU03c1_) e2);
   ESeq e1 e2 -> ESeq (rename _UU03c1_ e1) (rename _UU03c1_ e2);
   ELetRec l e -> ELetRec
    ((Prelude.map) (\pat ->
      case pat of {
       (,) n x -> (,) n
        (rename
          (iterate upren ((Prelude.+) ((Data.List.genericLength) l) n)
            _UU03c1_)
          x)})
      l)
    (rename (iterate upren ((Data.List.genericLength) l) _UU03c1_) e);
   ETry e1 vl1 e2 vl2 e3 -> ETry (rename _UU03c1_ e1) vl1
    (rename (iterate upren vl1 _UU03c1_) e2) vl2
    (rename (iterate upren vl2 _UU03c1_) e3);
   EBin l -> EBin ((Prelude.map) (rename _UU03c1_) l);
   ESeg seg ->
    case seg of {
     Build_Segment val0 size0 u t s e -> ESeg (Build_Segment
      (rename _UU03c1_ val0) (rename _UU03c1_ size0) u t s e)}}

renamePat :: Renaming -> Pat -> Pat
renamePat _UU03c1_ p =
  case p of {
   PCons hd tl -> PCons (renamePat _UU03c1_ hd) (renamePat _UU03c1_ tl);
   PTuple l -> PTuple ((Prelude.map) (renamePat _UU03c1_) l);
   PMap l -> PMap
    ((Prelude.map) (prod_map (renamePat _UU03c1_) (renamePat _UU03c1_)) l);
   PBin segments -> PBin
    ((Prelude.map) (\seg ->
      case seg of {
       Build_Segment val0 size0 u t s e -> Build_Segment
        (renamePat _UU03c1_ val0) (renameVal _UU03c1_ size0) u t s e})
      segments);
   _ -> p}

type Substitution = Prelude.Integer -> Prelude.Either Val Prelude.Integer

idsubst :: Substitution
idsubst x =
  Prelude.Right x

shift0 :: Substitution -> Substitution
shift0 _UU03be_ s =
  case _UU03be_ s of {
   Prelude.Left exp -> Prelude.Left (renameVal (\x -> Prelude.succ x) exp);
   Prelude.Right num -> Prelude.Right (Prelude.succ num)}

up_subst :: Substitution -> Substitution
up_subst _UU03be_ x =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Right 0)
    (\x' -> shift0 _UU03be_ x')
    x

subst :: Substitution -> Exp -> Exp
subst = 
  (\_UU03be_ base ->
    case base of {
     VVal v -> 
        let v' = (substVal _UU03be_ v)
        in v' `deepseq` VVal v';
     EExp e -> 
        let e' = (substNonVal _UU03be_ e)
        in e' `deepseq` EExp e'})


substVal :: Substitution -> Val -> Val
substVal _UU03be_ ex =
  case ex of {
   VCons hd tl -> VCons (substVal _UU03be_ hd) (substVal _UU03be_ tl);
   VTuple l -> VTuple ((Prelude.map) (substVal _UU03be_) l);
   VMap l -> VMap
    ((Prelude.map) (prod_map (substVal _UU03be_) (substVal _UU03be_)) l);
   VVar n ->
    case _UU03be_ n of {
     Prelude.Left exp -> exp;
     Prelude.Right num -> VVar num};
   VFunId n0 ->
    case n0 of {
     (,) n a ->
      case _UU03be_ n of {
       Prelude.Left exp -> exp;
       Prelude.Right num -> VFunId ((,) num a)}};
   VClos ext id vl e -> VClos
    ((Prelude.map) (\pat ->
      case pat of {
       (,) y x ->
        case y of {
         (,) i ls -> (,) ((,) i ls)
          (subst
            (iterate up_subst
              ((Prelude.+) ((Data.List.genericLength) ext) ls) _UU03be_)
            x)}})
      ext)
    id vl
    (subst
      (iterate up_subst ((Prelude.+) ((Data.List.genericLength) ext) vl)
        _UU03be_)
      e);
   VBitstring b -> VBitstring b;
   _ -> ex}

substNonVal :: Substitution -> NonVal -> NonVal
substNonVal _UU03be_ ex =
  case ex of {
   EFun vl e -> EFun vl (subst (iterate up_subst vl _UU03be_) e);
   EValues el -> EValues ((Prelude.map) (subst _UU03be_) el);
   ECons hd tl -> ECons (subst _UU03be_ hd) (subst _UU03be_ tl);
   ETuple l -> ETuple ((Prelude.map) (subst _UU03be_) l);
   EMap l -> EMap
    ((Prelude.map) (prod_map (subst _UU03be_) (subst _UU03be_)) l);
   ECall m f l -> ECall (subst _UU03be_ m) (subst _UU03be_ f)
    ((Prelude.map) (subst _UU03be_) l);
   EPrimOp f l -> EPrimOp f ((Prelude.map) (subst _UU03be_) l);
   EApp e l -> EApp (subst _UU03be_ e) ((Prelude.map) (subst _UU03be_) l);
   ECase e l -> ECase (subst _UU03be_ e)
    ((Prelude.map) (\pat ->
      case pat of {
       (,) y0 y ->
        case y0 of {
         (,) p x -> (,) ((,) ((Prelude.map) (substPat _UU03be_) p)
          (subst (iterate up_subst (patListVars p) _UU03be_) x))
          (subst (iterate up_subst (patListVars p) _UU03be_) y)}})
      l);
   ELet l e1 e2 -> ELet l (subst _UU03be_ e1)
    (subst (iterate up_subst l _UU03be_) e2);
   ESeq e1 e2 -> ESeq (subst _UU03be_ e1) (subst _UU03be_ e2);
   ELetRec l e -> ELetRec
    ((Prelude.map) (\pat ->
      case pat of {
       (,) n x -> (,) n
        (subst
          (iterate up_subst ((Prelude.+) ((Data.List.genericLength) l) n)
            _UU03be_)
          x)})
      l)
    (subst (iterate up_subst ((Data.List.genericLength) l) _UU03be_) e);
   ETry e1 vl1 e2 vl2 e3 -> ETry (subst _UU03be_ e1) vl1
    (subst (iterate up_subst vl1 _UU03be_) e2) vl2
    (subst (iterate up_subst vl2 _UU03be_) e3);
   EBin l -> EBin ((Prelude.map) (subst _UU03be_) l);
   ESeg seg ->
    case seg of {
     Build_Segment val0 size0 u t s e -> ESeg (Build_Segment
      (subst _UU03be_ val0) (subst _UU03be_ size0) u t s e)}}

substPat :: Substitution -> Pat -> Pat
substPat _UU03c3_ p =
  case p of {
   PCons hd tl -> PCons (substPat _UU03c3_ hd) (substPat _UU03c3_ tl);
   PTuple l -> PTuple ((Prelude.map) (substPat _UU03c3_) l);
   PMap l -> PMap
    ((Prelude.map) (prod_map (substPat _UU03c3_) (substPat _UU03c3_)) l);
   PBin segments -> PBin
    ((Prelude.map) (\seg ->
      case seg of {
       Build_Segment val0 size0 u t s e -> Build_Segment
        (substPat _UU03c3_ val0) (substVal _UU03c3_ size0) u t s e})
      segments);
   _ -> p}

scons :: a1 -> (Prelude.Integer -> a1) -> Prelude.Integer -> a1
scons s _UU03c3_ x =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> s)
    (\y -> _UU03c3_ y)
    x

list_subst :: (([]) Val) -> Substitution -> Substitution
list_subst l _UU03be_ =
  Prelude.foldr (\v acc -> scons (Prelude.Left v) acc) _UU03be_ l

cmp :: Prelude.String -> Prelude.String -> Prelude.Ordering
cmp =
  compare2

funid_eqb :: FunId -> FunId -> Prelude.Bool
funid_eqb v1 v2 =
  case v1 of {
   (,) fid1 num1 ->
    case v2 of {
     (,) fid2 num2 ->
      (Prelude.&&) ((Prelude.==) fid1 fid2) ((Prelude.==) num1 num2)}}

bvn_eqb :: Bvn -> Bvn -> Prelude.Bool
bvn_eqb b1 b2 =
  (Prelude.&&) (eqb (bvn_n b1) (bvn_n b2))
    ((Prelude.==) (bvn_unsigned b1) (bvn_unsigned b2))

val_eqb :: Val -> Val -> Prelude.Bool
val_eqb e1 e2 =
  case e1 of {
   VNil -> case e2 of {
            VNil -> Prelude.True;
            _ -> Prelude.False};
   VLit l -> case e2 of {
              VLit l' -> (Prelude.==) l l';
              _ -> Prelude.False};
   VPid _ -> case e2 of {
              VPid _ -> Prelude.True;
              _ -> Prelude.False};
   VCons hd tl ->
    case e2 of {
     VCons hd' tl' -> (Prelude.&&) (val_eqb hd hd') (val_eqb tl tl');
     _ -> Prelude.False};
   VTuple l ->
    case e2 of {
     VTuple l' ->
      let {
       blist l0 l'0 =
         case l0 of {
          ([]) ->
           case l'0 of {
            ([]) -> Prelude.True;
            (:) _ _ -> Prelude.False};
          (:) x xs ->
           case l'0 of {
            ([]) -> Prelude.False;
            (:) x' xs' -> (Prelude.&&) (val_eqb x x') (blist xs xs')}}}
      in blist l l';
     _ -> Prelude.False};
   VMap l ->
    case e2 of {
     VMap l' ->
      let {
       blist l0 l'0 =
         case l0 of {
          ([]) ->
           case l'0 of {
            ([]) -> Prelude.True;
            (:) _ _ -> Prelude.False};
          (:) y0 xs ->
           case y0 of {
            (,) x y ->
             case l'0 of {
              ([]) -> Prelude.False;
              (:) y1 xs' ->
               case y1 of {
                (,) x' y' ->
                 (Prelude.&&) (val_eqb x x')
                   ((Prelude.&&) (val_eqb y y') (blist xs xs'))}}}}}
      in blist l l';
     _ -> Prelude.False};
   VVar v -> case e2 of {
              VVar v' -> (Prelude.==) v v';
              _ -> Prelude.False};
   VFunId v -> case e2 of {
                VFunId v' -> funid_eqb v v';
                _ -> Prelude.False};
   VClos _ id _ _ ->
    case e2 of {
     VClos _ id' _ _ -> (Prelude.==) id id';
     _ -> Prelude.False};
   VBitstring b1 ->
    case e2 of {
     VBitstring b2 -> bvn_eqb b1 b2;
     _ -> Prelude.False}}

string_ltb :: Prelude.String -> Prelude.String -> Prelude.Bool
string_ltb s1 s2 =
  case cmp s1 s2 of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

lit_ltb :: Lit -> Lit -> Prelude.Bool
lit_ltb l1 l2 =
  case l1 of {
   Atom s ->
    case l2 of {
     Atom s' -> string_ltb s s';
     Integer _ -> Prelude.False};
   Integer x ->
    case l2 of {
     Atom _ -> Prelude.True;
     Integer x' -> (Prelude.<) x x'}}

list_less :: (a1 -> a1 -> Prelude.Bool) -> (a1 -> a1 -> Prelude.Bool) ->
             (([]) a1) -> (([]) a1) -> Prelude.Bool
list_less less eq a b =
  case a of {
   ([]) -> case b of {
            ([]) -> Prelude.False;
            (:) _ _ -> Prelude.True};
   (:) x xs ->
    case b of {
     ([]) -> Prelude.False;
     (:) y ys ->
      case eq x y of {
       Prelude.True -> list_less less eq xs ys;
       Prelude.False -> less x y}}}

list_equal :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> (([]) a1) ->
              Prelude.Bool
list_equal eq a b =
  case a of {
   ([]) -> case b of {
            ([]) -> Prelude.True;
            (:) _ _ -> Prelude.False};
   (:) x xs ->
    case b of {
     ([]) -> Prelude.False;
     (:) y ys ->
      case eq x y of {
       Prelude.True -> list_equal eq xs ys;
       Prelude.False -> Prelude.False}}}

val_ltb :: Val -> Val -> Prelude.Bool
val_ltb k v =
  case k of {
   VNil ->
    case v of {
     VCons _ _ -> Prelude.True;
     VBitstring _ -> Prelude.True;
     _ -> Prelude.False};
   VLit l -> case v of {
              VLit l' -> lit_ltb l l';
              _ -> Prelude.True};
   VPid _ ->
    case v of {
     VNil -> Prelude.True;
     VCons _ _ -> Prelude.True;
     VTuple _ -> Prelude.True;
     VMap _ -> Prelude.True;
     VBitstring _ -> Prelude.True;
     _ -> Prelude.False};
   VCons hd tl ->
    case v of {
     VCons hd' tl' ->
      case val_eqb hd hd' of {
       Prelude.True -> val_ltb tl tl';
       Prelude.False -> val_ltb hd hd'};
     VBitstring _ -> Prelude.True;
     _ -> Prelude.False};
   VTuple l ->
    case v of {
     VNil -> Prelude.True;
     VCons _ _ -> Prelude.True;
     VTuple l' ->
      (Prelude.||)
        (ltb ((Data.List.genericLength) l) ((Data.List.genericLength) l'))
        ((Prelude.&&)
          ((Prelude.==) ((Data.List.genericLength) l)
            ((Data.List.genericLength) l'))
          (list_less val_ltb val_eqb l l'));
     VMap _ -> Prelude.True;
     VBitstring _ -> Prelude.True;
     _ -> Prelude.False};
   VMap l ->
    case v of {
     VNil -> Prelude.True;
     VCons _ _ -> Prelude.True;
     VMap l' ->
      (Prelude.||)
        (ltb ((Data.List.genericLength) l) ((Data.List.genericLength) l'))
        ((Prelude.&&)
          ((Prelude.==) ((Data.List.genericLength) l)
            ((Data.List.genericLength) l'))
          ((Prelude.||)
            (let {
              list_less0 l0 l'0 =
                case l0 of {
                 ([]) ->
                  case l'0 of {
                   ([]) -> Prelude.False;
                   (:) _ _ -> Prelude.True};
                 (:) p xs ->
                  case p of {
                   (,) x _ ->
                    case l'0 of {
                     ([]) -> Prelude.False;
                     (:) p0 ys ->
                      case p0 of {
                       (,) x' _ ->
                        case val_eqb x x' of {
                         Prelude.True -> list_less0 xs ys;
                         Prelude.False -> val_ltb x x'}}}}}}
             in list_less0 l l')
            ((Prelude.&&)
              (list_equal val_eqb ((Prelude.map) Prelude.fst l)
                ((Prelude.map) Prelude.fst l'))
              (let {
                list_less0 l0 l'0 =
                  case l0 of {
                   ([]) ->
                    case l'0 of {
                     ([]) -> Prelude.False;
                     (:) _ _ -> Prelude.True};
                   (:) p xs ->
                    case p of {
                     (,) _ y ->
                      case l'0 of {
                       ([]) -> Prelude.False;
                       (:) p0 ys ->
                        case p0 of {
                         (,) _ y' ->
                          case val_eqb y y' of {
                           Prelude.True -> list_less0 xs ys;
                           Prelude.False -> val_ltb y y'}}}}}}
               in list_less0 l l'))));
     VBitstring _ -> Prelude.True;
     _ -> Prelude.False};
   VClos _ id _ _ ->
    case v of {
     VLit _ -> Prelude.False;
     VVar _ -> Prelude.False;
     VFunId _ -> Prelude.False;
     VClos _ id' _ _ -> ltb id id';
     _ -> Prelude.True};
   VBitstring b1 ->
    case v of {
     VBitstring b2 ->
      (Prelude.<) (bv_unsigned (bvn_n b1) (bvn_val b1))
        (bv_unsigned (bvn_n b2) (bvn_val b2));
     _ -> Prelude.False};
   _ -> Prelude.False}

map_insert :: Val -> Val -> (([]) ((,) Val Val)) -> ([]) ((,) Val Val)
map_insert k v m =
  case m of {
   ([]) -> (:) ((,) k v) ([]);
   (:) p ms ->
    case p of {
     (,) k' v' ->
      case val_ltb k k' of {
       Prelude.True -> (:) ((,) k v) ((:) ((,) k' v') ms);
       Prelude.False ->
        case val_eqb k k' of {
         Prelude.True -> m;
         Prelude.False -> (:) ((,) k' v') (map_insert k v ms)}}}}

map_put :: Val -> Val -> (([]) ((,) Val Val)) -> ([]) ((,) Val Val)
map_put k v m =
  case m of {
   ([]) -> (:) ((,) k v) ([]);
   (:) p ms ->
    case p of {
     (,) k' v' ->
      case val_ltb k k' of {
       Prelude.True -> (:) ((,) k v) ((:) ((,) k' v') ms);
       Prelude.False ->
        case val_eqb k k' of {
         Prelude.True -> (:) ((,) k v) ms;
         Prelude.False -> (:) ((,) k' v') (map_put k v ms)}}}}

map_get :: Val -> (([]) ((,) Val Val)) -> Prelude.Maybe Val
map_get k m =
  case m of {
   ([]) -> Prelude.Nothing;
   (:) p ms ->
    case p of {
     (,) k' v' ->
      case val_ltb k' k of {
       Prelude.True -> map_get k ms;
       Prelude.False ->
        case val_eqb k k' of {
         Prelude.True -> Prelude.Just v';
         Prelude.False -> Prelude.Nothing}}}}

make_val_map :: (([]) ((,) Val Val)) -> ([]) ((,) Val Val)
make_val_map l =
  case l of {
   ([]) -> ([]);
   (:) p vs -> case p of {
                (,) k v -> map_insert k v (make_val_map vs)}}

flatten_list :: (([]) ((,) a1 a1)) -> ([]) a1
flatten_list l =
  case l of {
   ([]) -> ([]);
   (:) p xs -> case p of {
                (,) x y -> (:) x ((:) y (flatten_list xs))}}

deflatten_list :: (([]) a1) -> ([]) ((,) a1 a1)
deflatten_list l =
  case l of {
   ([]) -> ([]);
   (:) x l0 ->
    case l0 of {
     ([]) -> ([]);
     (:) y xs -> (:) ((,) x y) (deflatten_list xs)}}

bvn_split :: N -> Bvn -> (,) Bvn Bvn
bvn_split n b =
  let {
   front = bv_extract (bvn_n b)
             ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
               (bvn_n b) n)
             n (bvn_val b)}
  in
  let {
   rest = bv_extract (bvn_n b) N0
            ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
              (bvn_n b) n)
            (bvn_val b)}
  in
  (,) (Bv_to_bvn n front) (Bv_to_bvn
  ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
    (bvn_n b) n)
  rest)

little_bv_to_Z :: N -> Bv -> Prelude.Integer
little_bv_to_Z n bits =
  let {
   k = div
         (add n (Npos ((\x -> 2 Prelude.* x Prelude.+ 1)
           ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))
         (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
         ((\x -> 2 Prelude.* x) 1))))}
  in
  let {
   last_width = (\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                  n
                  (mul (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                    ((\x -> 2 Prelude.* x) 1))))
                    ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                      k (Npos 1)))}
  in
  let {v = bv_unsigned n bits} in
  let {
   last_digit = modulo0 v
                  (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
                    (of_N last_width))}
  in
  let {
   high_part = div0 v
                 (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
                   (of_N last_width))}
  in
  let {
   high_bytes = reverse
                  (z_to_little_endian
                    (of_N
                      ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                        k (Npos 1)))
                    ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                    ((\x -> 2 Prelude.* x) 1)))) high_part)}
  in
  little_endian_to_Z ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1))))
    ((Prelude.++) high_bytes ((:) last_digit ([])))

decode_int :: N -> BinSign -> BinEnd -> Bv -> Prelude.Integer
decode_int w sign0 endi bits =
  let {
   raw = case endi of {
          LittleEndian -> z_to_bv w (little_bv_to_Z w bits);
          _ -> bits}}
  in
  case sign0 of {
   Signed -> bv_signed w raw;
   Unsigned -> bv_unsigned w raw}

data Match a =
   Matches a
 | NotMatches
 | NotSupported

bind_match :: (Match a1) -> (a1 -> Match a2) -> Match a2
bind_match r f =
  case r of {
   Matches a -> f a;
   NotMatches -> NotMatches;
   NotSupported -> NotSupported}

match_and :: (a1 -> a2 -> a3) -> (Match a1) -> (Match a2) -> Match a3
match_and f r1 r2 =
  case r1 of {
   Matches a ->
    case r2 of {
     Matches b -> Matches (f a b);
     NotMatches -> NotMatches;
     NotSupported -> NotSupported};
   NotMatches -> case r2 of {
                  NotSupported -> NotSupported;
                  _ -> NotMatches};
   NotSupported -> NotSupported}

decode_bits :: Bvn -> BinType -> N -> BinSign -> BinEnd -> Match Val
decode_bits bits type1 unit1 sign0 endi =
  case type1 of {
   IntType -> Matches (VLit (Integer
    (decode_int (bvn_n bits) sign0 endi (bvn_val bits))));
   BinaryType ->
    case eqb (modulo (bvn_n bits) unit1) N0 of {
     Prelude.True -> Matches (VBitstring bits);
     Prelude.False -> NotMatches};
   BitstringType -> Matches (VBitstring bits);
   _ -> NotSupported}

match_pattern :: Pat -> Val -> Match (([]) Val)
match_pattern p e =
  case p of {
   PVar -> Matches ((:) e ([]));
   PLit l0 ->
    case e of {
     VLit l ->
      case (Prelude.==) l l0 of {
       Prelude.True -> Matches ([]);
       Prelude.False -> NotMatches};
     _ -> NotMatches};
   PCons p1 p2 ->
    case e of {
     VCons v1 v2 ->
      match_and (Prelude.++) (match_pattern p1 v1) (match_pattern p2 v2);
     _ -> NotMatches};
   PTuple pl ->
    case e of {
     VTuple vl ->
      let {
       match_and_bind_elements pl0 vl0 =
         case pl0 of {
          ([]) -> case vl0 of {
                   ([]) -> Matches ([]);
                   (:) _ _ -> NotMatches};
          (:) p0 ps ->
           case vl0 of {
            ([]) -> NotMatches;
            (:) v vs ->
             match_and (Prelude.++) (match_pattern p0 v)
               (match_and_bind_elements ps vs)}}}
      in match_and_bind_elements pl vl;
     _ -> NotMatches};
   PMap pl ->
    case e of {
     VMap vl ->
      let {
       match_and_bind_elements pl0 vl0 =
         case pl0 of {
          ([]) -> case vl0 of {
                   ([]) -> Matches ([]);
                   (:) _ _ -> NotMatches};
          (:) y ps ->
           case y of {
            (,) p1 p2 ->
             case vl0 of {
              ([]) -> NotMatches;
              (:) y0 vs ->
               case y0 of {
                (,) v1 v2 ->
                 match_and (Prelude.++)
                   (match_and (Prelude.++) (match_pattern p1 v1)
                     (match_pattern p2 v2))
                   (match_and_bind_elements ps vs)}}}}}
      in match_and_bind_elements pl vl;
     _ -> NotMatches};
   PNil -> case e of {
            VNil -> Matches ([]);
            _ -> NotMatches};
   PBin segs ->
    case e of {
     VBitstring bits ->
      let {
       match_segs l bits0 =
         case l of {
          ([]) ->
           case eqb (bvn_n bits0) N0 of {
            Prelude.True -> Matches ([]);
            Prelude.False -> NotMatches};
          (:) s segs0 ->
           case s of {
            Build_Segment val0 size0 unit1 type1 sign0 endi ->
             case size0 of {
              VLit size1 ->
               case (Prelude.&&) (null segs0)
                      ((Prelude.==) size1 (Atom "all")) of {
                Prelude.True ->
                 bind_match
                   (decode_bits bits0 type1 (of_nat unit1) sign0 endi)
                   (match_pattern val0);
                Prelude.False ->
                 case size1 of {
                  Atom _ -> NotMatches;
                  Integer size2 ->
                   let {total = mul (to_N size2) (of_nat unit1)} in
                   case (Prelude.||) ((Prelude.<) size2 0)
                          (ltb0 (bvn_n bits0) total) of {
                    Prelude.True -> NotMatches;
                    Prelude.False ->
                     case bvn_split total bits0 of {
                      (,) front rest ->
                       match_and (Prelude.++)
                         (bind_match
                           (decode_bits front type1 (of_nat unit1) sign0
                             endi)
                           (match_pattern val0))
                         (match_segs segs0 rest)}}}};
              _ -> NotMatches}}}}
      in match_segs segs bits;
     _ -> NotMatches}}

match_pattern_list :: (([]) Pat) -> ValSeq -> Match (([]) Val)
match_pattern_list pl vl =
  case pl of {
   ([]) -> case vl of {
            ([]) -> Matches ([]);
            (:) _ _ -> NotMatches};
   (:) p ps ->
    case vl of {
     ([]) -> NotMatches;
     (:) v vs ->
      case match_pattern p v of {
       Matches vs' ->
        case match_pattern_list ps vs of {
         Matches vs'' -> Matches ((Prelude.++) vs' vs'');
         x -> x};
       x -> x}}}

data SideEffectId =
   Input
 | Output
 | AtomCreation

type SideEffect = (,) SideEffectId (([]) Val)

string_of_uint :: Uint -> Prelude.String
string_of_uint d =
  case d of {
   Nil -> "";
   D0 d0 -> (:) '0' (string_of_uint d0);
   D1 d0 -> (:) '1' (string_of_uint d0);
   D2 d0 -> (:) '2' (string_of_uint d0);
   D3 d0 -> (:) '3' (string_of_uint d0);
   D4 d0 -> (:) '4' (string_of_uint d0);
   D5 d0 -> (:) '5' (string_of_uint d0);
   D6 d0 -> (:) '6' (string_of_uint d0);
   D7 d0 -> (:) '7' (string_of_uint d0);
   D8 d0 -> (:) '8' (string_of_uint d0);
   D9 d0 -> (:) '9' (string_of_uint d0)}

string_of_uint0 :: Uint -> Prelude.String
string_of_uint0 d =
  case d of {
   Nil -> "0";
   _ -> string_of_uint d}

string_of_int :: Signed_int -> Prelude.String
string_of_int d =
  case d of {
   Pos d0 -> string_of_uint0 d0;
   Neg d0 -> (:) '-' (string_of_uint0 d0)}

data PrimopCode =
   PMatchFail
 | PRaise
 | PNothing
 | PRecvNext
 | PPeekMsg
 | PRemoveMsg
 | PRecvWaitTimeout

data BIFCode =
   BPlus
 | BMinus
 | BMult
 | BDivide
 | BRem
 | BDiv
 | BSl
 | BSr
 | BAbs
 | BFwrite
 | BFread
 | BAnd
 | BOr
 | BNot
 | BEq
 | BTypeEq
 | BNeq
 | BTypeNeq
 | BApp
 | BMinusMinus
 | BSplit
 | BTupleToList
 | BListToTuple
 | BListToAtom
 | BIntegerToList
 | BLt
 | BLe
 | BGt
 | BGe
 | BLength
 | BTupleSize
 | BTl
 | BHd
 | BElement
 | BSetElement
 | BIsNumber
 | BIsInteger
 | BIsAtom
 | BIsBoolean
 | BIsBinary
 | BIsBitstring
 | BError
 | BExit
 | BThrow
 | BSend
 | BSpawn
 | BSpawnLink
 | BProcessFlag
 | BSelf
 | BLink
 | BUnLink
 | BNothing
 | BFunInfo
 | BGet
 | BPut
 | BByteSize
 | BBitSize
 | BBinaryToList
 | BBitstringToList

is_shallow_proper_list :: Val -> Prelude.Bool
is_shallow_proper_list v =
  case v of {
   VNil -> Prelude.True;
   VCons _ y -> is_shallow_proper_list y;
   _ -> Prelude.False}

eval_append :: Val -> Val -> Redex
eval_append v1 v2 =
  case v1 of {
   VNil -> RValSeq ((:) v2 ([]));
   VCons x y ->
    case eval_append y v2 of {
     RValSeq vs ->
      case vs of {
       ([]) -> RExc
        (badarg (VTuple ((:) (VLit (Atom "++")) ((:) v1 ((:) v2 ([]))))));
       (:) res l ->
        case l of {
         ([]) -> RValSeq ((:) (VCons x res) ([]));
         (:) _ _ -> RExc
          (badarg (VTuple ((:) (VLit (Atom "++")) ((:) v1 ((:) v2 ([]))))))}};
     _ -> RExc
      (badarg (VTuple ((:) (VLit (Atom "++")) ((:) v1 ((:) v2 ([]))))))};
   _ -> RExc
    (badarg (VTuple ((:) (VLit (Atom "++")) ((:) v1 ((:) v2 ([]))))))}

subtract_elem :: Val -> Val -> Val
subtract_elem v1 v2 =
  case v1 of {
   VNil -> VNil;
   VCons x y ->
    case val_eqb x v2 of {
     Prelude.True -> y;
     Prelude.False -> VCons x (subtract_elem y v2)};
   _ -> errorVal}

eval_subtract :: Val -> Val -> Redex
eval_subtract v1 v2 =
  case (Prelude.&&) (is_shallow_proper_list v1) (is_shallow_proper_list v2) of {
   Prelude.True ->
    case v2 of {
     VNil -> RValSeq ((:) v1 ([]));
     VCons hd tl -> eval_subtract (subtract_elem v1 hd) tl;
     _ -> RExc
      (badarg (VTuple ((:) (VLit (Atom "--")) ((:) v1 ((:) v2 ([]))))))};
   Prelude.False -> RExc
    (badarg (VTuple ((:) (VLit (Atom "--")) ((:) v1 ((:) v2 ([]))))))}

split_cons :: Prelude.Integer -> Val -> Prelude.Maybe ((,) Val Val)
split_cons n v =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Just ((,) VNil v))
    (\n' ->
    case v of {
     VCons hd tl ->
      case split_cons n' tl of {
       Prelude.Just p ->
        case p of {
         (,) v1 v2 -> Prelude.Just ((,) (VCons hd v1) v2)};
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing})
    n

eval_split :: Val -> Val -> Redex
eval_split v1 v2 =
  case v1 of {
   VLit l ->
    case l of {
     Atom _ -> RExc
      (badarg (VTuple ((:) (VLit (Atom "split")) ((:) v1 ((:) v2 ([]))))));
     Integer i ->
      case (Prelude.<) i 0 of {
       Prelude.True -> RExc
        (badarg (VTuple ((:) (VLit (Atom "split")) ((:) v1 ((:) v2 ([]))))));
       Prelude.False ->
        case split_cons ((Prelude.id) i) v2 of {
         Prelude.Just p ->
          case p of {
           (,) v3 v4 -> RValSeq ((:) (VTuple ((:) v3 ((:) v4 ([])))) ([]))};
         Prelude.Nothing -> RExc
          (badarg (VTuple ((:) (VLit (Atom "split")) ((:) v1 ((:) v2
            ([]))))))}}};
   _ -> RExc
    (badarg (VTuple ((:) (VLit (Atom "split")) ((:) v1 ((:) v2 ([]))))))}

meta_to_cons :: (([]) Val) -> Val
meta_to_cons l =
  case l of {
   ([]) -> VNil;
   (:) x xs -> VCons x (meta_to_cons xs)}

transform_tuple :: Val -> Redex
transform_tuple v =
  case v of {
   VTuple l -> RValSeq ((:) (meta_to_cons l) ([]));
   _ -> RExc
    (badarg (VTuple ((:) (VLit (Atom "tuple_to_list")) ((:) v ([])))))}

mk_list :: Val -> Prelude.Maybe (([]) Val)
mk_list l =
  case l of {
   VNil -> Prelude.Just ([]);
   VCons v1 v2 ->
    case mk_list v2 of {
     Prelude.Just l0 -> Prelude.Just ((:) v1 l0);
     Prelude.Nothing -> Prelude.Nothing};
   _ -> Prelude.Nothing}

mk_ascii_list :: Val -> Prelude.Maybe (([]) Prelude.Char)
mk_ascii_list l =
  case l of {
   VNil -> Prelude.Just ([]);
   VCons hd v2 ->
    case hd of {
     VLit l0 ->
      case l0 of {
       Atom _ -> Prelude.Nothing;
       Integer v1 ->
        case mk_ascii_list v2 of {
         Prelude.Just s -> Prelude.Just ((:) (ascii_of_nat ((Prelude.id) v1))
          s);
         Prelude.Nothing -> Prelude.Nothing}};
     _ -> Prelude.Nothing};
   _ -> Prelude.Nothing}

string_to_vcons :: Prelude.String -> Val
string_to_vcons s =
  case s of {
   ([]) -> VNil;
   (:) x xs -> VCons (VLit (Integer ((Prelude.id) (nat_of_ascii x))))
    (string_to_vcons xs)}

len :: Val -> Prelude.Maybe Prelude.Integer
len l =
  case l of {
   VNil -> Prelude.Just 0;
   VCons _ v2 ->
    case len v2 of {
     Prelude.Just n2 -> Prelude.Just (Prelude.succ n2);
     Prelude.Nothing -> Prelude.Nothing};
   _ -> Prelude.Nothing}

eval_length :: (([]) Val) -> Redex
eval_length params =
  case params of {
   ([]) -> RExc (undef (VLit (Atom "length")));
   (:) v l ->
    case l of {
     ([]) ->
      case len v of {
       Prelude.Just n -> RValSeq ((:) (VLit (Integer ((Prelude.id) n))) ([]));
       Prelude.Nothing -> RExc
        (badarg (VTuple ((:) (VLit (Atom "length")) ((:) v ([])))))};
     (:) _ _ -> RExc (undef (VLit (Atom "length")))}}

eval_tuple_size :: (([]) Val) -> Redex
eval_tuple_size params =
  case params of {
   ([]) -> RExc (undef (VLit (Atom "tuple_size")));
   (:) v l0 ->
    case v of {
     VLit _ ->
      case l0 of {
       ([]) -> RExc
        (badarg (VTuple ((:) (VLit (Atom "tuple_size")) ((:) v ([])))));
       (:) _ _ -> RExc (undef (VLit (Atom "tuple_size")))};
     VTuple l ->
      case l0 of {
       ([]) -> RValSeq ((:) (VLit (Integer
        ((Prelude.id) ((Data.List.genericLength) l)))) ([]));
       (:) _ _ -> RExc (undef (VLit (Atom "tuple_size")))};
     VMap _ ->
      case l0 of {
       ([]) -> RExc
        (badarg (VTuple ((:) (VLit (Atom "tuple_size")) ((:) v ([])))));
       (:) _ _ -> RExc (undef (VLit (Atom "tuple_size")))};
     _ ->
      case l0 of {
       ([]) -> RExc
        (badarg (VTuple ((:) (VLit (Atom "tuple_size")) ((:) v ([])))));
       (:) _ _ -> RExc (undef (VLit (Atom "tuple_size")))}}}

z_to_bv_little :: N -> Prelude.Integer -> Bv
z_to_bv_little n z =
  let {
   k = div
         (add n (Npos ((\x -> 2 Prelude.* x Prelude.+ 1)
           ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))
         (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
         ((\x -> 2 Prelude.* x) 1))))}
  in
  let {
   last_width = (\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                  n
                  (mul (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                    ((\x -> 2 Prelude.* x) 1))))
                    ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                      k (Npos 1)))}
  in
  let {
   high_bytes = z_to_little_endian
                  (of_N
                    ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                      k (Npos 1)))
                  ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                  ((\x -> 2 Prelude.* x) 1)))) z}
  in
  let {
   high_part = little_endian_to_Z ((\x -> x) ((\x -> 2 Prelude.* x)
                 ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
                 (reverse high_bytes)}
  in
  let {
   last_digit = modulo0
                  (shiftr z
                    (of_N
                      (mul (Npos ((\x -> 2 Prelude.* x)
                        ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
                        ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                          k (Npos 1)))))
                  (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
                    (of_N last_width))}
  in
  z_to_bv n
    ((Prelude.+)
      ((Prelude.*) high_part
        (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) (of_N last_width)))
      last_digit)

segment_to_bitstring :: Val -> Val -> Prelude.Integer -> BinType -> BinEnd ->
                        Prelude.Maybe Redex
segment_to_bitstring v size0 unit1 type1 endian0 =
  case size0 of {
   VLit l ->
    case l of {
     Atom _ -> Prelude.Just (RExc
      (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple ((:) v ((:)
        size0 ([])))) ([]))))));
     Integer vsize ->
      case (Prelude.<) vsize 0 of {
       Prelude.True -> Prelude.Just (RExc
        (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple ((:) v
          ((:) size0 ([])))) ([]))))));
       Prelude.False ->
        let {fullsize = mul (abs_N vsize) (of_nat unit1)} in
        case type1 of {
         IntType ->
          case v of {
           VLit l0 ->
            case l0 of {
             Atom _ -> Prelude.Just (RExc
              (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple
                ((:) v ((:) size0 ([])))) ([]))))));
             Integer x ->
              case endian0 of {
               LittleEndian -> Prelude.Just (RValSeq ((:) (VBitstring
                (Bv_to_bvn fullsize (z_to_bv_little fullsize x))) ([])));
               _ -> Prelude.Just (RValSeq ((:) (VBitstring (Bv_to_bvn
                fullsize (z_to_bv fullsize x))) ([])))}};
           _ -> Prelude.Just (RExc
            (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple ((:)
              v ((:) size0 ([])))) ([]))))))};
         BinaryType ->
          case v of {
           VBitstring bits ->
            case (Prelude.&&)
                   (eqb
                     (modulo fullsize (Npos ((\x -> 2 Prelude.* x)
                       ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))
                     N0)
                   ((Prelude.<=) (to_nat fullsize) (to_nat (bvn_n bits))) of {
             Prelude.True -> Prelude.Just (RValSeq ((:) (VBitstring
              (Bv_to_bvn fullsize
              (bv_extract (bvn_n bits)
                ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                  (bvn_n bits) fullsize)
                fullsize (bvn_val bits))))
              ([])));
             Prelude.False -> Prelude.Just (RExc
              (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple
                ((:) v ((:) size0 ([])))) ([]))))))};
           _ -> Prelude.Just (RExc
            (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple ((:)
              v ((:) size0 ([])))) ([]))))))};
         BitstringType ->
          case (Prelude.==) unit1 (Prelude.succ 0) of {
           Prelude.True ->
            case v of {
             VBitstring bits ->
              case (Prelude.<=) (to_nat fullsize) (to_nat (bvn_n bits)) of {
               Prelude.True -> Prelude.Just (RValSeq ((:) (VBitstring
                (Bv_to_bvn fullsize
                (bv_extract (bvn_n bits)
                  ((\n m -> case n of { N0 -> N0; Npos a -> case m of { N0 -> n; Npos b -> if a Prelude.> b then Npos (a Prelude.- b) else N0 } })
                    (bvn_n bits) fullsize)
                  fullsize (bvn_val bits))))
                ([])));
               Prelude.False -> Prelude.Just (RExc
                (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple
                  ((:) v ((:) size0 ([])))) ([]))))))};
             _ -> Prelude.Just (RExc
              (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple
                ((:) v ((:) size0 ([])))) ([]))))))};
           Prelude.False -> Prelude.Just (RExc
            (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple ((:)
              v ((:) size0 ([])))) ([]))))))};
         _ -> Prelude.Nothing}}};
   _ -> Prelude.Just (RExc
    (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple ((:) v ((:)
      size0 ([])))) ([]))))))}

bvn_to_bytes :: Bvn -> (,) (([]) Prelude.Integer) Bvn
bvn_to_bytes b =
  let {n = bvn_n b} in
  let {
   r = modulo n (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
         ((\x -> 2 Prelude.* x) 1))))}
  in
  let {
   m = div n (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
         ((\x -> 2 Prelude.* x) 1))))}
  in
  (,)
  (reverse
    (z_to_little_endian (of_N m) ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))
      (shiftr (bvn_unsigned b) (of_N r))))
  (Bv_to_bvn r (bv_extract (bvn_n b) N0 r (bvn_val b)))

data FrameIdent =
   IValues
 | ITuple
 | IMap
 | IBin
 | ICall Val Val
 | IPrimOp Prelude.String
 | IApp Val

data Frame =
   FCons1 Exp
 | FCons2 Val
 | FParams FrameIdent (([]) Val) (([]) Exp)
 | FApp1 (([]) Exp)
 | FCallMod Exp (([]) Exp)
 | FCallFun Val (([]) Exp)
 | FCase1 (([]) ((,) ((,) (([]) Pat) Exp) Exp))
 | FCase2 (([]) Val) Exp (([]) ((,) ((,) (([]) Pat) Exp) Exp))
 | FLet Prelude.Integer Exp
 | FSeq Exp
 | FTry Prelude.Integer Exp Prelude.Integer Exp
 | FSeg1 Exp Prelude.Integer BinType BinSign BinEnd
 | FSeg2 Val Prelude.Integer BinType BinSign BinEnd

type FrameStack = ([]) Frame

construct_bitstring :: (([]) Val) -> Prelude.Maybe Bvn
construct_bitstring l =
  case l of {
   ([]) -> Prelude.Just (Bv_to_bvn N0 (z_to_bv N0 0));
   (:) v rest ->
    case v of {
     VBitstring bits ->
      case construct_bitstring rest of {
       Prelude.Just restbits -> Prelude.Just (Bv_to_bvn
        (add (bvn_n bits) (bvn_n restbits))
        (bv_concat (add (bvn_n bits) (bvn_n restbits)) (bvn_n bits)
          (bvn_n restbits) (bvn_val bits) (bvn_val restbits)));
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing}}

isPropagatable :: Frame -> Prelude.Bool
isPropagatable f =
  case f of {
   FTry _ _ _ _ -> Prelude.False;
   _ -> Prelude.True}

type Mapset' munit =
  munit
  -- singleton inductive, whose constructor was Mapset
  
type Gmap k a = Data.HashMap.Strict.HashMap k a
  -- singleton inductive, whose constructor was GMap
  
type Gset k = Data.HashSet.HashSet k

type Mailbox = (,) (([]) Val) (([]) Val)

emptyBox :: Mailbox
emptyBox =
  (,) ([]) ([])

type ProcessFlag = Prelude.Bool

type LiveProcess =
  (,) ((,) ((,) ((,) FrameStack Redex) Mailbox) (Gset PID)) ProcessFlag

type DeadProcess = Gmap PID Val

type Process = Prelude.Either LiveProcess DeadProcess

data Signal =
   SMessage Val
 | SExit Val Prelude.Bool
 | SLink
 | SUnlink

data Action =
   ASend PID PID Signal
 | AArrive PID PID Signal
 | ASelf PID
 | ASpawn PID Val Val Prelude.Bool
 | Coq__UU03c4_
 | Coq__UU03b5_

removeMessage :: Mailbox -> Prelude.Maybe Mailbox
removeMessage m =
  case m of {
   (,) m1 l ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) _ m2 -> Prelude.Just ((,) ([]) ((Prelude.++) m1 m2))}}

peekMessage :: Mailbox -> Prelude.Maybe Val
peekMessage m =
  case m of {
   (,) _ l ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) msg _ -> Prelude.Just msg}}

recvNext :: Mailbox -> Prelude.Maybe Mailbox
recvNext m =
  case m of {
   (,) m1 l ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) msg m2 -> Prelude.Just ((,) ((Prelude.++) m1 ((:) msg ([]))) m2)}}

mailboxPush :: Mailbox -> Val -> Mailbox
mailboxPush m msg =
  (,) (Prelude.fst m) ((Prelude.++) (Prelude.snd m) ((:) msg ([])))

lit_from_bool :: Prelude.Bool -> Val
lit_from_bool b =
  case b of {
   Prelude.True -> VLit (Atom "true");
   Prelude.False -> VLit (Atom "false")}

bool_from_lit :: Val -> Prelude.Maybe Prelude.Bool
bool_from_lit e =
  case e of {
   VLit l ->
    case l of {
     Atom x ->
      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             x "true" of {
       Prelude.True -> Prelude.Just Prelude.True;
       Prelude.False ->
        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               x "false" of {
         Prelude.True -> Prelude.Just Prelude.False;
         Prelude.False -> Prelude.Nothing}};
     Integer _ -> Prelude.Nothing};
   _ -> Prelude.Nothing}

type Ether = Gmap ((,) PID PID) (([]) Signal)

type ProcessPool = Gmap PID Process

type Node = (,) Ether ProcessPool

etherAdd_Interp :: PID -> PID -> Signal -> Ether -> Ether
etherAdd_Interp source dest m n =
  case Data.HashMap.Strict.lookup ((,) source dest) n of {
   Prelude.Just l ->
    Data.HashMap.Strict.insert ((,) source dest)
      ((Prelude.++) l ((:) m ([]))) n;
   Prelude.Nothing ->
    Data.HashMap.Strict.insert ((,) source dest) ((:) m ([])) n}

etherPop_Interp :: PID -> PID -> Ether -> Prelude.Maybe ((,) Signal Ether)
etherPop_Interp source dest n =
  case Data.HashMap.Strict.lookup ((,) source dest) n of {
   Prelude.Just l ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) x xs -> Prelude.Just ((,) x
      (Data.HashMap.Strict.insert ((,) source dest) xs n))};
   Prelude.Nothing -> Prelude.Nothing}

flat_union_Interp :: (a1 -> Gset PID) -> (([]) a1) -> Gset PID
flat_union_Interp f l =
  Prelude.foldr (\x acc -> Data.HashSet.union (f x) acc) Data.HashSet.empty l

usedPIDsExp_Interp :: Exp -> Gset PID
usedPIDsExp_Interp e =
  case e of {
   VVal e0 -> usedPIDsVal_Interp e0;
   EExp e0 -> usedPIDsNVal_Interp e0}

usedPIDsVal_Interp :: Val -> Gset PID
usedPIDsVal_Interp v =
  case v of {
   VPid p -> Data.HashSet.singleton p;
   VCons hd tl ->
    Data.HashSet.union (usedPIDsVal_Interp hd) (usedPIDsVal_Interp tl);
   VTuple l -> flat_union_Interp usedPIDsVal_Interp l;
   VMap l ->
    flat_union_Interp (\x ->
      Data.HashSet.union (usedPIDsVal_Interp (Prelude.fst x))
        (usedPIDsVal_Interp (Prelude.snd x)))
      l;
   VClos ext _ _ e ->
    Data.HashSet.union (usedPIDsExp_Interp e)
      (flat_union_Interp (\x -> usedPIDsExp_Interp (Prelude.snd x)) ext);
   _ -> Data.HashSet.empty}

usedPIDsNVal_Interp :: NonVal -> Gset PID
usedPIDsNVal_Interp n =
  case n of {
   EFun _ e -> usedPIDsExp_Interp e;
   EValues el -> flat_union_Interp usedPIDsExp_Interp el;
   ECons hd tl ->
    Data.HashSet.union (usedPIDsExp_Interp hd) (usedPIDsExp_Interp tl);
   ETuple l -> flat_union_Interp usedPIDsExp_Interp l;
   EMap l ->
    flat_union_Interp (\x ->
      Data.HashSet.union (usedPIDsExp_Interp (Prelude.fst x))
        (usedPIDsExp_Interp (Prelude.snd x)))
      l;
   ECall m f l ->
    Data.HashSet.union (usedPIDsExp_Interp m)
      (Data.HashSet.union (usedPIDsExp_Interp f)
        (flat_union_Interp usedPIDsExp_Interp l));
   EPrimOp _ l -> flat_union_Interp usedPIDsExp_Interp l;
   EApp exp l ->
    Data.HashSet.union (usedPIDsExp_Interp exp)
      (flat_union_Interp usedPIDsExp_Interp l);
   ECase e l ->
    Data.HashSet.union (usedPIDsExp_Interp e)
      (flat_union_Interp (\x ->
        Data.HashSet.union
          (Data.HashSet.union
            (flat_union_Interp usedPIDsPat_Interp
              (Prelude.fst (Prelude.fst x)))
            (usedPIDsExp_Interp (Prelude.snd (Prelude.fst x))))
          (usedPIDsExp_Interp (Prelude.snd x)))
        l);
   ELet _ e1 e2 ->
    Data.HashSet.union (usedPIDsExp_Interp e1) (usedPIDsExp_Interp e2);
   ESeq e1 e2 ->
    Data.HashSet.union (usedPIDsExp_Interp e1) (usedPIDsExp_Interp e2);
   ELetRec l e ->
    Data.HashSet.union (usedPIDsExp_Interp e)
      (flat_union_Interp (\x -> usedPIDsExp_Interp (Prelude.snd x)) l);
   ETry e1 _ e2 _ e3 ->
    Data.HashSet.union (usedPIDsExp_Interp e1)
      (Data.HashSet.union (usedPIDsExp_Interp e2) (usedPIDsExp_Interp e3));
   EBin l -> flat_union_Interp usedPIDsExp_Interp l;
   ESeg seg ->
    Data.HashSet.union (usedPIDsExp_Interp (val seg))
      (usedPIDsExp_Interp (size seg))}

usedPIDsPat_Interp :: Pat -> Gset PID
usedPIDsPat_Interp p =
  case p of {
   PCons hd tl ->
    Data.HashSet.union (usedPIDsPat_Interp hd) (usedPIDsPat_Interp tl);
   PTuple l -> flat_union_Interp usedPIDsPat_Interp l;
   PMap l ->
    flat_union_Interp (\x ->
      Data.HashSet.union (usedPIDsPat_Interp (Prelude.fst x))
        (usedPIDsPat_Interp (Prelude.snd x)))
      l;
   PBin segments ->
    flat_union_Interp (\x ->
      Data.HashSet.union (usedPIDsPat_Interp (val x))
        (usedPIDsVal_Interp (size x)))
      segments;
   _ -> Data.HashSet.empty}

usedPIDsRed_Interp :: Redex -> Gset PID
usedPIDsRed_Interp r =
  case r of {
   RExp e -> usedPIDsExp_Interp e;
   RValSeq vs -> flat_union_Interp usedPIDsVal_Interp vs;
   RExc e ->
    Data.HashSet.union (usedPIDsVal_Interp (Prelude.snd (Prelude.fst e)))
      (usedPIDsVal_Interp (Prelude.snd e));
   RBox -> Data.HashSet.empty}

usedPIDsFrameId_Interp :: FrameIdent -> Gset PID
usedPIDsFrameId_Interp i =
  case i of {
   ICall m f ->
    Data.HashSet.union (usedPIDsVal_Interp m) (usedPIDsVal_Interp f);
   IApp v -> usedPIDsVal_Interp v;
   _ -> Data.HashSet.empty}

usedPIDsFrame_Interp :: Frame -> Gset PID
usedPIDsFrame_Interp f =
  case f of {
   FCons1 hd -> usedPIDsExp_Interp hd;
   FCons2 tl -> usedPIDsVal_Interp tl;
   FParams ident vl el ->
    Data.HashSet.union (usedPIDsFrameId_Interp ident)
      (Data.HashSet.union (flat_union_Interp usedPIDsVal_Interp vl)
        (flat_union_Interp usedPIDsExp_Interp el));
   FApp1 l -> flat_union_Interp usedPIDsExp_Interp l;
   FCallMod f0 l ->
    Data.HashSet.union (usedPIDsExp_Interp f0)
      (flat_union_Interp usedPIDsExp_Interp l);
   FCallFun m l ->
    Data.HashSet.union (usedPIDsVal_Interp m)
      (flat_union_Interp usedPIDsExp_Interp l);
   FCase1 l ->
    flat_union_Interp (\x ->
      Data.HashSet.union
        (Data.HashSet.union
          (flat_union_Interp usedPIDsPat_Interp
            (Prelude.fst (Prelude.fst x)))
          (usedPIDsExp_Interp (Prelude.snd (Prelude.fst x))))
        (usedPIDsExp_Interp (Prelude.snd x)))
      l;
   FCase2 lv ex le ->
    Data.HashSet.union (usedPIDsExp_Interp ex)
      (Data.HashSet.union (flat_union_Interp usedPIDsVal_Interp lv)
        (flat_union_Interp (\x ->
          Data.HashSet.union
            (Data.HashSet.union
              (flat_union_Interp usedPIDsPat_Interp
                (Prelude.fst (Prelude.fst x)))
              (usedPIDsExp_Interp (Prelude.snd (Prelude.fst x))))
            (usedPIDsExp_Interp (Prelude.snd x)))
          le));
   FLet _ e -> usedPIDsExp_Interp e;
   FSeq e -> usedPIDsExp_Interp e;
   FTry _ e2 _ e3 ->
    Data.HashSet.union (usedPIDsExp_Interp e2) (usedPIDsExp_Interp e3);
   FSeg1 s _ _ _ _ -> usedPIDsExp_Interp s;
   FSeg2 v _ _ _ _ -> usedPIDsVal_Interp v}

usedPIDsStack_Interp :: FrameStack -> Gset PID
usedPIDsStack_Interp fs =
  flat_union_Interp usedPIDsFrame_Interp fs

usedPIDsProc_Interp :: Process -> Gset PID
usedPIDsProc_Interp p =
  case p of {
   Prelude.Left l ->
    case l of {
     (,) p0 _ ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case p2 of {
           (,) fs r ->
            Data.HashSet.union (usedPIDsStack_Interp fs)
              (Data.HashSet.union (usedPIDsRed_Interp r)
                (Data.HashSet.union links
                  (Data.HashSet.union
                    (flat_union_Interp usedPIDsVal_Interp (Prelude.fst mb))
                    (flat_union_Interp usedPIDsVal_Interp (Prelude.snd mb)))))}}}};
   Prelude.Right links ->
    (\f m -> Data.HashSet.unions [f k v | (k, v) <- Data.HashMap.Strict.toList m])
      (\k x -> Data.HashSet.insert k (usedPIDsVal_Interp x)) links}

allPIDsPool_Interp :: ProcessPool -> Gset PID
allPIDsPool_Interp _UU03a0_ =
  flat_union_Interp (\pat ->
    case pat of {
     (,) _UU03b9_ proc0 ->
      Data.HashSet.insert _UU03b9_ (usedPIDsProc_Interp proc0)})
    (Data.HashMap.Strict.toList _UU03a0_)

usedPIDsSignal_Interp :: Signal -> Gset PID
usedPIDsSignal_Interp s =
  case s of {
   SMessage e -> usedPIDsVal_Interp e;
   SExit r _ -> usedPIDsVal_Interp r;
   _ -> Data.HashSet.empty}

allPIDsEther_Interp :: Ether -> Gset PID
allPIDsEther_Interp eth =
  flat_union_Interp (\pat ->
    case pat of {
     (,) y sigs ->
      case y of {
       (,) _UU03b9_s _UU03b9_d ->
        Data.HashSet.union
          (Data.HashSet.insert _UU03b9_s (Data.HashSet.singleton _UU03b9_d))
          (flat_union_Interp usedPIDsSignal_Interp sigs)}})
    (Data.HashMap.Strict.toList eth)

usedInPool_Interp :: PID -> ProcessPool -> Prelude.Bool
usedInPool_Interp pid prs =
  Data.HashSet.member pid (allPIDsPool_Interp prs)

usedInEther_Interp :: PID -> Ether -> Prelude.Bool
usedInEther_Interp pid eth =
  Data.HashSet.member pid (allPIDsEther_Interp eth)

convert_primop_to_code_Interp :: Prelude.String -> PrimopCode
convert_primop_to_code_Interp s =
  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) s
         "match_fail" of {
   Prelude.True -> PMatchFail;
   Prelude.False ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) s
           "raise" of {
     Prelude.True -> PRaise;
     Prelude.False ->
      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             s "recv_next" of {
       Prelude.True -> PRecvNext;
       Prelude.False ->
        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               s "recv_peek_message" of {
         Prelude.True -> PPeekMsg;
         Prelude.False ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 s "remove_message" of {
           Prelude.True -> PRemoveMsg;
           Prelude.False ->
            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   s "recv_wait_timeout" of {
             Prelude.True -> PRecvWaitTimeout;
             Prelude.False -> PNothing}}}}}}

eval_primop_error_Interp :: Prelude.String -> (([]) Val) -> Prelude.Maybe
                            Exception
eval_primop_error_Interp fname params =
  case convert_primop_to_code_Interp fname of {
   PMatchFail ->
    case params of {
     ([]) -> Prelude.Nothing;
     (:) val0 l ->
      case l of {
       ([]) -> Prelude.Just ((,) ((,) Error val0) VNil);
       (:) _ _ -> Prelude.Nothing}};
   PRaise ->
    case params of {
     ([]) -> Prelude.Nothing;
     (:) stacktrace l ->
      case l of {
       ([]) -> Prelude.Nothing;
       (:) reas l0 ->
        case l0 of {
         ([]) -> Prelude.Just ((,) ((,) Error reas) stacktrace);
         (:) _ _ -> Prelude.Nothing}}};
   _ -> Prelude.Just (undef (VLit (Atom fname)))}

primop_eval_Interp :: Prelude.String -> (([]) Val) -> Prelude.Maybe
                      ((,) Redex (Prelude.Maybe SideEffect))
primop_eval_Interp fname params =
  case convert_primop_to_code_Interp fname of {
   PMatchFail ->
    case eval_primop_error_Interp fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   PRaise ->
    case eval_primop_error_Interp fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   PNothing -> Prelude.Just ((,) (RExc (undef (VLit (Atom fname))))
    Prelude.Nothing);
   _ -> Prelude.Nothing}

convert_string_to_code_Interp :: ((,) Prelude.String Prelude.String) ->
                                 BIFCode
convert_string_to_code_Interp pat =
  case pat of {
   (,) sf sn ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           sf "erlang" of {
     Prelude.True ->
      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             sn "+" of {
       Prelude.True -> BPlus;
       Prelude.False ->
        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               sn "-" of {
         Prelude.True -> BMinus;
         Prelude.False ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 sn "*" of {
           Prelude.True -> BMult;
           Prelude.False ->
            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   sn "/" of {
             Prelude.True -> BDivide;
             Prelude.False ->
              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                     sn "bsl" of {
               Prelude.True -> BSl;
               Prelude.False ->
                case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                       sn "bsr" of {
                 Prelude.True -> BSr;
                 Prelude.False ->
                  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                         sn "rem" of {
                   Prelude.True -> BRem;
                   Prelude.False ->
                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           sn "div" of {
                     Prelude.True -> BDiv;
                     Prelude.False ->
                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             sn "abs" of {
                       Prelude.True -> BAbs;
                       Prelude.False ->
                        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                               sn "and" of {
                         Prelude.True -> BAnd;
                         Prelude.False ->
                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                 sn "or" of {
                           Prelude.True -> BOr;
                           Prelude.False ->
                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                   sn "not" of {
                             Prelude.True -> BNot;
                             Prelude.False ->
                              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                     sn "==" of {
                               Prelude.True -> BEq;
                               Prelude.False ->
                                case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                       sn "=:=" of {
                                 Prelude.True -> BTypeEq;
                                 Prelude.False ->
                                  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                         sn "/=" of {
                                   Prelude.True -> BNeq;
                                   Prelude.False ->
                                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                           sn "=/=" of {
                                     Prelude.True -> BTypeNeq;
                                     Prelude.False ->
                                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                             sn "++" of {
                                       Prelude.True -> BApp;
                                       Prelude.False ->
                                        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               sn "--" of {
                                         Prelude.True -> BMinusMinus;
                                         Prelude.False ->
                                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 sn "tuple_to_list" of {
                                           Prelude.True -> BTupleToList;
                                           Prelude.False ->
                                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                   sn "list_to_tuple" of {
                                             Prelude.True -> BListToTuple;
                                             Prelude.False ->
                                              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                     sn "list_to_atom" of {
                                               Prelude.True -> BListToAtom;
                                               Prelude.False ->
                                                case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                       sn "integer_to_list" of {
                                                 Prelude.True ->
                                                  BIntegerToList;
                                                 Prelude.False ->
                                                  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                         sn "<" of {
                                                   Prelude.True -> BLt;
                                                   Prelude.False ->
                                                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                           sn ">" of {
                                                     Prelude.True -> BGt;
                                                     Prelude.False ->
                                                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                             sn "=<" of {
                                                       Prelude.True -> BLe;
                                                       Prelude.False ->
                                                        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                               sn ">=" of {
                                                         Prelude.True -> BGe;
                                                         Prelude.False ->
                                                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                 sn "length" of {
                                                           Prelude.True ->
                                                            BLength;
                                                           Prelude.False ->
                                                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                   sn
                                                                   "tuple_size" of {
                                                             Prelude.True ->
                                                              BTupleSize;
                                                             Prelude.False ->
                                                              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn "hd" of {
                                                               Prelude.True ->
                                                                BHd;
                                                               Prelude.False ->
                                                                case 
                                                                ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                  sn "tl" of {
                                                                 Prelude.True ->
                                                                  BTl;
                                                                 Prelude.False ->
                                                                  case 
                                                                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "element" of {
                                                                   Prelude.True ->
                                                                    BElement;
                                                                   Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "setelement" of {
                                                                     Prelude.True ->
                                                                    BSetElement;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "is_number" of {
                                                                     Prelude.True ->
                                                                    BIsNumber;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "is_integer" of {
                                                                     Prelude.True ->
                                                                    BIsInteger;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "is_atom" of {
                                                                     Prelude.True ->
                                                                    BIsAtom;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "is_boolean" of {
                                                                     Prelude.True ->
                                                                    BIsBoolean;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "fun_info" of {
                                                                     Prelude.True ->
                                                                    BFunInfo;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "error" of {
                                                                     Prelude.True ->
                                                                    BError;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn "exit" of {
                                                                     Prelude.True ->
                                                                    BExit;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "throw" of {
                                                                     Prelude.True ->
                                                                    BThrow;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn "!" of {
                                                                     Prelude.True ->
                                                                    BSend;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "spawn" of {
                                                                     Prelude.True ->
                                                                    BSpawn;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "spawn_link" of {
                                                                     Prelude.True ->
                                                                    BSpawnLink;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "process_flag" of {
                                                                     Prelude.True ->
                                                                    BProcessFlag;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn "self" of {
                                                                     Prelude.True ->
                                                                    BSelf;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn "link" of {
                                                                     Prelude.True ->
                                                                    BLink;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "unlink" of {
                                                                     Prelude.True ->
                                                                    BUnLink;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "is_bitstring" of {
                                                                     Prelude.True ->
                                                                    BIsBitstring;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "is_binary" of {
                                                                     Prelude.True ->
                                                                    BIsBinary;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "byte_size" of {
                                                                     Prelude.True ->
                                                                    BByteSize;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "bit_size" of {
                                                                     Prelude.True ->
                                                                    BBitSize;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "binary_to_list" of {
                                                                     Prelude.True ->
                                                                    BBinaryToList;
                                                                     Prelude.False ->
                                                                    case 
                                                                    ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                                    sn
                                                                    "bitstring_to_list" of {
                                                                     Prelude.True ->
                                                                    BBitstringToList;
                                                                     Prelude.False ->
                                                                    BNothing}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}};
     Prelude.False ->
      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
             sf "io" of {
       Prelude.True ->
        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               sn "fwrite" of {
         Prelude.True -> BFwrite;
         Prelude.False ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 sn "fread" of {
           Prelude.True -> BFread;
           Prelude.False -> BNothing}};
       Prelude.False ->
        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               sf "lists" of {
         Prelude.True ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 sn "split" of {
           Prelude.True -> BSplit;
           Prelude.False -> BNothing};
         Prelude.False ->
          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 sf "maps" of {
           Prelude.True ->
            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   sn "get" of {
             Prelude.True -> BGet;
             Prelude.False ->
              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                     sn "put" of {
               Prelude.True -> BPut;
               Prelude.False -> BNothing}};
           Prelude.False -> BNothing}}}}}

eval_arith_Interp :: Prelude.String -> Prelude.String -> (([]) Val) -> Redex
eval_arith_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BPlus ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Integer a0)) ([]));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                case l1 of {
                 ([]) -> RValSeq ((:) (VLit (Integer ((Prelude.+) a0 b0)))
                  ([]));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc
          (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BMinus ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Integer ((Prelude.-) 0 a0))) ([]));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                case l1 of {
                 ([]) -> RValSeq ((:) (VLit (Integer ((Prelude.-) a0 b0)))
                  ([]));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc
          (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BMult ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                case l1 of {
                 ([]) -> RValSeq ((:) (VLit (Integer ((Prelude.*) a0 b0)))
                  ([]));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BDivide ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
                  (\_ ->
                  case l1 of {
                   ([]) -> RExc
                    (badarith (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                      (Integer a0)) ((:) (VLit (Integer 0)) ([]))))));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  (\_ ->
                  case l1 of {
                   ([]) -> RValSeq ((:) (VLit (Integer (div0 a0 b0))) ([]));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  (\_ ->
                  case l1 of {
                   ([]) -> RValSeq ((:) (VLit (Integer (div0 a0 b0))) ([]));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  b0};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BRem ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
                  (\_ ->
                  case l1 of {
                   ([]) -> RExc
                    (badarith (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                      (Integer a0)) ((:) (VLit (Integer 0)) ([]))))));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  (\_ ->
                  case l1 of {
                   ([]) -> RValSeq ((:) (VLit (Integer (rem a0 b0))) ([]));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  (\_ ->
                  case l1 of {
                   ([]) -> RValSeq ((:) (VLit (Integer (rem a0 b0))) ([]));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  b0};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BDiv ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
                  (\_ ->
                  case l1 of {
                   ([]) -> RExc
                    (badarith (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                      (Integer a0)) ((:) (VLit (Integer 0)) ([]))))));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  (\_ ->
                  case l1 of {
                   ([]) -> RValSeq ((:) (VLit (Integer (quot a0 b0))) ([]));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  (\_ ->
                  case l1 of {
                   ([]) -> RValSeq ((:) (VLit (Integer (quot a0 b0))) ([]));
                   (:) _ _ -> RExc (undef (VLit (Atom fname)))})
                  b0};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BSl ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                case l1 of {
                 ([]) -> RValSeq ((:) (VLit (Integer (shiftl a0 b0))) ([]));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BSr ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case l1 of {
             ([]) -> RExc
              (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer a0 ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) b l1 ->
            case b of {
             VLit l2 ->
              case l2 of {
               Atom _ ->
                case l1 of {
                 ([]) -> RExc
                  (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))};
               Integer b0 ->
                case l1 of {
                 ([]) -> RValSeq ((:) (VLit (Integer (shiftr a0 b0))) ([]));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VTuple _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l1 of {
               ([]) -> RExc
                (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l1 ->
          case l1 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) b l0 ->
          case l0 of {
           ([]) -> RExc
            (badarith (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BAbs ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case a of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RExc
            (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))};
         Integer a0 ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Integer ((Prelude.abs) a0))) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_io_Interp :: Prelude.String -> Prelude.String -> (([]) Val) -> (,) 
                  Redex (Prelude.Maybe SideEffect)
eval_io_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BFwrite ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing)
      (\n ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> (,) (RValSeq ((:) (VLit (Atom "ok")) ([]))) (Prelude.Just ((,)
        Output params)))
        (\_ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing)
        n)
      ((Data.List.genericLength) params);
   BFread ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing)
      (\n ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing)
        (\n0 ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> (,) (RValSeq ((:) (VTuple ((:) (VLit (Atom "ok")) ((:)
          (nth (Prelude.succ 0) params errorVal) ([])))) ([]))) (Prelude.Just
          ((,) Input params)))
          (\_ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing)
          n0)
        n)
      ((Data.List.genericLength) params);
   _ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing}

eval_logical_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                       Redex
eval_logical_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BAnd ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) b l0 ->
        case l0 of {
         ([]) ->
          case (Prelude.==) a (VLit (Atom "true")) of {
           Prelude.True ->
            case (Prelude.==) b (VLit (Atom "true")) of {
             Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
             Prelude.False ->
              case (Prelude.==) b (VLit (Atom "false")) of {
               Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
               Prelude.False -> RExc
                (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))))}};
           Prelude.False ->
            case (Prelude.==) a (VLit (Atom "false")) of {
             Prelude.True ->
              case (Prelude.==) b (VLit (Atom "true")) of {
               Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
               Prelude.False ->
                case (Prelude.==) b (VLit (Atom "false")) of {
                 Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
                 Prelude.False -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))))}};
             Prelude.False -> RExc
              (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))))}};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BOr ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) b l0 ->
        case l0 of {
         ([]) ->
          case (Prelude.==) a (VLit (Atom "true")) of {
           Prelude.True ->
            case (Prelude.==) b (VLit (Atom "true")) of {
             Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
             Prelude.False ->
              case (Prelude.==) b (VLit (Atom "false")) of {
               Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
               Prelude.False -> RExc
                (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                  ([]))))))}};
           Prelude.False ->
            case (Prelude.==) a (VLit (Atom "false")) of {
             Prelude.True ->
              case (Prelude.==) b (VLit (Atom "true")) of {
               Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
               Prelude.False ->
                case (Prelude.==) b (VLit (Atom "false")) of {
                 Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
                 Prelude.False -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                    ([]))))))}};
             Prelude.False -> RExc
              (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ((:) b
                ([]))))))}};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BNot ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) a l ->
      case l of {
       ([]) ->
        case (Prelude.==) a (VLit (Atom "true")) of {
         Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
         Prelude.False ->
          case (Prelude.==) a (VLit (Atom "false")) of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RExc
            (badarg (VTuple ((:) (VLit (Atom fname)) ((:) a ([])))))}};
       (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_equality_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                        Redex
eval_equality_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BEq ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case val_eqb v1 v2 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BTypeEq ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case val_eqb v1 v2 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BNeq ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case val_eqb v1 v2 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "true")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BTypeNeq ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case val_eqb v1 v2 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "false")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "true")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_transform_list_Interp :: Prelude.String -> Prelude.String -> (([]) 
                              Val) -> Redex
eval_transform_list_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BApp ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) -> eval_append v1 v2;
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BMinusMinus ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) -> eval_subtract v1 v2;
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BSplit ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) -> eval_split v1 v2;
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_list_tuple_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                          Redex
eval_list_tuple_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BTupleToList ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case l of {
       ([]) -> transform_tuple v;
       (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
   BListToTuple ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case l of {
       ([]) ->
        case mk_list v of {
         Prelude.Just l0 -> RValSeq ((:) (VTuple l0) ([]));
         Prelude.Nothing -> RExc
          (badarg (VTuple ((:) (VLit (Atom "list_to_tuple")) ((:) v ([])))))};
       (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_convert_Interp :: Prelude.String -> Prelude.String -> (([]) Val) -> (,)
                       Redex (Prelude.Maybe SideEffect)
eval_convert_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BListToAtom ->
    case params of {
     ([]) -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing;
     (:) v l ->
      case l of {
       ([]) ->
        case mk_ascii_list v of {
         Prelude.Just sl -> (,) (RValSeq ((:) (VLit (Atom
          (string_of_list_ascii sl))) ([]))) (Prelude.Just ((,) AtomCreation
          ((:) (VLit (Atom (string_of_list_ascii sl))) ([]))));
         Prelude.Nothing -> (,) (RExc
          (badarg (VTuple ((:) (VLit (Atom "list_to_atom")) ((:) v ([]))))))
          Prelude.Nothing};
       (:) _ _ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing}};
   BIntegerToList ->
    case params of {
     ([]) -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing;
     (:) v l ->
      case l of {
       ([]) ->
        case v of {
         VLit l0 ->
          case l0 of {
           Atom _ -> (,) (RExc
            (badarg (VTuple ((:) (VLit (Atom "integer_to_list")) ((:) v
              ([]))))))
            Prelude.Nothing;
           Integer z -> (,) (RValSeq ((:)
            (string_to_vcons (string_of_int (to_int z))) ([])))
            Prelude.Nothing};
         _ -> (,) (RExc
          (badarg (VTuple ((:) (VLit (Atom "integer_to_list")) ((:) v
            ([]))))))
          Prelude.Nothing};
       (:) _ _ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing}};
   _ -> (,) (RExc (undef (VLit (Atom fname)))) Prelude.Nothing}

eval_cmp_Interp :: Prelude.String -> Prelude.String -> (([]) Val) -> Redex
eval_cmp_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BLt ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case val_ltb v1 v2 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BLe ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case (Prelude.||) (val_ltb v1 v2) (val_eqb v1 v2) of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BGt ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case val_ltb v2 v1 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BGe ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case (Prelude.||) (val_ltb v2 v1) (val_eqb v1 v2) of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_hd_tl_Interp :: Prelude.String -> Prelude.String -> (([]) Val) -> Redex
eval_hd_tl_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BTl ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VCons _ y ->
        case l of {
         ([]) -> RValSeq ((:) y ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BHd ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VCons x _ ->
        case l of {
         ([]) -> RValSeq ((:) x ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_elem_tuple_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                          Redex
eval_elem_tuple_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BElement ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l0 ->
      case v1 of {
       VLit l1 ->
        case l1 of {
         Atom _ ->
          case l0 of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v2 l ->
            case l of {
             ([]) -> RExc
              (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                ([]))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
         Integer i ->
          case l0 of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v2 l2 ->
            case v2 of {
             VLit _ ->
              case l2 of {
               ([]) -> RExc
                (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VTuple l ->
              case l2 of {
               ([]) ->
                (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
                  (\_ -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                    (Integer i)) ((:) (VTuple l) ([])))))))
                  (\p ->
                  case nth_error l (pred ((Prelude.id) p)) of {
                   Prelude.Just v -> RValSeq ((:) v ([]));
                   Prelude.Nothing -> RExc
                    (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                      (Integer i)) ((:) (VTuple l) ([]))))))})
                  (\_ -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                    (Integer i)) ((:) (VTuple l) ([])))))))
                  i;
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             VMap _ ->
              case l2 of {
               ([]) -> RExc
                (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))};
             _ ->
              case l2 of {
               ([]) -> RExc
                (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                  ([]))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
       VTuple _ ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) v2 l1 ->
          case l1 of {
           ([]) -> RExc
            (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VMap _ ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) v2 l1 ->
          case l1 of {
           ([]) -> RExc
            (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       _ ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) v2 l ->
          case l of {
           ([]) -> RExc
            (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
              ([]))))));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BSetElement ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v1 l0 ->
      case v1 of {
       VLit l1 ->
        case l1 of {
         Atom _ ->
          case l0 of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v2 l ->
            case l of {
             ([]) -> RExc (undef (VLit (Atom fname)));
             (:) v3 l2 ->
              case l2 of {
               ([]) -> RExc
                (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2 ((:)
                  v3 ([])))))));
               (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
         Integer i ->
          case l0 of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v2 l2 ->
            case v2 of {
             VLit _ ->
              case l2 of {
               ([]) -> RExc (undef (VLit (Atom fname)));
               (:) v3 l3 ->
                case l3 of {
                 ([]) -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                    ((:) v3 ([])))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VTuple l ->
              case l2 of {
               ([]) -> RExc (undef (VLit (Atom fname)));
               (:) v3 l3 ->
                case l3 of {
                 ([]) ->
                  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
                    (\_ -> RExc
                    (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                      (Integer i)) ((:) (VTuple l) ([])))))))
                    (\p ->
                    case replace_nth_error l (pred ((Prelude.id) p)) v3 of {
                     Prelude.Just l' -> RValSeq ((:) (VTuple l') ([]));
                     Prelude.Nothing -> RExc
                      (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                        (Integer i)) ((:) (VTuple l) ((:) v3 ([])))))))})
                    (\_ -> RExc
                    (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VLit
                      (Integer i)) ((:) (VTuple l) ([])))))))
                    i;
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             VMap _ ->
              case l2 of {
               ([]) -> RExc (undef (VLit (Atom fname)));
               (:) v3 l3 ->
                case l3 of {
                 ([]) -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                    ((:) v3 ([])))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
             _ ->
              case l2 of {
               ([]) -> RExc (undef (VLit (Atom fname)));
               (:) v3 l ->
                case l of {
                 ([]) -> RExc
                  (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2
                    ((:) v3 ([])))))));
                 (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}}};
       VTuple _ ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) v2 l1 ->
          case l1 of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v3 l2 ->
            case l2 of {
             ([]) -> RExc
              (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2 ((:)
                v3 ([])))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
       VMap _ ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) v2 l1 ->
          case l1 of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v3 l2 ->
            case l2 of {
             ([]) -> RExc
              (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2 ((:)
                v3 ([])))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
       _ ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) v2 l ->
          case l of {
           ([]) -> RExc (undef (VLit (Atom fname)));
           (:) v3 l1 ->
            case l1 of {
             ([]) -> RExc
              (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v1 ((:) v2 ((:)
                v3 ([])))))));
             (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_check_Interp :: Prelude.String -> Prelude.String -> (([]) Val) -> Redex
eval_check_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BIsNumber ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))};
         Integer _ ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Atom "true")) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VTuple _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BIsInteger ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))};
         Integer _ ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Atom "true")) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VTuple _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BIsAtom ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit l0 ->
        case l0 of {
         Atom _ ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Atom "true")) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))};
         Integer _ ->
          case l of {
           ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
       VTuple _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BIsBoolean ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case l of {
       ([]) ->
        case (Prelude.||) ((Prelude.==) v (VLit (Atom "true")))
               ((Prelude.==) v (VLit (Atom "false"))) of {
         Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
         Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
       (:) _ _ -> RExc (undef (VLit (Atom fname)))}};
   BIsBinary ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VBitstring b ->
        case l of {
         ([]) ->
          case eqb
                 (modulo (bvn_n b) (Npos ((\x -> 2 Prelude.* x)
                   ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))
                 N0 of {
           Prelude.True -> RValSeq ((:) (VLit (Atom "true")) ([]));
           Prelude.False -> RValSeq ((:) (VLit (Atom "false")) ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BIsBitstring ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VBitstring _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "true")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Atom "false")) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_error_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                     Prelude.Maybe Exception
eval_error_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BError ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) reason l ->
      case l of {
       ([]) -> Prelude.Just ((,) ((,) Error reason) VNil);
       (:) args l0 ->
        case l0 of {
         ([]) -> Prelude.Just ((,) ((,) Error reason) args);
         (:) _ l1 ->
          case l1 of {
           ([]) -> Prelude.Just ((,) ((,) Error reason) args);
           (:) _ _ -> Prelude.Just (undef (VLit (Atom fname)))}}}};
   BExit ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) reason l ->
      case l of {
       ([]) -> Prelude.Just ((,) ((,) Exit reason) VNil);
       (:) _ l0 ->
        case l0 of {
         ([]) -> Prelude.Nothing;
         (:) _ _ -> Prelude.Just (undef (VLit (Atom fname)))}}};
   BThrow ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) reason l ->
      case l of {
       ([]) -> Prelude.Just ((,) ((,) Throw reason) VNil);
       (:) _ _ -> Prelude.Just (undef (VLit (Atom fname)))}};
   _ -> Prelude.Just (undef (VLit (Atom fname)))}

eval_funinfo_Interp :: (([]) Val) -> Redex
eval_funinfo_Interp params =
  case params of {
   ([]) -> RExc (undef (VLit (Atom "fun_info")));
   (:) v1 l ->
    case v1 of {
     VLit _ ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom "fun_info")));
       (:) v2 l1 ->
        case l1 of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom "fun_info")) ((:) v1 ((:) v2
            ([]))))));
         (:) _ _ -> RExc (undef (VLit (Atom "fun_info")))}};
     VTuple _ ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom "fun_info")));
       (:) v2 l1 ->
        case l1 of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom "fun_info")) ((:) v1 ((:) v2
            ([]))))));
         (:) _ _ -> RExc (undef (VLit (Atom "fun_info")))}};
     VMap _ ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom "fun_info")));
       (:) v2 l1 ->
        case l1 of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom "fun_info")) ((:) v1 ((:) v2
            ([]))))));
         (:) _ _ -> RExc (undef (VLit (Atom "fun_info")))}};
     VClos ext id params0 e ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom "fun_info")));
       (:) v2 l0 ->
        case l0 of {
         ([]) ->
          case (Prelude.==) v2 (VLit (Atom "arity")) of {
           Prelude.True -> RValSeq ((:) (VLit (Integer
            ((Prelude.id) params0))) ([]));
           Prelude.False -> RExc
            (badarg (VTuple ((:) (VLit (Atom "fun_info")) ((:) (VClos ext id
              params0 e) ((:) v2 ([]))))))};
         (:) _ _ -> RExc (undef (VLit (Atom "fun_info")))}};
     _ ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom "fun_info")));
       (:) v2 l0 ->
        case l0 of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom "fun_info")) ((:) v1 ((:) v2
            ([]))))));
         (:) _ _ -> RExc (undef (VLit (Atom "fun_info")))}}}}

eval_concurrent_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                          Prelude.Maybe Exception
eval_concurrent_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BSend ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) _ l ->
      case l of {
       ([]) -> Prelude.Just (undef (VLit (Atom fname)));
       (:) _ _ -> Prelude.Nothing}};
   BSpawn ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) _ l ->
      case l of {
       ([]) -> Prelude.Just (undef (VLit (Atom fname)));
       (:) _ _ -> Prelude.Nothing}};
   BSpawnLink ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) _ l ->
      case l of {
       ([]) -> Prelude.Just (undef (VLit (Atom fname)));
       (:) _ _ -> Prelude.Nothing}};
   BProcessFlag ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) _ _ -> Prelude.Nothing};
   BSelf ->
    case params of {
     ([]) -> Prelude.Nothing;
     (:) _ _ -> Prelude.Just (undef (VLit (Atom fname)))};
   BLink ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) _ _ -> Prelude.Nothing};
   BUnLink ->
    case params of {
     ([]) -> Prelude.Just (undef (VLit (Atom fname)));
     (:) _ _ -> Prelude.Nothing};
   _ -> Prelude.Just (undef (VLit (Atom fname)))}

eval_map_bifs_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                        Redex
eval_map_bifs_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BGet ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) key l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) map l0 ->
        case l0 of {
         ([]) ->
          case map of {
           VMap contents ->
            case map_get key contents of {
             Prelude.Just v -> RValSeq ((:) v ([]));
             Prelude.Nothing -> RExc (badkey key)};
           _ -> RExc (badmap map)};
         (:) default0 l1 ->
          case l1 of {
           ([]) ->
            case map of {
             VMap contents ->
              case map_get key contents of {
               Prelude.Just v -> RValSeq ((:) v ([]));
               Prelude.Nothing -> RValSeq ((:) default0 ([]))};
             _ -> RExc (badmap map)};
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   BPut ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) key l ->
      case l of {
       ([]) -> RExc (undef (VLit (Atom fname)));
       (:) value l0 ->
        case l0 of {
         ([]) -> RExc (undef (VLit (Atom fname)));
         (:) map l1 ->
          case l1 of {
           ([]) ->
            case map of {
             VMap contents -> RValSeq ((:) (VMap
              (map_put key value contents)) ([]));
             _ -> RExc
              (badmap (VTuple ((:) (VLit (Atom "put")) ((:) key ((:) value
                ((:) map ([])))))))};
           (:) _ _ -> RExc (undef (VLit (Atom fname)))}}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_bin_to_list_Interp :: Prelude.String -> Prelude.String -> (([]) 
                           Val) -> Redex
eval_bin_to_list_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BBinaryToList ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VBitstring b ->
        case l of {
         ([]) ->
          case eqb
                 (modulo (bvn_n b) (Npos ((\x -> 2 Prelude.* x)
                   ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))
                 N0 of {
           Prelude.True ->
            case bvn_to_bytes b of {
             (,) bytes _ -> RValSeq ((:)
              (meta_to_cons
                ((Prelude.map) (compose (\x -> VLit x) (\x -> Integer x))
                  bytes))
              ([]))};
           Prelude.False -> RExc
            (badarg (VTuple ((:) (VLit (Atom fname)) ((:) (VBitstring b)
              ([])))))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BBitstringToList ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VBitstring b ->
        case l of {
         ([]) ->
          case bvn_to_bytes b of {
           (,) bytes rems -> RValSeq ((:)
            (meta_to_cons
              ((Prelude.++)
                ((Prelude.map) (compose (\x -> VLit x) (\x -> Integer x))
                  bytes)
                (case eqb
                        (modulo (bvn_n b) (Npos ((\x -> 2 Prelude.* x)
                          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                          1)))))
                        N0 of {
                  Prelude.True -> ([]);
                  Prelude.False -> (:) (VBitstring rems) ([])})))
            ([]))};
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_bin_size_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
                        Redex
eval_bin_size_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BByteSize ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VBitstring b ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Integer
          (of_N
            (add
              (div (bvn_n b) (Npos ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))
              (case eqb
                      (modulo (bvn_n b) (Npos ((\x -> 2 Prelude.* x)
                        ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))
                      N0 of {
                Prelude.True -> N0;
                Prelude.False -> Npos 1})))))
          ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   BBitSize ->
    case params of {
     ([]) -> RExc (undef (VLit (Atom fname)));
     (:) v l ->
      case v of {
       VLit _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VTuple _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VMap _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       VBitstring b ->
        case l of {
         ([]) -> RValSeq ((:) (VLit (Integer (of_N (bvn_n b)))) ([]));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))};
       _ ->
        case l of {
         ([]) -> RExc
          (badarg (VTuple ((:) (VLit (Atom fname)) ((:) v ([])))));
         (:) _ _ -> RExc (undef (VLit (Atom fname)))}}};
   _ -> RExc (undef (VLit (Atom fname)))}

eval_Interp :: Prelude.String -> Prelude.String -> (([]) Val) ->
               Prelude.Maybe ((,) Redex (Prelude.Maybe SideEffect))
eval_Interp mname fname params =
  case convert_string_to_code_Interp ((,) mname fname) of {
   BFwrite -> Prelude.Just (eval_io_Interp mname fname params);
   BFread -> Prelude.Just (eval_io_Interp mname fname params);
   BAnd -> Prelude.Just ((,) (eval_logical_Interp mname fname params)
    Prelude.Nothing);
   BOr -> Prelude.Just ((,) (eval_logical_Interp mname fname params)
    Prelude.Nothing);
   BNot -> Prelude.Just ((,) (eval_logical_Interp mname fname params)
    Prelude.Nothing);
   BEq -> Prelude.Just ((,) (eval_equality_Interp mname fname params)
    Prelude.Nothing);
   BTypeEq -> Prelude.Just ((,) (eval_equality_Interp mname fname params)
    Prelude.Nothing);
   BNeq -> Prelude.Just ((,) (eval_equality_Interp mname fname params)
    Prelude.Nothing);
   BTypeNeq -> Prelude.Just ((,) (eval_equality_Interp mname fname params)
    Prelude.Nothing);
   BApp -> Prelude.Just ((,) (eval_transform_list_Interp mname fname params)
    Prelude.Nothing);
   BMinusMinus -> Prelude.Just ((,)
    (eval_transform_list_Interp mname fname params) Prelude.Nothing);
   BSplit -> Prelude.Just ((,)
    (eval_transform_list_Interp mname fname params) Prelude.Nothing);
   BTupleToList -> Prelude.Just ((,)
    (eval_list_tuple_Interp mname fname params) Prelude.Nothing);
   BListToTuple -> Prelude.Just ((,)
    (eval_list_tuple_Interp mname fname params) Prelude.Nothing);
   BListToAtom -> Prelude.Just (eval_convert_Interp mname fname params);
   BIntegerToList -> Prelude.Just (eval_convert_Interp mname fname params);
   BLt -> Prelude.Just ((,) (eval_cmp_Interp mname fname params)
    Prelude.Nothing);
   BLe -> Prelude.Just ((,) (eval_cmp_Interp mname fname params)
    Prelude.Nothing);
   BGt -> Prelude.Just ((,) (eval_cmp_Interp mname fname params)
    Prelude.Nothing);
   BGe -> Prelude.Just ((,) (eval_cmp_Interp mname fname params)
    Prelude.Nothing);
   BLength -> Prelude.Just ((,) (eval_length params) Prelude.Nothing);
   BTupleSize -> Prelude.Just ((,) (eval_tuple_size params) Prelude.Nothing);
   BTl -> Prelude.Just ((,) (eval_hd_tl_Interp mname fname params)
    Prelude.Nothing);
   BHd -> Prelude.Just ((,) (eval_hd_tl_Interp mname fname params)
    Prelude.Nothing);
   BElement -> Prelude.Just ((,) (eval_elem_tuple_Interp mname fname params)
    Prelude.Nothing);
   BSetElement -> Prelude.Just ((,)
    (eval_elem_tuple_Interp mname fname params) Prelude.Nothing);
   BIsNumber -> Prelude.Just ((,) (eval_check_Interp mname fname params)
    Prelude.Nothing);
   BIsInteger -> Prelude.Just ((,) (eval_check_Interp mname fname params)
    Prelude.Nothing);
   BIsAtom -> Prelude.Just ((,) (eval_check_Interp mname fname params)
    Prelude.Nothing);
   BIsBoolean -> Prelude.Just ((,) (eval_check_Interp mname fname params)
    Prelude.Nothing);
   BIsBinary -> Prelude.Just ((,) (eval_check_Interp mname fname params)
    Prelude.Nothing);
   BIsBitstring -> Prelude.Just ((,) (eval_check_Interp mname fname params)
    Prelude.Nothing);
   BError ->
    case eval_error_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BExit ->
    case eval_error_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BThrow ->
    case eval_error_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BSend ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BSpawn ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BSpawnLink ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BProcessFlag ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BSelf ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BLink ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BUnLink ->
    case eval_concurrent_Interp mname fname params of {
     Prelude.Just exc -> Prelude.Just ((,) (RExc exc) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Nothing};
   BNothing -> Prelude.Just ((,) (RExc (undef (VLit (Atom fname))))
    Prelude.Nothing);
   BFunInfo -> Prelude.Just ((,) (eval_funinfo_Interp params)
    Prelude.Nothing);
   BGet -> Prelude.Just ((,) (eval_map_bifs_Interp mname fname params)
    Prelude.Nothing);
   BPut -> Prelude.Just ((,) (eval_map_bifs_Interp mname fname params)
    Prelude.Nothing);
   BByteSize -> Prelude.Just ((,) (eval_bin_size_Interp mname fname params)
    Prelude.Nothing);
   BBitSize -> Prelude.Just ((,) (eval_bin_size_Interp mname fname params)
    Prelude.Nothing);
   BBinaryToList -> Prelude.Just ((,)
    (eval_bin_to_list_Interp mname fname params) Prelude.Nothing);
   BBitstringToList -> Prelude.Just ((,)
    (eval_bin_to_list_Interp mname fname params) Prelude.Nothing);
   _ -> Prelude.Just ((,) (eval_arith_Interp mname fname params)
    Prelude.Nothing)}

create_result_Interp :: FrameIdent -> (([]) Val) -> Prelude.Maybe
                        ((,) Redex (Prelude.Maybe SideEffect))
create_result_Interp ident vl =
  case ident of {
   IValues -> Prelude.Just ((,) (RValSeq vl) Prelude.Nothing);
   ITuple -> Prelude.Just ((,) (RValSeq ((:) (VTuple vl) ([])))
    Prelude.Nothing);
   IMap -> Prelude.Just ((,) (RValSeq ((:) (VMap
    (make_val_map (deflatten_list vl))) ([]))) Prelude.Nothing);
   IBin ->
    case construct_bitstring vl of {
     Prelude.Just val0 -> Prelude.Just ((,) (RValSeq ((:) (VBitstring val0)
      ([]))) Prelude.Nothing);
     Prelude.Nothing -> Prelude.Just ((,) (RExc
      (badarg (VTuple ((:) (VLit (Atom "eval_bits")) ((:) (VTuple vl)
        ([]))))))
      Prelude.Nothing)};
   ICall m f ->
    case m of {
     VLit l ->
      case l of {
       Atom module0 ->
        case f of {
         VLit l0 ->
          case l0 of {
           Atom func -> eval_Interp module0 func vl;
           Integer _ -> Prelude.Just ((,) (RExc
            (badfun (VTuple ((:) m ((:) f ([])))))) Prelude.Nothing)};
         _ -> Prelude.Just ((,) (RExc (badfun (VTuple ((:) m ((:) f ([]))))))
          Prelude.Nothing)};
       Integer _ -> Prelude.Just ((,) (RExc
        (badfun (VTuple ((:) m ((:) f ([])))))) Prelude.Nothing)};
     _ -> Prelude.Just ((,) (RExc (badfun (VTuple ((:) m ((:) f ([]))))))
      Prelude.Nothing)};
   IPrimOp f -> primop_eval_Interp f vl;
   IApp v ->
    case v of {
     VClos ext id vars e ->
      case (Prelude.==) vars ((Data.List.genericLength) vl) of {
       Prelude.True -> Prelude.Just ((,) (RExp
        (subst
          (list_subst ((Prelude.++) (convert_to_closlist ext) vl) idsubst) e))
        Prelude.Nothing);
       Prelude.False -> Prelude.Just ((,) (RExc
        (badarity (VClos ext id vars e))) Prelude.Nothing)};
     _ -> Prelude.Just ((,) (RExc (badfun v)) Prelude.Nothing)}}

sequentialStepFunc :: FrameStack -> Redex -> Prelude.Maybe
                      ((,) FrameStack Redex)
sequentialStepFunc fs r =
  case r of {
   RExp e0 ->
    case e0 of {
     VVal v -> Prelude.Just ((,) fs (RValSeq ((:) v ([]))));
     EExp e4 ->
      case e4 of {
       EFun vl e -> Prelude.Just ((,) fs (RValSeq ((:) (VClos ([]) 0 vl e)
        ([]))));
       EValues el -> Prelude.Just ((,) ((:) (FParams IValues ([]) el) fs)
        RBox);
       ECons hd tl -> Prelude.Just ((,) ((:) (FCons1 hd) fs) (RExp tl));
       ETuple el -> Prelude.Just ((,) ((:) (FParams ITuple ([]) el) fs) RBox);
       EMap l ->
        case l of {
         ([]) -> Prelude.Just ((,) fs (RValSeq ((:) (VMap ([])) ([]))));
         (:) p el ->
          case p of {
           (,) e1 e2 -> Prelude.Just ((,) ((:) (FParams IMap ([]) ((:) e2
            (flatten_list el))) fs) (RExp e1))}};
       ECall m f el -> Prelude.Just ((,) ((:) (FCallMod f el) fs) (RExp m));
       EPrimOp f el -> Prelude.Just ((,) ((:) (FParams (IPrimOp f) ([]) el)
        fs) RBox);
       EApp e l -> Prelude.Just ((,) ((:) (FApp1 l) fs) (RExp e));
       ECase e l -> Prelude.Just ((,) ((:) (FCase1 l) fs) (RExp e));
       ELet l e1 e2 -> Prelude.Just ((,) ((:) (FLet l e2) fs) (RExp e1));
       ESeq e1 e2 -> Prelude.Just ((,) ((:) (FSeq e2) fs) (RExp e1));
       ELetRec l e ->
        let {
         lc = convert_to_closlist
                ((Prelude.map) (\pat ->
                  case pat of {
                   (,) x y -> (,) ((,) 0 x) y}) l)}
        in
        Prelude.Just ((,) fs (RExp (subst (list_subst lc idsubst) e)));
       ETry e1 vl1 e2 vl2 e3 -> Prelude.Just ((,) ((:) (FTry vl1 e2 vl2 e3)
        fs) (RExp e1));
       EBin el -> Prelude.Just ((,) ((:) (FParams IBin ([]) el) fs) RBox);
       ESeg seg -> Prelude.Just ((,) ((:) (FSeg1 (size seg) (unit0 seg)
        (type0 seg) (sign seg) (endian seg)) fs) (RExp (val seg)))}};
   RValSeq vs ->
    case fs of {
     ([]) -> Prelude.Nothing;
     (:) f0 xs ->
      case f0 of {
       FCons1 hd ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l ->
          case l of {
           ([]) -> Prelude.Just ((,) ((:) (FCons2 v) xs) (RExp hd));
           (:) _ _ -> Prelude.Nothing}};
       FCons2 tl ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l ->
          case l of {
           ([]) -> Prelude.Just ((,) xs (RValSeq ((:) (VCons v tl) ([]))));
           (:) _ _ -> Prelude.Nothing}};
       FParams ident vl el0 ->
        case el0 of {
         ([]) ->
          case vs of {
           ([]) -> Prelude.Nothing;
           (:) v l ->
            case l of {
             ([]) ->
              case create_result_Interp ident ((Prelude.++) vl ((:) v ([]))) of {
               Prelude.Just p ->
                case p of {
                 (,) res _ -> Prelude.Just ((,) xs res)};
               Prelude.Nothing -> Prelude.Nothing};
             (:) _ _ -> Prelude.Nothing}};
         (:) e el ->
          case vs of {
           ([]) -> Prelude.Nothing;
           (:) v l ->
            case l of {
             ([]) -> Prelude.Just ((,) ((:) (FParams ident
              ((Prelude.++) vl ((:) v ([]))) el) xs) (RExp e));
             (:) _ _ -> Prelude.Nothing}}};
       FApp1 el ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l ->
          case l of {
           ([]) -> Prelude.Just ((,) ((:) (FParams (IApp v) ([]) el) xs)
            RBox);
           (:) _ _ -> Prelude.Nothing}};
       FCallMod f el ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l ->
          case l of {
           ([]) -> Prelude.Just ((,) ((:) (FCallFun v el) xs) (RExp f));
           (:) _ _ -> Prelude.Nothing}};
       FCallFun m el ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l ->
          case l of {
           ([]) -> Prelude.Just ((,) ((:) (FParams (ICall m v) ([]) el) xs)
            RBox);
           (:) _ _ -> Prelude.Nothing}};
       FCase1 l0 ->
        case l0 of {
         ([]) -> Prelude.Just ((,) xs (RExc if_clause));
         (:) p l ->
          case p of {
           (,) p0 e2 ->
            case p0 of {
             (,) lp e1 ->
              case match_pattern_list lp vs of {
               Matches vs' -> Prelude.Just ((,) ((:) (FCase2 vs
                (subst (list_subst vs' idsubst) e2) l) xs) (RExp
                (subst (list_subst vs' idsubst) e1)));
               NotMatches -> Prelude.Just ((,) ((:) (FCase1 l) xs) (RValSeq
                vs));
               NotSupported -> Prelude.Nothing}}}};
       FCase2 vs' e' l ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l0 ->
          case v of {
           VLit l1 ->
            case l1 of {
             Atom str ->
              case l0 of {
               ([]) ->
                case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                       str "true" of {
                 Prelude.True -> Prelude.Just ((,) xs (RExp e'));
                 Prelude.False ->
                  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                         str "false" of {
                   Prelude.True -> Prelude.Just ((,) ((:) (FCase1 l) xs)
                    (RValSeq vs'));
                   Prelude.False -> Prelude.Nothing}};
               (:) _ _ -> Prelude.Nothing};
             Integer _ -> Prelude.Nothing};
           _ -> Prelude.Nothing}};
       FLet l e2 ->
        case (Prelude.==) ((Data.List.genericLength) vs) l of {
         Prelude.True -> Prelude.Just ((,) xs (RExp
          (subst (list_subst vs idsubst) e2)));
         Prelude.False -> Prelude.Nothing};
       FSeq e2 ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) _ l ->
          case l of {
           ([]) -> Prelude.Just ((,) xs (RExp e2));
           (:) _ _ -> Prelude.Nothing}};
       FTry vl1 e2 _ _ ->
        case (Prelude.==) vl1 ((Data.List.genericLength) vs) of {
         Prelude.True -> Prelude.Just ((,) xs (RExp
          (subst (list_subst vs idsubst) e2)));
         Prelude.False -> Prelude.Nothing};
       FSeg1 size0 unit1 type1 sign0 endian0 ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) v l ->
          case l of {
           ([]) -> Prelude.Just ((,) ((:) (FSeg2 v unit1 type1 sign0 endian0)
            xs) (RExp size0));
           (:) _ _ -> Prelude.Nothing}};
       FSeg2 v unit1 type1 _ endian0 ->
        case vs of {
         ([]) -> Prelude.Nothing;
         (:) vsize l ->
          case l of {
           ([]) ->
            case segment_to_bitstring v vsize unit1 type1 endian0 of {
             Prelude.Just r0 -> Prelude.Just ((,) xs r0);
             Prelude.Nothing -> Prelude.Nothing};
           (:) _ _ -> Prelude.Nothing}}}};
   RExc e ->
    case e of {
     (,) p details ->
      case p of {
       (,) class0 reason ->
        case fs of {
         ([]) -> Prelude.Nothing;
         (:) f xs ->
          case f of {
           FTry _ _ vl2 e3 ->
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              case isPropagatable f of {
               Prelude.True -> Prelude.Just ((,) xs (RExc ((,) ((,) class0
                reason) details)));
               Prelude.False -> Prelude.Nothing})
              (\n ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ ->
                case isPropagatable f of {
                 Prelude.True -> Prelude.Just ((,) xs (RExc ((,) ((,) class0
                  reason) details)));
                 Prelude.False -> Prelude.Nothing})
                (\n0 ->
                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                  (\_ ->
                  case isPropagatable f of {
                   Prelude.True -> Prelude.Just ((,) xs (RExc ((,) ((,)
                    class0 reason) details)));
                   Prelude.False -> Prelude.Nothing})
                  (\n1 ->
                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                    (\_ -> Prelude.Just ((,) xs (RExp
                    (subst
                      (list_subst ((:) (exclass_to_value class0) ((:) reason
                        ((:) details ([])))) idsubst)
                      e3))))
                    (\_ ->
                    case isPropagatable f of {
                     Prelude.True -> Prelude.Just ((,) xs (RExc ((,) ((,)
                      class0 reason) details)));
                     Prelude.False -> Prelude.Nothing})
                    n1)
                  n0)
                n)
              vl2;
           _ ->
            case isPropagatable f of {
             Prelude.True -> Prelude.Just ((,) xs (RExc ((,) ((,) class0
              reason) details)));
             Prelude.False -> Prelude.Nothing}}}}};
   RBox ->
    case fs of {
     ([]) -> Prelude.Nothing;
     (:) f xs ->
      case f of {
       FParams ident vl el0 ->
        case el0 of {
         ([]) ->
          case ident of {
           IMap -> Prelude.Nothing;
           _ ->
            case create_result_Interp ident vl of {
             Prelude.Just p ->
              case p of {
               (,) res _ -> Prelude.Just ((,) xs res)};
             Prelude.Nothing -> Prelude.Nothing}};
         (:) e el ->
          case ident of {
           IMap -> Prelude.Nothing;
           _ -> Prelude.Just ((,) ((:) (FParams ident vl el) xs) (RExp e))}};
       _ -> Prelude.Nothing}}}

plsASendSExit :: PID -> Val -> Prelude.Bool -> Process -> Prelude.Maybe
                 Process
plsASendSExit _UU03b9_ v is_dead p =
  case is_dead of {
   Prelude.True ->
    case p of {
     Prelude.Left _ -> Prelude.Nothing;
     Prelude.Right links ->
      case Data.HashMap.Strict.lookup _UU03b9_ links of {
       Prelude.Just reason ->
        case (Prelude.==) reason v of {
         Prelude.True -> Prelude.Just (Prelude.Right
          (Data.HashMap.Strict.delete _UU03b9_ links));
         Prelude.False -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing}};
   Prelude.False ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links ->
          case p1 of {
           (,) p2 mb ->
            case p2 of {
             (,) f r ->
              case f of {
               ([]) -> Prelude.Nothing;
               (:) f0 fs ->
                case f0 of {
                 FParams ident vl el ->
                  case ident of {
                   ICall m f1 ->
                    case m of {
                     VLit l0 ->
                      case l0 of {
                       Atom str_erlang ->
                        case f1 of {
                         VLit l1 ->
                          case l1 of {
                           Atom str_exit ->
                            case vl of {
                             ([]) -> Prelude.Nothing;
                             (:) v0 l2 ->
                              case v0 of {
                               VPid _UU03b9_' ->
                                case l2 of {
                                 ([]) ->
                                  case el of {
                                   ([]) ->
                                    case r of {
                                     RValSeq vs ->
                                      case vs of {
                                       ([]) -> Prelude.Nothing;
                                       (:) v' l3 ->
                                        case l3 of {
                                         ([]) ->
                                          case (Prelude.&&)
                                                 ((Prelude.&&)
                                                   ((Prelude.&&)
                                                     (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                       str_erlang "erlang")
                                                     (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                       str_exit "exit"))
                                                   ((Prelude.==) v' v))
                                                 ((Prelude.==) _UU03b9_'
                                                   _UU03b9_) of {
                                           Prelude.True -> Prelude.Just
                                            (Prelude.Left ((,) ((,) ((,) ((,)
                                            fs (RValSeq ((:) (VLit (Atom
                                            "true")) ([])))) mb) links)
                                            flag));
                                           Prelude.False -> Prelude.Nothing};
                                         (:) _ _ -> Prelude.Nothing}};
                                     _ -> Prelude.Nothing};
                                   (:) _ _ -> Prelude.Nothing};
                                 (:) _ _ -> Prelude.Nothing};
                               _ -> Prelude.Nothing}};
                           Integer _ -> Prelude.Nothing};
                         _ -> Prelude.Nothing};
                       Integer _ -> Prelude.Nothing};
                     _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing}}}}}};
     Prelude.Right _ -> Prelude.Nothing}}

processLocalStepASend :: PID -> Signal -> Process -> Prelude.Maybe Process
processLocalStepASend _UU03b9_ msg p =
  case msg of {
   SMessage v ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links ->
          case p1 of {
           (,) p2 mb ->
            case p2 of {
             (,) f r ->
              case f of {
               ([]) -> Prelude.Nothing;
               (:) f0 fs ->
                case f0 of {
                 FParams ident vl el ->
                  case ident of {
                   ICall m f1 ->
                    case m of {
                     VLit l0 ->
                      case l0 of {
                       Atom str_erlang ->
                        case f1 of {
                         VLit l1 ->
                          case l1 of {
                           Atom str_send ->
                            case vl of {
                             ([]) -> Prelude.Nothing;
                             (:) v0 l2 ->
                              case v0 of {
                               VPid _UU03b9_' ->
                                case l2 of {
                                 ([]) ->
                                  case el of {
                                   ([]) ->
                                    case r of {
                                     RValSeq vs ->
                                      case vs of {
                                       ([]) -> Prelude.Nothing;
                                       (:) v' l3 ->
                                        case l3 of {
                                         ([]) ->
                                          case (Prelude.&&)
                                                 (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                   str_erlang "erlang")
                                                 (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                   str_send "!") of {
                                           Prelude.True ->
                                            case (Prelude.&&)
                                                   ((Prelude.==) v' v)
                                                   ((Prelude.==) _UU03b9_'
                                                     _UU03b9_) of {
                                             Prelude.True -> Prelude.Just
                                              (Prelude.Left ((,) ((,) ((,)
                                              ((,) fs (RValSeq ((:) v ([]))))
                                              mb) links) flag));
                                             Prelude.False -> Prelude.Nothing};
                                           Prelude.False -> Prelude.Nothing};
                                         (:) _ _ -> Prelude.Nothing}};
                                     _ -> Prelude.Nothing};
                                   (:) _ _ -> Prelude.Nothing};
                                 (:) _ _ -> Prelude.Nothing};
                               _ -> Prelude.Nothing}};
                           Integer _ -> Prelude.Nothing};
                         _ -> Prelude.Nothing};
                       Integer _ -> Prelude.Nothing};
                     _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing}}}}}};
     Prelude.Right _ -> Prelude.Nothing};
   SExit v is_dead -> plsASendSExit _UU03b9_ v is_dead p;
   SLink ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links ->
          case p1 of {
           (,) p2 mb ->
            case p2 of {
             (,) f r ->
              case f of {
               ([]) -> Prelude.Nothing;
               (:) f0 fs ->
                case f0 of {
                 FParams ident vl el ->
                  case ident of {
                   ICall m f1 ->
                    case m of {
                     VLit l0 ->
                      case l0 of {
                       Atom str_erlang ->
                        case f1 of {
                         VLit l1 ->
                          case l1 of {
                           Atom str_link ->
                            case vl of {
                             ([]) ->
                              case el of {
                               ([]) ->
                                case r of {
                                 RValSeq vs ->
                                  case vs of {
                                   ([]) -> Prelude.Nothing;
                                   (:) v l2 ->
                                    case v of {
                                     VPid _UU03b9_' ->
                                      case l2 of {
                                       ([]) ->
                                        case (Prelude.&&)
                                               (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_erlang "erlang")
                                               (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_link "link") of {
                                         Prelude.True ->
                                          case (Prelude.==) _UU03b9_'
                                                 _UU03b9_ of {
                                           Prelude.True -> Prelude.Just
                                            (Prelude.Left ((,) ((,) ((,) ((,)
                                            fs (RValSeq ((:) (VLit (Atom
                                            "ok")) ([])))) mb)
                                            (Data.HashSet.insert _UU03b9_
                                              links))
                                            flag));
                                           Prelude.False -> Prelude.Nothing};
                                         Prelude.False -> Prelude.Nothing};
                                       (:) _ _ -> Prelude.Nothing};
                                     _ -> Prelude.Nothing}};
                                 _ -> Prelude.Nothing};
                               (:) _ _ -> Prelude.Nothing};
                             (:) _ _ -> Prelude.Nothing};
                           Integer _ -> Prelude.Nothing};
                         _ -> Prelude.Nothing};
                       Integer _ -> Prelude.Nothing};
                     _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing}}}}}};
     Prelude.Right _ -> Prelude.Nothing};
   SUnlink ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links ->
          case p1 of {
           (,) p2 mb ->
            case p2 of {
             (,) f r ->
              case f of {
               ([]) -> Prelude.Nothing;
               (:) f0 fs ->
                case f0 of {
                 FParams ident vl el ->
                  case ident of {
                   ICall m f1 ->
                    case m of {
                     VLit l0 ->
                      case l0 of {
                       Atom str_erlang ->
                        case f1 of {
                         VLit l1 ->
                          case l1 of {
                           Atom str_unlink ->
                            case vl of {
                             ([]) ->
                              case el of {
                               ([]) ->
                                case r of {
                                 RValSeq vs ->
                                  case vs of {
                                   ([]) -> Prelude.Nothing;
                                   (:) v l2 ->
                                    case v of {
                                     VPid _UU03b9_' ->
                                      case l2 of {
                                       ([]) ->
                                        case (Prelude.&&)
                                               (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_erlang "erlang")
                                               (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_unlink "unlink") of {
                                         Prelude.True ->
                                          case (Prelude.==) _UU03b9_'
                                                 _UU03b9_ of {
                                           Prelude.True -> Prelude.Just
                                            (Prelude.Left ((,) ((,) ((,) ((,)
                                            fs (RValSeq ((:) (VLit (Atom
                                            "ok")) ([])))) mb)
                                            (Data.HashSet.delete _UU03b9_
                                              links))
                                            flag));
                                           Prelude.False -> Prelude.Nothing};
                                         Prelude.False -> Prelude.Nothing};
                                       (:) _ _ -> Prelude.Nothing};
                                     _ -> Prelude.Nothing}};
                                 _ -> Prelude.Nothing};
                               (:) _ _ -> Prelude.Nothing};
                             (:) _ _ -> Prelude.Nothing};
                           Integer _ -> Prelude.Nothing};
                         _ -> Prelude.Nothing};
                       Integer _ -> Prelude.Nothing};
                     _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing}}}}}};
     Prelude.Right _ -> Prelude.Nothing}}

plsAArriveSExit :: PID -> PID -> Val -> Prelude.Bool -> Process ->
                   Prelude.Maybe Process
plsAArriveSExit source dest reason b p =
  case p of {
   Prelude.Left l ->
    case l of {
     (,) p0 flag ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case flag of {
           Prelude.True ->
            case b of {
             Prelude.True ->
              case Data.HashSet.member source links of {
               Prelude.True -> Prelude.Just (Prelude.Left ((,) ((,) ((,) p2
                (mailboxPush mb (VTuple ((:) (VLit (Atom "EXIT")) ((:) (VPid
                  source) ((:) reason ([])))))))
                links) Prelude.True));
               Prelude.False ->
                case (Prelude.==) dest source of {
                 Prelude.True -> Prelude.Nothing;
                 Prelude.False -> Prelude.Just p}};
             Prelude.False ->
              case (Prelude.==) reason (VLit (Atom "kill")) of {
               Prelude.True -> Prelude.Just (Prelude.Right
                ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                  (VLit (Atom "killed")) links));
               Prelude.False -> Prelude.Just (Prelude.Left ((,) ((,) ((,) p2
                (mailboxPush mb (VTuple ((:) (VLit (Atom "EXIT")) ((:) (VPid
                  source) ((:) reason ([])))))))
                links) Prelude.True))}};
           Prelude.False ->
            case (Prelude.==) dest source of {
             Prelude.True ->
              case b of {
               Prelude.True ->
                case (Prelude.==) reason (VLit (Atom "normal")) of {
                 Prelude.True -> Prelude.Just (Prelude.Right
                  ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                    (VLit (Atom "normal")) links));
                 Prelude.False ->
                  case Data.HashSet.member source links of {
                   Prelude.True -> Prelude.Just (Prelude.Right
                    ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                      reason links));
                   Prelude.False -> Prelude.Nothing}};
               Prelude.False ->
                case (Prelude.==) reason (VLit (Atom "kill")) of {
                 Prelude.True -> Prelude.Just (Prelude.Right
                  ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                    (VLit (Atom "killed")) links));
                 Prelude.False -> Prelude.Just (Prelude.Right
                  ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                    reason links))}};
             Prelude.False ->
              case b of {
               Prelude.True ->
                case (Prelude.==) reason (VLit (Atom "normal")) of {
                 Prelude.True -> Prelude.Just p;
                 Prelude.False ->
                  case Data.HashSet.member source links of {
                   Prelude.True -> Prelude.Just (Prelude.Right
                    ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                      reason links));
                   Prelude.False -> Prelude.Just p}};
               Prelude.False ->
                case (Prelude.==) reason (VLit (Atom "normal")) of {
                 Prelude.True -> Prelude.Just p;
                 Prelude.False ->
                  case (Prelude.==) reason (VLit (Atom "kill")) of {
                   Prelude.True -> Prelude.Just (Prelude.Right
                    ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                      (VLit (Atom "killed")) links));
                   Prelude.False -> Prelude.Just (Prelude.Right
                    ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                      reason links))}}}}}}}};
   Prelude.Right _ -> Prelude.Nothing}

processLocalStepAArrive :: PID -> PID -> Signal -> Process -> Prelude.Maybe
                           Process
processLocalStepAArrive source dest msg p =
  case msg of {
   SMessage v ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links ->
          case p1 of {
           (,) p2 mb -> Prelude.Just (Prelude.Left ((,) ((,) ((,) p2
            (mailboxPush mb v)) links) flag))}}};
     Prelude.Right _ -> Prelude.Nothing};
   SExit reason b -> plsAArriveSExit source dest reason b p;
   SLink ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links -> Prelude.Just (Prelude.Left ((,) ((,) p1
          (Data.HashSet.insert source links)) flag))}};
     Prelude.Right _ -> Prelude.Nothing};
   SUnlink ->
    case p of {
     Prelude.Left l ->
      case l of {
       (,) p0 flag ->
        case p0 of {
         (,) p1 links -> Prelude.Just (Prelude.Left ((,) ((,) p1
          (Data.HashSet.delete source links)) flag))}};
     Prelude.Right _ -> Prelude.Nothing}}

processLocalStepASelf :: PID -> Process -> Prelude.Maybe Process
processLocalStepASelf _UU03b9_ p =
  case p of {
   Prelude.Left l ->
    case l of {
     (,) p0 flag ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case p2 of {
           (,) f r ->
            case f of {
             ([]) -> Prelude.Nothing;
             (:) f0 fs ->
              case f0 of {
               FParams ident vl el ->
                case ident of {
                 ICall m f1 ->
                  case m of {
                   VLit l0 ->
                    case l0 of {
                     Atom str_erlang ->
                      case f1 of {
                       VLit l1 ->
                        case l1 of {
                         Atom str_self ->
                          case vl of {
                           ([]) ->
                            case el of {
                             ([]) ->
                              case r of {
                               RBox ->
                                case (Prelude.&&)
                                       (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                         str_erlang "erlang")
                                       (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                         str_self "self") of {
                                 Prelude.True -> Prelude.Just (Prelude.Left
                                  ((,) ((,) ((,) ((,) fs (RValSeq ((:) (VPid
                                  _UU03b9_) ([])))) mb) links) flag));
                                 Prelude.False -> Prelude.Nothing};
                               _ -> Prelude.Nothing};
                             (:) _ _ -> Prelude.Nothing};
                           (:) _ _ -> Prelude.Nothing};
                         Integer _ -> Prelude.Nothing};
                       _ -> Prelude.Nothing};
                     Integer _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing};
               _ -> Prelude.Nothing}}}}}};
   Prelude.Right _ -> Prelude.Nothing}

plsASpawnSpawn :: PID -> (([])
                  ((,) ((,) Prelude.Integer Prelude.Integer) Exp)) ->
                  Prelude.Integer -> Prelude.Integer -> Exp -> Val -> Process
                  -> Prelude.Maybe Process
plsASpawnSpawn _UU03b9_ ext id vars e l p =
  case p of {
   Prelude.Left l0 ->
    case l0 of {
     (,) p0 flag ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case p2 of {
           (,) f r ->
            case f of {
             ([]) -> Prelude.Nothing;
             (:) f0 fs ->
              case f0 of {
               FParams ident vl el ->
                case ident of {
                 ICall m f1 ->
                  case m of {
                   VLit l1 ->
                    case l1 of {
                     Atom str_erlang ->
                      case f1 of {
                       VLit l2 ->
                        case l2 of {
                         Atom str_spawn ->
                          case vl of {
                           ([]) -> Prelude.Nothing;
                           (:) lv l3 ->
                            case l3 of {
                             ([]) ->
                              case el of {
                               ([]) ->
                                case r of {
                                 RValSeq vs ->
                                  case vs of {
                                   ([]) -> Prelude.Nothing;
                                   (:) l' l4 ->
                                    case l4 of {
                                     ([]) ->
                                      case (Prelude.&&)
                                             (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               str_erlang "erlang")
                                             (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               str_spawn "spawn") of {
                                       Prelude.True ->
                                        case (Prelude.&&)
                                               ((Prelude.==) lv (VClos ext id
                                                 vars e))
                                               ((Prelude.==) l' l) of {
                                         Prelude.True -> Prelude.Just
                                          (Prelude.Left ((,) ((,) ((,) ((,)
                                          fs (RValSeq ((:) (VPid _UU03b9_)
                                          ([])))) mb) links) flag));
                                         Prelude.False -> Prelude.Nothing};
                                       Prelude.False -> Prelude.Nothing};
                                     (:) _ _ -> Prelude.Nothing}};
                                 _ -> Prelude.Nothing};
                               (:) _ _ -> Prelude.Nothing};
                             (:) _ _ -> Prelude.Nothing}};
                         Integer _ -> Prelude.Nothing};
                       _ -> Prelude.Nothing};
                     Integer _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing};
               _ -> Prelude.Nothing}}}}}};
   Prelude.Right _ -> Prelude.Nothing}

plsASpawnSpawnLink :: PID -> (([])
                      ((,) ((,) Prelude.Integer Prelude.Integer) Exp)) ->
                      Prelude.Integer -> Prelude.Integer -> Exp -> Val ->
                      Process -> Prelude.Maybe Process
plsASpawnSpawnLink _UU03b9_ ext id vars e l p =
  case p of {
   Prelude.Left l0 ->
    case l0 of {
     (,) p0 flag ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case p2 of {
           (,) f r ->
            case f of {
             ([]) -> Prelude.Nothing;
             (:) f0 fs ->
              case f0 of {
               FParams ident vl el ->
                case ident of {
                 ICall m f1 ->
                  case m of {
                   VLit l1 ->
                    case l1 of {
                     Atom str_erlang ->
                      case f1 of {
                       VLit l2 ->
                        case l2 of {
                         Atom str_spawn_link ->
                          case vl of {
                           ([]) -> Prelude.Nothing;
                           (:) lv l3 ->
                            case l3 of {
                             ([]) ->
                              case el of {
                               ([]) ->
                                case r of {
                                 RValSeq vs ->
                                  case vs of {
                                   ([]) -> Prelude.Nothing;
                                   (:) l' l4 ->
                                    case l4 of {
                                     ([]) ->
                                      case (Prelude.&&)
                                             (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               str_erlang "erlang")
                                             (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               str_spawn_link "spawn_link") of {
                                       Prelude.True ->
                                        case (Prelude.&&)
                                               ((Prelude.==) lv (VClos ext id
                                                 vars e))
                                               ((Prelude.==) l' l) of {
                                         Prelude.True -> Prelude.Just
                                          (Prelude.Left ((,) ((,) ((,) ((,)
                                          fs (RValSeq ((:) (VPid _UU03b9_)
                                          ([])))) mb)
                                          (Data.HashSet.insert _UU03b9_
                                            links))
                                          flag));
                                         Prelude.False -> Prelude.Nothing};
                                       Prelude.False -> Prelude.Nothing};
                                     (:) _ _ -> Prelude.Nothing}};
                                 _ -> Prelude.Nothing};
                               (:) _ _ -> Prelude.Nothing};
                             (:) _ _ -> Prelude.Nothing}};
                         Integer _ -> Prelude.Nothing};
                       _ -> Prelude.Nothing};
                     Integer _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing};
               _ -> Prelude.Nothing}}}}}};
   Prelude.Right _ -> Prelude.Nothing}

processLocalStepASpawn :: PID -> (([])
                          ((,) ((,) Prelude.Integer Prelude.Integer) Exp)) ->
                          Prelude.Integer -> Prelude.Integer -> Exp -> Val ->
                          Prelude.Bool -> Process -> Prelude.Maybe Process
processLocalStepASpawn _UU03b9_ ext id vars e l l_flag p =
  case len l of {
   Prelude.Just vars' ->
    case (Prelude.==) vars' vars of {
     Prelude.True ->
      case l_flag of {
       Prelude.True -> plsASpawnSpawnLink _UU03b9_ ext id vars e l p;
       Prelude.False -> plsASpawnSpawn _UU03b9_ ext id vars e l p};
     Prelude.False -> Prelude.Nothing};
   Prelude.Nothing -> Prelude.Nothing}

processLocalStepTau :: Process -> Prelude.Maybe Process
processLocalStepTau p =
  case p of {
   Prelude.Left l ->
    case l of {
     (,) p0 flag ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case p2 of {
           (,) fs e ->
            case sequentialStepFunc fs e of {
             Prelude.Just p3 -> Prelude.Just (Prelude.Left ((,) ((,) ((,) p3
              mb) links) flag));
             Prelude.Nothing ->
              case fs of {
               ([]) -> Prelude.Nothing;
               (:) f fs' ->
                case f of {
                 FParams ident vl el ->
                  case ident of {
                   ICall m f0 ->
                    case m of {
                     VLit l0 ->
                      case l0 of {
                       Atom str_erlang ->
                        case f0 of {
                         VLit l1 ->
                          case l1 of {
                           Atom str_process_flag ->
                            case vl of {
                             ([]) -> Prelude.Nothing;
                             (:) v l2 ->
                              case v of {
                               VLit l3 ->
                                case l3 of {
                                 Atom str_trap_exit ->
                                  case l2 of {
                                   ([]) ->
                                    case el of {
                                     ([]) ->
                                      case (Prelude.&&)
                                             ((Prelude.&&)
                                               (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_erlang "erlang")
                                               (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_process_flag
                                                 "process_flag"))
                                             (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               str_trap_exit "trap_exit") of {
                                       Prelude.True ->
                                        case e of {
                                         RValSeq vs ->
                                          case vs of {
                                           ([]) -> Prelude.Nothing;
                                           (:) v0 l4 ->
                                            case l4 of {
                                             ([]) ->
                                              case bool_from_lit v0 of {
                                               Prelude.Just _ ->
                                                Prelude.Nothing;
                                               Prelude.Nothing ->
                                                Prelude.Just (Prelude.Left
                                                ((,) ((,) ((,) ((,) fs' (RExc
                                                (badarg v0))) mb) links)
                                                flag))};
                                             (:) _ _ -> Prelude.Nothing}};
                                         _ -> Prelude.Nothing};
                                       Prelude.False -> Prelude.Nothing};
                                     (:) _ _ -> Prelude.Nothing};
                                   (:) _ _ -> Prelude.Nothing};
                                 Integer _ -> Prelude.Nothing};
                               _ -> Prelude.Nothing}};
                           Integer _ -> Prelude.Nothing};
                         _ -> Prelude.Nothing};
                       Integer _ -> Prelude.Nothing};
                     _ -> Prelude.Nothing};
                   IPrimOp str_primop ->
                    case vl of {
                     ([]) ->
                      case el of {
                       ([]) ->
                        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                               str_primop "recv_peek_message" of {
                         Prelude.True ->
                          case e of {
                           RBox ->
                            case peekMessage mb of {
                             Prelude.Just msg -> Prelude.Just (Prelude.Left
                              ((,) ((,) ((,) ((,) fs' (RValSeq ((:) (VLit
                              (Atom "true")) ((:) msg ([]))))) mb) links)
                              flag));
                             Prelude.Nothing -> Prelude.Nothing};
                           _ -> Prelude.Nothing};
                         Prelude.False ->
                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                 str_primop "recv_next" of {
                           Prelude.True ->
                            case e of {
                             RBox ->
                              case recvNext mb of {
                               Prelude.Just mb' -> Prelude.Just (Prelude.Left
                                ((,) ((,) ((,) ((,) fs' (RValSeq ((:) (VLit
                                (Atom "ok")) ([])))) mb') links) flag));
                               Prelude.Nothing -> Prelude.Nothing};
                             _ -> Prelude.Nothing};
                           Prelude.False ->
                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                   str_primop "remove_message" of {
                             Prelude.True ->
                              case e of {
                               RBox ->
                                case removeMessage mb of {
                                 Prelude.Just mb' -> Prelude.Just
                                  (Prelude.Left ((,) ((,) ((,) ((,) fs'
                                  (RValSeq ((:) (VLit (Atom "ok")) ([]))))
                                  mb') links) flag));
                                 Prelude.Nothing -> Prelude.Nothing};
                               _ -> Prelude.Nothing};
                             Prelude.False ->
                              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                     str_primop "recv_wait_timeout" of {
                               Prelude.True ->
                                case e of {
                                 RValSeq vs ->
                                  case vs of {
                                   ([]) -> Prelude.Nothing;
                                   (:) v l0 ->
                                    case l0 of {
                                     ([]) ->
                                      case v of {
                                       VLit l1 ->
                                        case l1 of {
                                         Atom str_infinity ->
                                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 str_infinity "infinity" of {
                                           Prelude.True ->
                                            case mb of {
                                             (,) oldmb l2 ->
                                              case l2 of {
                                               ([]) -> Prelude.Nothing;
                                               (:) msg newmb -> Prelude.Just
                                                (Prelude.Left ((,) ((,) ((,)
                                                ((,) fs' (RValSeq ((:) (VLit
                                                (Atom "false")) ([])))) ((,)
                                                oldmb ((:) msg newmb)))
                                                links) flag))}};
                                           Prelude.False -> Prelude.Just
                                            (Prelude.Left ((,) ((,) ((,) ((,)
                                            fs' (RExc (timeout_value v))) mb)
                                            links) flag))};
                                         Integer x ->
                                          (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
                                            (\_ -> Prelude.Just (Prelude.Left
                                            ((,) ((,) ((,) ((,) fs' (RValSeq
                                            ((:) (VLit (Atom "true")) ([]))))
                                            mb) links) flag)))
                                            (\_ -> Prelude.Just (Prelude.Left
                                            ((,) ((,) ((,) ((,) fs' (RExc
                                            (timeout_value v))) mb) links)
                                            flag)))
                                            (\_ -> Prelude.Just (Prelude.Left
                                            ((,) ((,) ((,) ((,) fs' (RExc
                                            (timeout_value v))) mb) links)
                                            flag)))
                                            x};
                                       _ -> Prelude.Just (Prelude.Left ((,)
                                        ((,) ((,) ((,) fs' (RExc
                                        (timeout_value v))) mb) links) flag))};
                                     (:) _ _ -> Prelude.Nothing}};
                                 _ -> Prelude.Nothing};
                               Prelude.False -> Prelude.Nothing}}}};
                       (:) _ _ -> Prelude.Nothing};
                     (:) _ _ -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 _ -> Prelude.Nothing}}}}}}};
   Prelude.Right _ -> Prelude.Nothing}

processLocalStepEps :: Process -> Prelude.Maybe Process
processLocalStepEps p =
  case p of {
   Prelude.Left l ->
    case l of {
     (,) p0 flag ->
      case p0 of {
       (,) p1 links ->
        case p1 of {
         (,) p2 mb ->
          case p2 of {
           (,) f e ->
            case f of {
             ([]) ->
              case e of {
               RValSeq vs ->
                case vs of {
                 ([]) -> Prelude.Nothing;
                 (:) _ l0 ->
                  case l0 of {
                   ([]) -> Prelude.Just (Prelude.Right
                    ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                      (VLit (Atom "normal")) links));
                   (:) _ _ -> Prelude.Nothing}};
               RExc exc -> Prelude.Just (Prelude.Right
                ((\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])
                  (Prelude.snd (Prelude.fst exc)) links));
               _ -> Prelude.Nothing};
             (:) f0 fs ->
              case f0 of {
               FParams ident vl el ->
                case el of {
                 ([]) ->
                  case ident of {
                   ICall m f1 ->
                    case m of {
                     VLit l0 ->
                      case l0 of {
                       Atom str_erlang ->
                        case f1 of {
                         VLit l1 ->
                          case l1 of {
                           Atom str_process_flag ->
                            case (Prelude.&&)
                                   (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                     str_erlang "erlang")
                                   (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                     str_process_flag "process_flag") of {
                             Prelude.True ->
                              case vl of {
                               ([]) -> Prelude.Nothing;
                               (:) v l2 ->
                                case v of {
                                 VLit l3 ->
                                  case l3 of {
                                   Atom str_trap_exit ->
                                    case l2 of {
                                     ([]) ->
                                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                             str_trap_exit "trap_exit" of {
                                       Prelude.True ->
                                        case e of {
                                         RValSeq vs ->
                                          case vs of {
                                           ([]) -> Prelude.Nothing;
                                           (:) v0 l4 ->
                                            case l4 of {
                                             ([]) ->
                                              case bool_from_lit v0 of {
                                               Prelude.Just y -> Prelude.Just
                                                (Prelude.Left ((,) ((,) ((,)
                                                ((,) fs (RValSeq ((:)
                                                (lit_from_bool flag) ([]))))
                                                mb) links) y));
                                               Prelude.Nothing ->
                                                Prelude.Nothing};
                                             (:) _ _ -> Prelude.Nothing}};
                                         _ -> Prelude.Nothing};
                                       Prelude.False -> Prelude.Nothing};
                                     (:) _ _ -> Prelude.Nothing};
                                   Integer _ -> Prelude.Nothing};
                                 _ -> Prelude.Nothing}};
                             Prelude.False -> Prelude.Nothing};
                           Integer _ -> Prelude.Nothing};
                         _ -> Prelude.Nothing};
                       Integer _ -> Prelude.Nothing};
                     _ -> Prelude.Nothing};
                   IPrimOp str_recv_peek_message ->
                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           str_recv_peek_message "recv_peek_message" of {
                     Prelude.True ->
                      case vl of {
                       ([]) ->
                        case e of {
                         RBox ->
                          case peekMessage mb of {
                           Prelude.Just _ -> Prelude.Nothing;
                           Prelude.Nothing -> Prelude.Just (Prelude.Left ((,)
                            ((,) ((,) ((,) fs (RValSeq ((:) (VLit (Atom
                            "false")) ((:) errorVal ([]))))) mb) links)
                            flag))};
                         _ -> Prelude.Nothing};
                       (:) _ _ -> Prelude.Nothing};
                     Prelude.False -> Prelude.Nothing};
                   _ -> Prelude.Nothing};
                 (:) _ _ -> Prelude.Nothing};
               _ -> Prelude.Nothing}}}}}};
   Prelude.Right _ -> Prelude.Nothing}

processLocalStepFunc :: Process -> Action -> Prelude.Maybe Process
processLocalStepFunc p a =
  case a of {
   ASend _ _UU03b9_ msg -> processLocalStepASend _UU03b9_ msg p;
   AArrive source dest msg -> processLocalStepAArrive source dest msg p;
   ASelf _UU03b9_ -> processLocalStepASelf _UU03b9_ p;
   ASpawn _UU03b9_ t1 l l_flag ->
    case t1 of {
     VClos ext id vars e ->
      processLocalStepASpawn _UU03b9_ ext id vars e l l_flag p;
     _ -> Prelude.Nothing};
   Coq__UU03c4_ -> processLocalStepTau p;
   Coq__UU03b5_ -> processLocalStepEps p}

interProcessStepFunc :: Node -> Action -> PID -> Prelude.Maybe Node
interProcessStepFunc pat a pid =
  case pat of {
   (,) eth prs ->
    case Data.HashMap.Strict.lookup pid prs of {
     Prelude.Just p ->
      case a of {
       ASend sourcePID destPID sig ->
        case (Prelude.==) sourcePID pid of {
         Prelude.True ->
          case processLocalStepFunc p a of {
           Prelude.Just p' -> Prelude.Just ((,)
            (etherAdd_Interp sourcePID destPID sig eth)
            (Data.HashMap.Strict.insert pid p' prs));
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.False -> Prelude.Nothing};
       AArrive sourcePID destPID sig ->
        case (Prelude.==) destPID pid of {
         Prelude.True ->
          case etherPop_Interp sourcePID destPID eth of {
           Prelude.Just p0 ->
            case p0 of {
             (,) t eth' ->
              case (Prelude.==) sig t of {
               Prelude.True ->
                case processLocalStepFunc p a of {
                 Prelude.Just p' -> Prelude.Just ((,) eth'
                  (Data.HashMap.Strict.insert pid p' prs));
                 Prelude.Nothing -> Prelude.Nothing};
               Prelude.False -> Prelude.Nothing}};
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.False -> Prelude.Nothing};
       ASelf selfPID ->
        case (Prelude.==) selfPID pid of {
         Prelude.True ->
          case processLocalStepFunc p a of {
           Prelude.Just p' -> Prelude.Just ((,) eth
            (Data.HashMap.Strict.insert pid p' prs));
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.False -> Prelude.Nothing};
       ASpawn freshPID v1 v2 link_flag ->
        case mk_list v2 of {
         Prelude.Just l ->
          case (Prelude.||) (usedInPool_Interp freshPID prs)
                 (usedInEther_Interp freshPID eth) of {
           Prelude.True -> Prelude.Nothing;
           Prelude.False ->
            case create_result_Interp (IApp v1) l of {
             Prelude.Just p0 ->
              case p0 of {
               (,) r _ ->
                case processLocalStepFunc p a of {
                 Prelude.Just p' -> Prelude.Just ((,) eth
                  (Data.HashMap.Strict.insert freshPID (Prelude.Left ((,)
                    ((,) ((,) ((,) ([]) r) emptyBox)
                    (case link_flag of {
                      Prelude.True -> Data.HashSet.singleton pid;
                      Prelude.False -> Data.HashSet.empty}))
                    Prelude.False)) (Data.HashMap.Strict.insert pid p' prs)));
                 Prelude.Nothing -> Prelude.Nothing}};
             Prelude.Nothing -> Prelude.Nothing}};
         Prelude.Nothing -> Prelude.Nothing};
       _ ->
        case processLocalStepFunc p a of {
         Prelude.Just p' -> Prelude.Just ((,) eth
          (Data.HashMap.Strict.insert pid p' prs));
         Prelude.Nothing -> Prelude.Nothing}};
     Prelude.Nothing -> Prelude.Nothing}}

nonArrivalAction :: LiveProcess -> PID -> PID -> Action
nonArrivalAction pat selfPID freshPID =
  case pat of {
   (,) p _ ->
    case p of {
     (,) p0 _ ->
      case p0 of {
       (,) p1 mb ->
        case p1 of {
         (,) fs e ->
          case fs of {
           ([]) ->
            case e of {
             RValSeq vs ->
              case vs of {
               ([]) -> Coq__UU03c4_;
               (:) _ l ->
                case l of {
                 ([]) -> Coq__UU03b5_;
                 (:) _ _ -> Coq__UU03c4_}};
             RExc _ -> Coq__UU03b5_;
             _ -> Coq__UU03c4_};
           (:) f _ ->
            case f of {
             FParams ident lval el ->
              case el of {
               ([]) ->
                case ident of {
                 ICall m f0 ->
                  case m of {
                   VLit l ->
                    case l of {
                     Atom str_erlang ->
                      case f0 of {
                       VLit l0 ->
                        case l0 of {
                         Atom fn ->
                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                 str_erlang "erlang" of {
                           Prelude.True ->
                            case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                   fn "!" of {
                             Prelude.True ->
                              case lval of {
                               ([]) -> Coq__UU03c4_;
                               (:) v l1 ->
                                case v of {
                                 VPid destPID ->
                                  case l1 of {
                                   ([]) ->
                                    case e of {
                                     RValSeq vs ->
                                      case vs of {
                                       ([]) -> Coq__UU03c4_;
                                       (:) v0 l2 ->
                                        case l2 of {
                                         ([]) -> ASend selfPID destPID
                                          (SMessage v0);
                                         (:) _ _ -> Coq__UU03c4_}};
                                     _ -> Coq__UU03c4_};
                                   (:) _ _ -> Coq__UU03c4_};
                                 _ -> Coq__UU03c4_}};
                             Prelude.False ->
                              case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                     fn "exit" of {
                               Prelude.True ->
                                case lval of {
                                 ([]) -> Coq__UU03c4_;
                                 (:) v l1 ->
                                  case v of {
                                   VPid destPID ->
                                    case l1 of {
                                     ([]) ->
                                      case e of {
                                       RValSeq vs ->
                                        case vs of {
                                         ([]) -> Coq__UU03c4_;
                                         (:) v0 l2 ->
                                          case l2 of {
                                           ([]) -> ASend selfPID destPID
                                            (SExit v0 Prelude.False);
                                           (:) _ _ -> Coq__UU03c4_}};
                                       _ -> Coq__UU03c4_};
                                     (:) _ _ -> Coq__UU03c4_};
                                   _ -> Coq__UU03c4_}};
                               Prelude.False ->
                                case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                       fn "link" of {
                                 Prelude.True ->
                                  case lval of {
                                   ([]) ->
                                    case e of {
                                     RValSeq vs ->
                                      case vs of {
                                       ([]) -> Coq__UU03c4_;
                                       (:) v l1 ->
                                        case v of {
                                         VPid destPID ->
                                          case l1 of {
                                           ([]) -> ASend selfPID destPID
                                            SLink;
                                           (:) _ _ -> Coq__UU03c4_};
                                         _ -> Coq__UU03c4_}};
                                     _ -> Coq__UU03c4_};
                                   (:) _ _ -> Coq__UU03c4_};
                                 Prelude.False ->
                                  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                         fn "unlink" of {
                                   Prelude.True ->
                                    case lval of {
                                     ([]) ->
                                      case e of {
                                       RValSeq vs ->
                                        case vs of {
                                         ([]) -> Coq__UU03c4_;
                                         (:) v l1 ->
                                          case v of {
                                           VPid destPID ->
                                            case l1 of {
                                             ([]) -> ASend selfPID destPID
                                              SUnlink;
                                             (:) _ _ -> Coq__UU03c4_};
                                           _ -> Coq__UU03c4_}};
                                       _ -> Coq__UU03c4_};
                                     (:) _ _ -> Coq__UU03c4_};
                                   Prelude.False ->
                                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                           fn "self" of {
                                     Prelude.True ->
                                      case lval of {
                                       ([]) ->
                                        case e of {
                                         RBox -> ASelf selfPID;
                                         _ -> Coq__UU03c4_};
                                       (:) _ _ -> Coq__UU03c4_};
                                     Prelude.False ->
                                      case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                             fn "spawn" of {
                                       Prelude.True ->
                                        case lval of {
                                         ([]) -> Coq__UU03c4_;
                                         (:) v l1 ->
                                          case v of {
                                           VClos ext id vars e' ->
                                            case l1 of {
                                             ([]) ->
                                              case e of {
                                               RValSeq vs ->
                                                case vs of {
                                                 ([]) -> Coq__UU03c4_;
                                                 (:) l2 l3 ->
                                                  case l3 of {
                                                   ([]) -> ASpawn freshPID
                                                    (VClos ext id vars e') l2
                                                    Prelude.False;
                                                   (:) _ _ -> Coq__UU03c4_}};
                                               _ -> Coq__UU03c4_};
                                             (:) _ _ -> Coq__UU03c4_};
                                           _ -> Coq__UU03c4_}};
                                       Prelude.False ->
                                        case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                               fn "spawn_link" of {
                                         Prelude.True ->
                                          case lval of {
                                           ([]) -> Coq__UU03c4_;
                                           (:) v l1 ->
                                            case v of {
                                             VClos ext id vars e' ->
                                              case l1 of {
                                               ([]) ->
                                                case e of {
                                                 RValSeq vs ->
                                                  case vs of {
                                                   ([]) -> Coq__UU03c4_;
                                                   (:) l2 l3 ->
                                                    case l3 of {
                                                     ([]) -> ASpawn freshPID
                                                      (VClos ext id vars e')
                                                      l2 Prelude.True;
                                                     (:) _ _ -> Coq__UU03c4_}};
                                                 _ -> Coq__UU03c4_};
                                               (:) _ _ -> Coq__UU03c4_};
                                             _ -> Coq__UU03c4_}};
                                         Prelude.False ->
                                          case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                 fn "process_flag" of {
                                           Prelude.True ->
                                            case lval of {
                                             ([]) -> Coq__UU03c4_;
                                             (:) v l1 ->
                                              case v of {
                                               VLit l2 ->
                                                case l2 of {
                                                 Atom str_trap_exit ->
                                                  case l1 of {
                                                   ([]) ->
                                                    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                                           str_trap_exit
                                                           "trap_exit" of {
                                                     Prelude.True ->
                                                      case e of {
                                                       RValSeq vs ->
                                                        case vs of {
                                                         ([]) -> Coq__UU03c4_;
                                                         (:) v0 l3 ->
                                                          case l3 of {
                                                           ([]) ->
                                                            case bool_from_lit
                                                                   v0 of {
                                                             Prelude.Just _ ->
                                                              Coq__UU03b5_;
                                                             Prelude.Nothing ->
                                                              Coq__UU03c4_};
                                                           (:) _ _ ->
                                                            Coq__UU03c4_}};
                                                       _ -> Coq__UU03c4_};
                                                     Prelude.False ->
                                                      Coq__UU03c4_};
                                                   (:) _ _ -> Coq__UU03c4_};
                                                 Integer _ -> Coq__UU03c4_};
                                               _ -> Coq__UU03c4_}};
                                           Prelude.False -> Coq__UU03c4_}}}}}}}};
                           Prelude.False -> Coq__UU03c4_};
                         Integer _ -> Coq__UU03c4_};
                       _ -> Coq__UU03c4_};
                     Integer _ -> Coq__UU03c4_};
                   _ -> Coq__UU03c4_};
                 IPrimOp str_recv_peek_message ->
                  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                         str_recv_peek_message "recv_peek_message" of {
                   Prelude.True ->
                    case e of {
                     RBox ->
                      case peekMessage mb of {
                       Prelude.Just _ -> Coq__UU03c4_;
                       Prelude.Nothing -> Coq__UU03b5_};
                     _ -> Coq__UU03c4_};
                   Prelude.False -> Coq__UU03c4_};
                 _ -> Coq__UU03c4_};
               (:) _ _ -> Coq__UU03c4_};
             _ -> Coq__UU03c4_}}}}}}

deadActions :: DeadProcess -> PID -> ([]) Action
deadActions p selfPID =
  let {links = Data.HashSet.toList (Data.HashMap.Strict.keysSet p)} in
  let {
   f l =
     case l of {
      ([]) -> ([]);
      (:) linkPID l' ->
       case Data.HashMap.Strict.lookup linkPID p of {
        Prelude.Just reason -> (:) (ASend selfPID linkPID (SExit reason
         Prelude.True)) (f l');
        Prelude.Nothing -> f l'}}}
  in f links

unavailablePIDs :: Node -> Gset PID
unavailablePIDs pat =
  case pat of {
   (,) eth prs ->
    Data.HashSet.union (allPIDsEther_Interp eth) (allPIDsPool_Interp prs)}

makeInitialNode :: Redex -> Node
makeInitialNode r =
  let {
   p = Prelude.Left ((,) ((,) ((,) ((,) ([]) r) emptyBox) Data.HashSet.empty)
    Prelude.False)}
  in
  let {
   initPID = (\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))
               (usedPIDsProc_Interp p)}
  in
  (,) Data.HashMap.Strict.empty (Data.HashMap.Strict.singleton initPID p)

makeInitialConfig :: Redex -> (,) Node PID
makeInitialConfig r =
  let {
   p = Prelude.Left ((,) ((,) ((,) ((,) ([]) r) emptyBox) Data.HashSet.empty)
    Prelude.False)}
  in
  let {
   initPID = (\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))
               (usedPIDsProc_Interp p)}
  in
  (,) ((,) Data.HashMap.Strict.empty
  (Data.HashMap.Strict.singleton initPID p)) initPID

ex_Redex :: Redex
ex_Redex =
  RExp (EExp (ELetRec ((:) ((,) (Prelude.succ 0) (EExp (ECase (VVal (VVar
    (Prelude.succ 0))) ((:) ((,) ((,) ((:) (PLit (Integer 0)) ([])) (VVal
    (VLit (Atom "true")))) (VVal (VLit (Integer ((\x -> x) 1))))) ((:) ((,)
    ((,) ((:) PVar ([])) (VVal (VLit (Atom "true")))) (EExp (ELet
    (Prelude.succ 0) (EExp (EApp (VVal (VFunId ((,) (Prelude.succ 0)
    (Prelude.succ 0)))) ((:) (EExp (ECall (VVal (VLit (Atom "erlang"))) (VVal
    (VLit (Atom "-"))) ((:) (VVal (VVar 0)) ((:) (VVal (VLit (Integer
    ((\x -> x) 1)))) ([]))))) ([])))) (EExp (ECall (VVal (VLit (Atom
    "erlang"))) (VVal (VLit (Atom "*"))) ((:) (VVal (VVar (Prelude.succ 0)))
    ((:) (VVal (VVar 0)) ([])))))))) ([])))))) ([])) (EExp (EApp (VVal
    (VFunId ((,) 0 (Prelude.succ 0)))) ((:) (VVal (VLit (Integer ((\x -> x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    1)))))))) ([]))))))

ex_Process :: Process
ex_Process =
  Prelude.Left ((,) ((,) ((,) ((,) ([]) ex_Redex) emptyBox)
    Data.HashSet.empty) Prelude.False)

nodeSimpleStep :: Node -> (Prelude.Either PID ((,) PID PID)) -> Prelude.Maybe
                  ((,) Node Action)
nodeSimpleStep pat op =
  case pat of {
   (,) eth prs ->
    case op of {
     Prelude.Left selfPID ->
      case Data.HashMap.Strict.lookup selfPID prs of {
       Prelude.Just p0 ->
        case p0 of {
         Prelude.Left p ->
          let {
           a = nonArrivalAction p selfPID
                 ((\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))
                   (unavailablePIDs ((,) eth prs)))}
          in
          case interProcessStepFunc ((,) eth prs) a selfPID of {
           Prelude.Just node' -> Prelude.Just ((,) node' a);
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.Right p ->
          case deadActions p selfPID of {
           ([]) -> Prelude.Nothing;
           (:) a _ ->
            case interProcessStepFunc ((,) eth prs) a selfPID of {
             Prelude.Just node' -> Prelude.Just ((,) node' a);
             Prelude.Nothing -> Prelude.Nothing}}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Right p ->
      case p of {
       (,) srcPID dstPID ->
        case Data.HashMap.Strict.lookup ((,) srcPID dstPID) eth of {
         Prelude.Just l ->
          case l of {
           ([]) -> Prelude.Nothing;
           (:) v _ ->
            let {a = AArrive srcPID dstPID v} in
            case interProcessStepFunc ((,) eth prs) a dstPID of {
             Prelude.Just node' -> Prelude.Just ((,) node' a);
             Prelude.Nothing -> Prelude.Nothing}};
         Prelude.Nothing -> Prelude.Nothing}}}}

interProcessStepFuncFast :: Node -> PID -> (Prelude.Either PID ((,) PID PID))
                            -> Prelude.Maybe ((,) ((,) Node Action) PID)
interProcessStepFuncFast pat hiPID op =
  case pat of {
   (,) eth prs ->
    case op of {
     Prelude.Left pid ->
      case Data.HashMap.Strict.lookup pid prs of {
       Prelude.Just p0 ->
        case p0 of {
         Prelude.Left p ->
          let {a = nonArrivalAction p pid (Prelude.succ hiPID)} in
          case a of {
           ASend sourcePID destPID sig ->
            case (Prelude.==) sourcePID pid of {
             Prelude.True ->
              case processLocalStepFunc (Prelude.Left p) a of {
               Prelude.Just p' -> Prelude.Just ((,) ((,) ((,)
                (etherAdd_Interp sourcePID destPID sig eth)
                (Data.HashMap.Strict.insert pid p' prs)) a) hiPID);
               Prelude.Nothing -> Prelude.Nothing};
             Prelude.False -> Prelude.Nothing};
           AArrive _ _ _ -> Prelude.Nothing;
           ASelf selfPID ->
            case (Prelude.==) selfPID pid of {
             Prelude.True ->
              case processLocalStepFunc (Prelude.Left p) a of {
               Prelude.Just p' -> Prelude.Just ((,) ((,) ((,) eth
                (Data.HashMap.Strict.insert pid p' prs)) a) hiPID);
               Prelude.Nothing -> Prelude.Nothing};
             Prelude.False -> Prelude.Nothing};
           ASpawn freshPID v1 v2 link_flag ->
            case mk_list v2 of {
             Prelude.Just l ->
              case create_result_Interp (IApp v1) l of {
               Prelude.Just p1 ->
                case p1 of {
                 (,) r _ ->
                  case processLocalStepFunc (Prelude.Left p) a of {
                   Prelude.Just p' -> Prelude.Just ((,) ((,) ((,) eth
                    (Data.HashMap.Strict.insert freshPID (Prelude.Left ((,)
                      ((,) ((,) ((,) ([]) r) emptyBox)
                      (case link_flag of {
                        Prelude.True -> Data.HashSet.singleton pid;
                        Prelude.False -> Data.HashSet.empty}))
                      Prelude.False))
                      (Data.HashMap.Strict.insert pid p' prs)))
                    a) (Prelude.succ hiPID));
                   Prelude.Nothing -> Prelude.Nothing}};
               Prelude.Nothing -> Prelude.Nothing};
             Prelude.Nothing -> Prelude.Nothing};
           _ ->
            case processLocalStepFunc (Prelude.Left p) a of {
             Prelude.Just p' -> Prelude.Just ((,) ((,) ((,) eth
              (Data.HashMap.Strict.insert pid p' prs)) a) hiPID);
             Prelude.Nothing -> Prelude.Nothing}};
         Prelude.Right p ->
          case deadActions p pid of {
           ([]) -> Prelude.Nothing;
           (:) a _ ->
            case a of {
             ASend sourcePID destPID sig ->
              case (Prelude.==) sourcePID pid of {
               Prelude.True ->
                case processLocalStepFunc (Prelude.Right p) a of {
                 Prelude.Just p' -> Prelude.Just ((,) ((,) ((,)
                  (etherAdd_Interp sourcePID destPID sig eth)
                  (Data.HashMap.Strict.insert pid p' prs)) a) hiPID);
                 Prelude.Nothing -> Prelude.Nothing};
               Prelude.False -> Prelude.Nothing};
             _ -> Prelude.Nothing}}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Right p ->
      case p of {
       (,) srcPID dstPID ->
        case Data.HashMap.Strict.lookup dstPID prs of {
         Prelude.Just p0 ->
          case Data.HashMap.Strict.lookup ((,) srcPID dstPID) eth of {
           Prelude.Just l ->
            case l of {
             ([]) -> Prelude.Nothing;
             (:) v _ ->
              let {a = AArrive srcPID dstPID v} in
              case etherPop_Interp srcPID dstPID eth of {
               Prelude.Just p1 ->
                case p1 of {
                 (,) _ eth' ->
                  case processLocalStepFunc p0 a of {
                   Prelude.Just p' -> Prelude.Just ((,) ((,) ((,) eth'
                    (Data.HashMap.Strict.insert dstPID p' prs)) a) hiPID);
                   Prelude.Nothing -> Prelude.Nothing}};
               Prelude.Nothing -> Prelude.Nothing}};
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing}}}}

nodeTauFirstStep :: Node -> PID -> Prelude.Maybe ((,) Node (([]) Action))
nodeTauFirstStep pat pid =
  case pat of {
   (,) eth prs ->
    case Data.HashMap.Strict.lookup pid prs of {
     Prelude.Just p0 ->
      case p0 of {
       Prelude.Left p ->
        case processLocalStepTau (Prelude.Left p) of {
         Prelude.Just p' -> Prelude.Just ((,) ((,) eth
          (Data.HashMap.Strict.insert pid p' prs)) ([]));
         Prelude.Nothing ->
          case nonArrivalAction p pid
                 ((\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))
                   (unavailablePIDs ((,) eth prs))) of {
           Coq__UU03c4_ -> Prelude.Nothing;
           x -> Prelude.Just ((,) ((,) eth prs) ((:) x ([])))}};
       Prelude.Right p ->
        let {al = deadActions p pid} in Prelude.Just ((,) ((,) eth prs) al)};
     Prelude.Nothing -> Prelude.Nothing}}

isDead :: Node -> PID -> Prelude.Bool
isDead pat pid =
  case pat of {
   (,) _ prs ->
    case Data.HashMap.Strict.lookup pid prs of {
     Prelude.Just p0 ->
      case p0 of {
       Prelude.Left _ -> Prelude.False;
       Prelude.Right _ -> Prelude.True};
     Prelude.Nothing -> Prelude.False}}

isTotallyDead :: Node -> PID -> Prelude.Bool
isTotallyDead pat pid =
  case pat of {
   (,) _ prs ->
    case Data.HashMap.Strict.lookup pid prs of {
     Prelude.Just p0 ->
      case p0 of {
       Prelude.Left _ -> Prelude.False;
       Prelude.Right p ->
        (Prelude.==)
          ((\dead -> Prelude.toInteger (Data.HashMap.Strict.size dead)) p) 0};
     Prelude.Nothing -> Prelude.False}}

etherNonEmpty :: Node -> ([]) ((,) PID PID)
etherNonEmpty pat =
  case pat of {
   (,) eth _ ->
    (Prelude.filter) (\k ->
      case Data.HashMap.Strict.lookup k eth of {
       Prelude.Just l ->
        case l of {
         ([]) -> Prelude.False;
         (:) _ _ -> Prelude.True};
       Prelude.Nothing -> Prelude.False})
      ((\eth -> Data.HashSet.toList (Data.HashMap.Strict.keysSet eth)) eth)}

currentProcessList :: Node -> ([]) PID
currentProcessList pat =
  case pat of {
   (,) _ prs -> Data.HashSet.toList (Data.HashMap.Strict.keysSet prs)}

deriving instance Prelude.Show Uint 
deriving instance GHC.Base.Eq Uint 
deriving instance Prelude.Show Signed_int 
deriving instance GHC.Base.Eq Signed_int 
deriving instance Prelude.Show N 
deriving instance GHC.Base.Eq N 
deriving instance Prelude.Show Bvn 
deriving instance GHC.Base.Eq Bvn 
deriving instance Prelude.Show Lit 
deriving instance GHC.Base.Eq Lit 
deriving instance Prelude.Show BinType 
deriving instance GHC.Base.Eq BinType 
deriving instance Prelude.Show BinSign 
deriving instance GHC.Base.Eq BinSign 
deriving instance Prelude.Show BinEnd 
deriving instance GHC.Base.Eq BinEnd 
deriving instance (Prelude.Show t1, Prelude.Show t2) => Prelude.Show (Segment t1 t2 )
deriving instance (GHC.Base.Eq t1, GHC.Base.Eq t2) => GHC.Base.Eq (Segment t1 t2 )
deriving instance Prelude.Show Exp 
deriving instance GHC.Base.Eq Exp 
deriving instance Prelude.Show Val 
deriving instance GHC.Base.Eq Val 
deriving instance Prelude.Show NonVal 
deriving instance GHC.Base.Eq NonVal 
deriving instance Prelude.Show Pat 
deriving instance GHC.Base.Eq Pat 
deriving instance Prelude.Show ExcClass 
deriving instance GHC.Base.Eq ExcClass 
deriving instance Prelude.Show Redex 
deriving instance GHC.Base.Eq Redex 
deriving instance (Prelude.Show a) => Prelude.Show (Match a )
deriving instance (GHC.Base.Eq a) => GHC.Base.Eq (Match a )
deriving instance Prelude.Show SideEffectId 
deriving instance GHC.Base.Eq SideEffectId 
deriving instance Prelude.Show PrimopCode 
deriving instance GHC.Base.Eq PrimopCode 
deriving instance Prelude.Show BIFCode 
deriving instance GHC.Base.Eq BIFCode 
deriving instance Prelude.Show FrameIdent 
deriving instance GHC.Base.Eq FrameIdent 
deriving instance Prelude.Show Frame 
deriving instance GHC.Base.Eq Frame 
deriving instance Prelude.Show Signal 
deriving instance GHC.Base.Eq Signal 
deriving instance Prelude.Show Action 
deriving instance GHC.Base.Eq Action 

instance NFData Lit where
  rnf (Atom s)     = rnf s
  rnf (Integer i)  = rnf i

instance NFData Exp where
  rnf (VVal v)   = rnf v
  rnf (EExp e)   = rnf e

instance NFData Val where
  rnf VNil                    = ()
  rnf (VLit l)                = rnf l
  rnf (VPid pid)              = rnf pid
  rnf (VCons v1 v2)           = rnf v1 `Prelude.seq` rnf v2
  rnf (VTuple vs)             = rnf vs
  rnf (VMap vps)              = rnf vps
  rnf (VVar v)                = rnf v
  rnf (VFunId f)              = rnf f
  rnf (VClos env n1 n2 body)  = rnf env `Prelude.seq` rnf n1 `Prelude.seq` rnf n2 `Prelude.seq` rnf body

instance NFData NonVal where
  rnf (EFun n e)                    = rnf n `Prelude.seq` rnf e
  rnf (EValues es)                  = rnf es
  rnf (ECons e1 e2)                 = rnf e1 `Prelude.seq` rnf e2
  rnf (ETuple es)                   = rnf es
  rnf (EMap m)                      = rnf m
  rnf (ECall f arg args)            = rnf f `Prelude.seq` rnf arg `Prelude.seq` rnf args
  rnf (EPrimOp s args)              = rnf s `Prelude.seq` rnf args
  rnf (EApp f args)                 = rnf f `Prelude.seq` rnf args
  rnf (ECase scrutinee branches)    = rnf scrutinee `Prelude.seq` rnf branches
  rnf (ELet x e1 e2)                = rnf x `Prelude.seq` rnf e1 `Prelude.seq` rnf e2
  rnf (ESeq e1 e2)                  = rnf e1 `Prelude.seq` rnf e2
  rnf (ELetRec binds e)            = rnf binds `Prelude.seq` rnf e
  rnf (ETry e1 n1 e2 n2 e3)         = rnf e1 `Prelude.seq` rnf n1 `Prelude.seq` rnf e2 `Prelude.seq` rnf n2 `Prelude.seq` rnf e3

instance NFData Pat where
  rnf PVar            = ()
  rnf (PLit lit)      = rnf lit
  rnf (PCons p1 p2)   = rnf p1 `Prelude.seq` rnf p2
  rnf (PTuple ps)     = rnf ps
  rnf (PMap pairs)    = rnf pairs
  rnf PNil            = ()

instance NFData Redex where
  rnf (RExp e)       = rnf e
  rnf (RValSeq vs)   = rnf vs
  rnf (RExc ex)      = rnf ex
  rnf RBox           = ()

instance NFData ExcClass where
  rnf Error = ()
  rnf Throw = ()
  rnf Exit  = ()

instance NFData FrameIdent where
  rnf IValues         = ()
  rnf ITuple          = ()
  rnf IMap            = ()
  rnf (ICall v1 v2)   = rnf v1 `Prelude.seq` rnf v2
  rnf (IPrimOp s)     = rnf s
  rnf (IApp v)        = rnf v

instance NFData Frame where
  rnf (FCons1 e)                     = rnf e
  rnf (FCons2 v)                     = rnf v
  rnf (FParams fid vs es)            = rnf fid `Prelude.seq` rnf vs `Prelude.seq` rnf es
  rnf (FApp1 es)                     = rnf es
  rnf (FCallMod e es)                = rnf e `Prelude.seq` rnf es
  rnf (FCallFun v es)                = rnf v `Prelude.seq` rnf es
  rnf (FCase1 branches)              = rnf branches
  rnf (FCase2 vs e branches)         = rnf vs `Prelude.seq` rnf e `Prelude.seq` rnf branches
  rnf (FLet i e)                     = rnf i `Prelude.seq` rnf e
  rnf (FSeq e)                      = rnf e
  rnf (FTry i1 e1 i2 e2)            = rnf i1 `Prelude.seq` rnf e1 `Prelude.seq` rnf i2 `Prelude.seq` rnf e2

instance NFData Signal where
  rnf (SMessage v)       = rnf v
  rnf (SExit v b)        = rnf v `Prelude.seq` rnf b
  rnf SLink              = ()
  rnf SUnlink            = ()

instance NFData Action where
  rnf (ASend p1 p2 sig)  = rnf p1 `Prelude.seq` rnf p2 `Prelude.seq` rnf sig
  rnf (AArrive p1 p2 sig)= rnf p1 `Prelude.seq` rnf p2 `Prelude.seq` rnf sig
  rnf (ASelf p)          = rnf p
  rnf (ASpawn p v1 v2 b) = rnf p `Prelude.seq` rnf v1 `Prelude.seq` rnf v2 `Prelude.seq` rnf b
  rnf Coq__UU03c4_       = ()
  rnf Coq__UU03b5_       = ()

-- ====================| instances of Hashable for TreeMaker.hs |====================
-- Since the possible non-arrival actions' collection for each tree node is a HashSet
-- type Action needs to have a Hashable instance.
-- Done in a hacky way: first we hash an int representing the constructor type and
-- then proceed to hash an actual value of the datatype.
-- P.S. potentially not needed, if you change th type of possibleNAActions to list.

instance Data.Hashable.Hashable Lit where
  hashWithSalt s (Atom a)   = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` a
  hashWithSalt s (Integer n)= s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` n

instance Data.Hashable.Hashable Exp where
  hashWithSalt s (VVal v)   = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` v
  hashWithSalt s (EExp e)   = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` e

instance Data.Hashable.Hashable Pat where
  hashWithSalt s PVar              = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int)
  hashWithSalt s (PLit l)          = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` l
  hashWithSalt s (PCons p1 p2)     = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int) `Data.Hashable.hashWithSalt` p1 `Data.Hashable.hashWithSalt` p2
  hashWithSalt s (PTuple ps)       = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int) `Data.Hashable.hashWithSalt` ps
  hashWithSalt s (PMap xs)         = s `Data.Hashable.hashWithSalt` (4::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs
  hashWithSalt s PNil              = s `Data.Hashable.hashWithSalt` (5::GHC.Base.Int)

instance Data.Hashable.Hashable ExcClass where
  hashWithSalt s Exit = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int)
  hashWithSalt s Error = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int)
  hashWithSalt s Throw = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int)

instance Data.Hashable.Hashable Redex where
  hashWithSalt s (RExp e)    = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` e
  hashWithSalt s (RValSeq v) = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` v
  hashWithSalt s (RExc ex)   = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int) `Data.Hashable.hashWithSalt` ex
  hashWithSalt s RBox        = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int)

instance Data.Hashable.Hashable NonVal where
  hashWithSalt s (EFun i e)          = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` i `Data.Hashable.hashWithSalt` e
  hashWithSalt s (EValues xs)        = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (ECons a b)         = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int) `Data.Hashable.hashWithSalt` a `Data.Hashable.hashWithSalt` b
  hashWithSalt s (ETuple es)         = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int) `Data.Hashable.hashWithSalt` es
  hashWithSalt s (EMap xs)           = s `Data.Hashable.hashWithSalt` (4::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (ECall a b cs)      = s `Data.Hashable.hashWithSalt` (5::GHC.Base.Int) `Data.Hashable.hashWithSalt` a `Data.Hashable.hashWithSalt` b `Data.Hashable.hashWithSalt` cs
  hashWithSalt s (EPrimOp op es)     = s `Data.Hashable.hashWithSalt` (6::GHC.Base.Int) `Data.Hashable.hashWithSalt` op `Data.Hashable.hashWithSalt` es
  hashWithSalt s (EApp f args)       = s `Data.Hashable.hashWithSalt` (7::GHC.Base.Int) `Data.Hashable.hashWithSalt` f `Data.Hashable.hashWithSalt` args
  hashWithSalt s (ECase e xs)        = s `Data.Hashable.hashWithSalt` (8::GHC.Base.Int) `Data.Hashable.hashWithSalt` e `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (ELet v e1 e2)      = s `Data.Hashable.hashWithSalt` (9::GHC.Base.Int) `Data.Hashable.hashWithSalt` v `Data.Hashable.hashWithSalt` e1 `Data.Hashable.hashWithSalt` e2
  hashWithSalt s (ESeq a b)          = s `Data.Hashable.hashWithSalt` (10::GHC.Base.Int) `Data.Hashable.hashWithSalt` a `Data.Hashable.hashWithSalt` b
  hashWithSalt s (ELetRec xs e)      = s `Data.Hashable.hashWithSalt` (11::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs `Data.Hashable.hashWithSalt` e
  hashWithSalt s (ETry body v1 h1 v2 h2) =
    s `Data.Hashable.hashWithSalt` (12::GHC.Base.Int)
      `Data.Hashable.hashWithSalt` body
      `Data.Hashable.hashWithSalt` v1
      `Data.Hashable.hashWithSalt` h1
      `Data.Hashable.hashWithSalt` v2
      `Data.Hashable.hashWithSalt` h2

instance Data.Hashable.Hashable Val where
  hashWithSalt s VNil            = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int)
  hashWithSalt s (VLit l)        = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` l
  hashWithSalt s (VPid p)        = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int) `Data.Hashable.hashWithSalt` p
  hashWithSalt s (VCons a b)     = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int) `Data.Hashable.hashWithSalt` a `Data.Hashable.hashWithSalt` b
  hashWithSalt s (VTuple xs)     = s `Data.Hashable.hashWithSalt` (4::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (VMap xs)       = s `Data.Hashable.hashWithSalt` (5::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (VVar v)        = s `Data.Hashable.hashWithSalt` (6::GHC.Base.Int) `Data.Hashable.hashWithSalt` v
  hashWithSalt s (VFunId f)      = s `Data.Hashable.hashWithSalt` (7::GHC.Base.Int) `Data.Hashable.hashWithSalt` f
  hashWithSalt s (VClos env a b e) =
    s `Data.Hashable.hashWithSalt` (8::GHC.Base.Int)
      `Data.Hashable.hashWithSalt` env
      `Data.Hashable.hashWithSalt` a
      `Data.Hashable.hashWithSalt` b
      `Data.Hashable.hashWithSalt` e

instance Data.Hashable.Hashable Signal where
  hashWithSalt s (SMessage v)  = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` v
  hashWithSalt s (SExit v b)   = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` v `Data.Hashable.hashWithSalt` b
  hashWithSalt s SLink         = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int)
  hashWithSalt s SUnlink       = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int)

instance Data.Hashable.Hashable Action where
  hashWithSalt s (ASend p1 p2 sig) =
    s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` p1
      `Data.Hashable.hashWithSalt` p2 `Data.Hashable.hashWithSalt` sig

  hashWithSalt s (AArrive p1 p2 sig) =
    s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` p1
      `Data.Hashable.hashWithSalt` p2 `Data.Hashable.hashWithSalt` sig

  hashWithSalt s (ASelf pid) =
    s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int) `Data.Hashable.hashWithSalt` pid

  hashWithSalt s (ASpawn pid v1 v2 b) =
    s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int)
      `Data.Hashable.hashWithSalt` pid
      `Data.Hashable.hashWithSalt` v1
      `Data.Hashable.hashWithSalt` v2
      `Data.Hashable.hashWithSalt` b

  hashWithSalt s Coq__UU03c4_ = s `Data.Hashable.hashWithSalt` (4::GHC.Base.Int)
  hashWithSalt s Coq__UU03b5_ = s `Data.Hashable.hashWithSalt` (5::GHC.Base.Int)

instance Data.Hashable.Hashable FrameIdent where
  hashWithSalt s IValues         = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int)
  hashWithSalt s ITuple          = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int)
  hashWithSalt s IMap            = s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int)
  hashWithSalt s (ICall a b)     = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int) `Data.Hashable.hashWithSalt` a `Data.Hashable.hashWithSalt` b
  hashWithSalt s (IPrimOp op)    = s `Data.Hashable.hashWithSalt` (4::GHC.Base.Int) `Data.Hashable.hashWithSalt` op
  hashWithSalt s (IApp v)        = s `Data.Hashable.hashWithSalt` (5::GHC.Base.Int) `Data.Hashable.hashWithSalt` v

instance Data.Hashable.Hashable Frame where
  hashWithSalt s (FCons1 e)          = s `Data.Hashable.hashWithSalt` (0::GHC.Base.Int) `Data.Hashable.hashWithSalt` e
  hashWithSalt s (FCons2 v)          = s `Data.Hashable.hashWithSalt` (1::GHC.Base.Int) `Data.Hashable.hashWithSalt` v
  hashWithSalt s (FParams frameid vs es)  =
    s `Data.Hashable.hashWithSalt` (2::GHC.Base.Int) `Data.Hashable.hashWithSalt` frameid
      `Data.Hashable.hashWithSalt` vs `Data.Hashable.hashWithSalt` es
  hashWithSalt s (FApp1 es)          = s `Data.Hashable.hashWithSalt` (3::GHC.Base.Int) `Data.Hashable.hashWithSalt` es
  hashWithSalt s (FCallMod e es)     = s `Data.Hashable.hashWithSalt` (4::GHC.Base.Int) `Data.Hashable.hashWithSalt` e `Data.Hashable.hashWithSalt` es
  hashWithSalt s (FCallFun v es)     = s `Data.Hashable.hashWithSalt` (5::GHC.Base.Int) `Data.Hashable.hashWithSalt` v `Data.Hashable.hashWithSalt` es
  hashWithSalt s (FCase1 xs)         = s `Data.Hashable.hashWithSalt` (6::GHC.Base.Int) `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (FCase2 vs e xs)    = s `Data.Hashable.hashWithSalt` (7::GHC.Base.Int) `Data.Hashable.hashWithSalt` vs `Data.Hashable.hashWithSalt` e `Data.Hashable.hashWithSalt` xs
  hashWithSalt s (FLet v e)          = s `Data.Hashable.hashWithSalt` (8::GHC.Base.Int) `Data.Hashable.hashWithSalt` v `Data.Hashable.hashWithSalt` e
  hashWithSalt s (FSeq e)            = s `Data.Hashable.hashWithSalt` (9::GHC.Base.Int) `Data.Hashable.hashWithSalt` e
  hashWithSalt s (FTry v1 e1 v2 e2)  =
    s `Data.Hashable.hashWithSalt` (10::GHC.Base.Int)
      `Data.Hashable.hashWithSalt` v1 `Data.Hashable.hashWithSalt` e1
      `Data.Hashable.hashWithSalt` v2 `Data.Hashable.hashWithSalt` e2

{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Model_Checker(Int(..), Nat, nat_of_integer, Char, DBMEntry(..), Act, Bexp,
                 Exp, Acconstraint, Set, Sum, JSON, Result(..), Len_list,
                 Resulta, Mode(..), Formula, State_space(..),
                 parse_convert_check, parse_convert_run_check,
                 parse_convert_run_print)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Heap;
import qualified Uint;
import qualified Array;
import qualified IArray;
import qualified Uint32;
import qualified Printing;
import qualified Data_Bits;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

typerep_int :: Itself Int -> Typerepa;
typerep_int t = Typerep "Int.int" [];

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

class Countable a where {
};

class (Countable a, Typerep a) => Heapa a where {
};

instance Countable Int where {
};

instance Typerep Int where {
  typerep = typerep_int;
};

instance Heapa Int where {
};

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

data Num = One | Bit0 Num | Bit1 Num;

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool;

string_of_digit :: Nat -> [Char];
string_of_digit n =
  (if equal_nat n zero_nat
    then [Char False False False False True True False False]
    else (if equal_nat n one_nat
           then [Char True False False False True True False False]
           else (if equal_nat n (nat_of_integer (2 :: Integer))
                  then [Char False True False False True True False False]
                  else (if equal_nat n (nat_of_integer (3 :: Integer))
                         then [Char True True False False True True False False]
                         else (if equal_nat n (nat_of_integer (4 :: Integer))
                                then [Char False False True False True True
False False]
                                else (if equal_nat n
   (nat_of_integer (5 :: Integer))
                                       then [Char True False True False True
       True False False]
                                       else (if equal_nat n
          (nat_of_integer (6 :: Integer))
      then [Char False True True False True True False False]
      else (if equal_nat n (nat_of_integer (7 :: Integer))
             then [Char True True True False True True False False]
             else (if equal_nat n (nat_of_integer (8 :: Integer))
                    then [Char False False False True True True False False]
                    else [Char True False False True True True False
                            False])))))))));

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

shows_string :: [Char] -> [Char] -> [Char];
shows_string = (\ a b -> a ++ b);

showsp_nat :: Nat -> Nat -> [Char] -> [Char];
showsp_nat p n =
  (if less_nat n (nat_of_integer (10 :: Integer))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 :: Integer))) .
           shows_string
             (string_of_digit (modulo_nat n (nat_of_integer (10 :: Integer)))));

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

nat :: Int -> Nat;
nat k = Nat (max (0 :: Integer) (integer_of_int k));

showsp_int :: Nat -> Int -> [Char] -> [Char];
showsp_int p i =
  (if less_int i zero_int
    then shows_string [Char True False True True False True False False] .
           showsp_nat p (nat (uminus_int i))
    else showsp_nat p (nat i));

shows_prec_int :: Nat -> Int -> [Char] -> [Char];
shows_prec_int = showsp_int;

shows_sep ::
  forall a.
    (a -> [Char] -> [Char]) -> ([Char] -> [Char]) -> [a] -> [Char] -> [Char];
shows_sep s sep [] = shows_string [];
shows_sep s sep [x] = s x;
shows_sep s sep (x : v : va) = (s x . sep) . shows_sep s sep (v : va);

shows_list_gen ::
  forall a.
    (a -> [Char] -> [Char]) ->
      [Char] -> [Char] -> [Char] -> [Char] -> [a] -> [Char] -> [Char];
shows_list_gen showsx e l s r xs =
  (if null xs then shows_string e
    else (shows_string l . shows_sep showsx (shows_string s) xs) .
           shows_string r);

showsp_list ::
  forall a. (Nat -> a -> [Char] -> [Char]) -> Nat -> [a] -> [Char] -> [Char];
showsp_list s p xs =
  shows_list_gen (s zero_nat)
    [Char True True False True True False True False,
      Char True False True True True False True False]
    [Char True True False True True False True False]
    [Char False False True True False True False False,
      Char False False False False False True False False]
    [Char True False True True True False True False] xs;

shows_list_int :: [Int] -> [Char] -> [Char];
shows_list_int = showsp_list shows_prec_int zero_nat;

class Showa a where {
  shows_prec :: Nat -> a -> [Char] -> [Char];
  shows_list :: [a] -> [Char] -> [Char];
};

instance Showa Int where {
  shows_prec = shows_prec_int;
  shows_list = shows_list_int;
};

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Int where {
  plus = plus_int;
};

class Zero a where {
  zero :: a;
};

instance Zero Int where {
  zero = zero_int;
};

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

class Minus a where {
  minus :: a -> a -> a;
};

instance Minus Int where {
  minus = minus_int;
};

class Uminus a where {
  uminus :: a -> a;
};

instance Uminus Int where {
  uminus = uminus_int;
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

instance Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Int where {
};

instance Order Int where {
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Cancel_semigroup_add a, Minus a, Monoid_add a,
        Uminus a) => Group_add a where {
};

instance Semigroup_add Int where {
};

instance Cancel_semigroup_add Int where {
};

instance Monoid_add Int where {
};

instance Group_add Int where {
};

def_hashmap_size_int :: Itself Int -> Nat;
def_hashmap_size_int = (\ _ -> nat_of_integer (16 :: Integer));

class Hashable a where {
  hashcode :: a -> Uint32.Word32;
  def_hashmap_size :: Itself a -> Nat;
};

uint32_of_int :: Int -> Uint32.Word32;
uint32_of_int i = (Prelude.fromInteger (integer_of_int i) :: Uint32.Word32);

hashcode_int :: Int -> Uint32.Word32;
hashcode_int i = uint32_of_int i;

instance Hashable Int where {
  hashcode = hashcode_int;
  def_hashmap_size = def_hashmap_size_int;
};

class (Order a) => Linorder a where {
};

instance Linorder Int where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Group_add a) => Ab_group_add a where {
};

instance Ab_semigroup_add Int where {
};

instance Cancel_ab_semigroup_add Int where {
};

instance Comm_monoid_add Int where {
};

instance Cancel_comm_monoid_add Int where {
};

instance Ab_group_add Int where {
};

class (Ab_semigroup_add a, Order a) => Ordered_ab_semigroup_add a where {
};

class (Ordered_ab_semigroup_add a) => Strict_ordered_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Strict_ordered_ab_semigroup_add a) => Ordered_cancel_ab_semigroup_add a where {
};

class (Ordered_cancel_ab_semigroup_add a) => Ordered_ab_semigroup_add_imp_le a where {
};

class (Comm_monoid_add a,
        Strict_ordered_ab_semigroup_add a) => Strict_ordered_comm_monoid_add a where {
};

class (Comm_monoid_add a,
        Ordered_ab_semigroup_add a) => Ordered_comm_monoid_add a where {
};

class (Ordered_cancel_ab_semigroup_add a, Ordered_comm_monoid_add a,
        Strict_ordered_comm_monoid_add a) => Ordered_cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Ordered_ab_semigroup_add_imp_le a,
        Ordered_cancel_comm_monoid_add a) => Ordered_ab_semigroup_monoid_add_imp_le a where {
};

class (Ab_group_add a,
        Ordered_ab_semigroup_monoid_add_imp_le a) => Ordered_ab_group_add a where {
};

instance Ordered_ab_semigroup_add Int where {
};

instance Strict_ordered_ab_semigroup_add Int where {
};

instance Ordered_cancel_ab_semigroup_add Int where {
};

instance Ordered_ab_semigroup_add_imp_le Int where {
};

instance Strict_ordered_comm_monoid_add Int where {
};

instance Ordered_comm_monoid_add Int where {
};

instance Ordered_cancel_comm_monoid_add Int where {
};

instance Ordered_ab_semigroup_monoid_add_imp_le Int where {
};

instance Ordered_ab_group_add Int where {
};

class (Ordered_ab_semigroup_add a,
        Linorder a) => Linordered_ab_semigroup_add a where {
};

class (Linordered_ab_semigroup_add a,
        Ordered_ab_semigroup_add_imp_le a) => Linordered_cancel_ab_semigroup_add a where {
};

class (Linordered_ab_semigroup_add a,
        Ordered_comm_monoid_add a) => Linordered_ab_monoid_add a where {
};

class (Linordered_ab_monoid_add a,
        Linordered_cancel_ab_semigroup_add a) => Linordered_cancel_ab_monoid_add a where {
};

class (Linordered_cancel_ab_monoid_add a,
        Ordered_ab_group_add a) => Linordered_ab_group_add a where {
};

instance Linordered_ab_semigroup_add Int where {
};

instance Linordered_cancel_ab_semigroup_add Int where {
};

instance Linordered_ab_monoid_add Int where {
};

instance Linordered_cancel_ab_monoid_add Int where {
};

instance Linordered_ab_group_add Int where {
};

instance Eq Nat where {
  a == b = equal_nat a b;
};

typerep_nat :: Itself Nat -> Typerepa;
typerep_nat t = Typerep "Nat.nat" [];

instance Countable Nat where {
};

instance Typerep Nat where {
  typerep = typerep_nat;
};

instance Heapa Nat where {
};

shows_prec_nat :: Nat -> Nat -> [Char] -> [Char];
shows_prec_nat = showsp_nat;

shows_list_nat :: [Nat] -> [Char] -> [Char];
shows_list_nat = showsp_list shows_prec_nat zero_nat;

instance Showa Nat where {
  shows_prec = shows_prec_nat;
  shows_list = shows_list_nat;
};

class One a where {
  one :: a;
};

instance One Nat where {
  one = one_nat;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

instance Plus Nat where {
  plus = plus_nat;
};

instance Zero Nat where {
  zero = zero_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

instance Preorder Nat where {
};

instance Order Nat where {
};

instance Semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

def_hashmap_size_nat :: Itself Nat -> Nat;
def_hashmap_size_nat = (\ _ -> nat_of_integer (16 :: Integer));

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

hashcode_nat :: Nat -> Uint32.Word32;
hashcode_nat n = uint32_of_int (int_of_nat n);

instance Hashable Nat where {
  hashcode = hashcode_nat;
  def_hashmap_size = def_hashmap_size_nat;
};

instance Linorder Nat where {
};

less_eq_bool :: Bool -> Bool -> Bool;
less_eq_bool True b = b;
less_eq_bool False b = True;

less_bool :: Bool -> Bool -> Bool;
less_bool True b = False;
less_bool False b = b;

instance Ord Bool where {
  less_eq = less_eq_bool;
  less = less_bool;
};

typerep_list :: forall a. (Typerep a) => Itself [a] -> Typerepa;
typerep_list t = Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type];

instance (Countable a) => Countable [a] where {
};

instance (Typerep a) => Typerep [a] where {
  typerep = typerep_list;
};

instance (Heapa a) => Heapa [a] where {
};

shows_prec_list :: forall a. (Showa a) => Nat -> [a] -> [Char] -> [Char];
shows_prec_list p xs = shows_list xs;

shows_list_list :: forall a. (Showa a) => [[a]] -> [Char] -> [Char];
shows_list_list xss = showsp_list shows_prec_list zero_nat xss;

instance (Showa a) => Showa [a] where {
  shows_prec = shows_prec_list;
  shows_list = shows_list_list;
};

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

def_hashmap_size_list :: forall a. (Hashable a) => Itself [a] -> Nat;
def_hashmap_size_list =
  (\ _ ->
    times_nat (nat_of_integer (2 :: Integer))
      ((def_hashmap_size :: Itself a -> Nat) Type));

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

hashcode_list :: forall a. (Hashable a) => [a] -> Uint32.Word32;
hashcode_list =
  foldl (\ h x ->
          h * (Prelude.fromInteger (33 :: Integer) :: Uint32.Word32) +
            hashcode x)
    ((Prelude.fromInteger (5381 :: Integer) :: Uint32.Word32));

instance (Hashable a) => Hashable [a] where {
  hashcode = hashcode_list;
  def_hashmap_size = def_hashmap_size_list;
};

typerep_array ::
  forall a. (Typerep a) => Itself (Heap.STArray Heap.RealWorld a) -> Typerepa;
typerep_array t = Typerep "Heap.array" [(typerep :: Itself a -> Typerepa) Type];

instance Countable (Heap.STArray Heap.RealWorld a) where {
};

instance (Typerep a) => Typerep (Heap.STArray Heap.RealWorld a) where {
  typerep = typerep_array;
};

instance (Typerep a) => Heapa (Heap.STArray Heap.RealWorld a) where {
};

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2 x3 x4 x5 x6 x7 x8) (Char y1 y2 y3 y4 y5 y6 y7 y8) =
  x1 == y1 &&
    x2 == y2 &&
      x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7 && x8 == y8;

instance Eq Char where {
  a == b = equal_char a b;
};

shows_prec_char :: Nat -> Char -> [Char] -> [Char];
shows_prec_char p c = (\ a -> c : a);

shows_list_char :: [Char] -> [Char] -> [Char];
shows_list_char cs = shows_string cs;

instance Showa Char where {
  shows_prec = shows_prec_char;
  shows_list = shows_list_char;
};

lexordp_eq :: forall a. (Ord a) => [a] -> [a] -> Bool;
lexordp_eq (x : xs) (y : ys) = less x y || not (less y x) && lexordp_eq xs ys;
lexordp_eq (x : xs) [] = False;
lexordp_eq xs [] = null xs;
lexordp_eq [] ys = True;

less_eq_char :: Char -> Char -> Bool;
less_eq_char (Char b0 b1 b2 b3 b4 b5 b6 b7) (Char c0 c1 c2 c3 c4 c5 c6 c7) =
  lexordp_eq [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0];

lexordp :: forall a. (Ord a) => [a] -> [a] -> Bool;
lexordp (x : xs) (y : ys) = less x y || not (less y x) && lexordp xs ys;
lexordp xs [] = False;
lexordp [] ys = not (null ys);

less_char :: Char -> Char -> Bool;
less_char (Char b0 b1 b2 b3 b4 b5 b6 b7) (Char c0 c1 c2 c3 c4 c5 c6 c7) =
  lexordp [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0];

instance Ord Char where {
  less_eq = less_eq_char;
  less = less_char;
};

instance Preorder Char where {
};

instance Order Char where {
};

instance Linorder Char where {
};

data DBMEntry a = Le a | Lt a | INF;

typerep_DBMEntry :: forall a. (Typerep a) => Itself (DBMEntry a) -> Typerepa;
typerep_DBMEntry t =
  Typerep "DBM.DBMEntry" [(typerep :: Itself a -> Typerepa) Type];

instance (Countable a) => Countable (DBMEntry a) where {
};

instance (Typerep a) => Typerep (DBMEntry a) where {
  typerep = typerep_DBMEntry;
};

instance (Heapa a) => Heapa (DBMEntry a) where {
};

dbm_add ::
  forall a.
    (Linordered_cancel_ab_semigroup_add a) => DBMEntry a ->
        DBMEntry a -> DBMEntry a;
dbm_add INF uu = INF;
dbm_add (Le v) INF = INF;
dbm_add (Lt v) INF = INF;
dbm_add (Le a) (Le b) = Le (plus a b);
dbm_add (Le a) (Lt b) = Lt (plus a b);
dbm_add (Lt a) (Le b) = Lt (plus a b);
dbm_add (Lt a) (Lt b) = Lt (plus a b);

plus_DBMEntry ::
  forall a.
    (Linordered_cancel_ab_monoid_add a) => DBMEntry a ->
     DBMEntry a -> DBMEntry a;
plus_DBMEntry = dbm_add;

instance (Linordered_cancel_ab_monoid_add a) => Plus (DBMEntry a) where {
  plus = plus_DBMEntry;
};

zero_DBMEntry :: forall a. (Zero a) => DBMEntry a;
zero_DBMEntry = Le zero;

instance (Zero a) => Zero (DBMEntry a) where {
  zero = zero_DBMEntry;
};

equal_DBMEntry :: forall a. (Eq a) => DBMEntry a -> DBMEntry a -> Bool;
equal_DBMEntry (Lt x2) INF = False;
equal_DBMEntry INF (Lt x2) = False;
equal_DBMEntry (Le x1) INF = False;
equal_DBMEntry INF (Le x1) = False;
equal_DBMEntry (Le x1) (Lt x2) = False;
equal_DBMEntry (Lt x2) (Le x1) = False;
equal_DBMEntry (Lt x2) (Lt y2) = x2 == y2;
equal_DBMEntry (Le x1) (Le y1) = x1 == y1;
equal_DBMEntry INF INF = True;

dbm_lt :: forall a. (Linorder a) => DBMEntry a -> DBMEntry a -> Bool;
dbm_lt INF x = False;
dbm_lt (Lt a) (Lt b) = less a b;
dbm_lt (Lt a) (Le b) = less_eq a b;
dbm_lt (Le a) (Lt b) = less a b;
dbm_lt (Le a) (Le b) = less a b;
dbm_lt (Le a) INF = True;
dbm_lt (Lt a) INF = True;

dbm_le :: forall a. (Eq a, Linorder a) => DBMEntry a -> DBMEntry a -> Bool;
dbm_le a b = equal_DBMEntry a b || dbm_lt a b;

less_eq_DBMEntry ::
  forall a. (Eq a, Linorder a) => DBMEntry a -> DBMEntry a -> Bool;
less_eq_DBMEntry = dbm_le;

less_DBMEntry :: forall a. (Linorder a) => DBMEntry a -> DBMEntry a -> Bool;
less_DBMEntry = dbm_lt;

instance (Eq a, Linorder a) => Ord (DBMEntry a) where {
  less_eq = less_eq_DBMEntry;
  less = less_DBMEntry;
};

instance (Eq a, Linorder a) => Preorder (DBMEntry a) where {
};

instance (Eq a, Linorder a) => Order (DBMEntry a) where {
};

instance (Linordered_cancel_ab_monoid_add a) => Semigroup_add (DBMEntry
                        a) where {
};

instance (Linordered_cancel_ab_monoid_add a) => Monoid_add (DBMEntry a) where {
};

instance (Eq a, Linorder a) => Linorder (DBMEntry a) where {
};

instance (Linordered_cancel_ab_monoid_add a) => Ab_semigroup_add (DBMEntry
                           a) where {
};

instance (Linordered_cancel_ab_monoid_add a) => Comm_monoid_add (DBMEntry
                          a) where {
};

instance (Linordered_cancel_ab_monoid_add a,
           Eq a) => Ordered_ab_semigroup_add (DBMEntry a) where {
};

instance (Linordered_cancel_ab_monoid_add a,
           Eq a) => Ordered_comm_monoid_add (DBMEntry a) where {
};

instance (Linordered_cancel_ab_monoid_add a,
           Eq a) => Linordered_ab_semigroup_add (DBMEntry a) where {
};

instance (Linordered_cancel_ab_monoid_add a,
           Eq a) => Linordered_ab_monoid_add (DBMEntry a) where {
};

shows_space :: [Char] -> [Char];
shows_space =
  shows_prec_char zero_nat
    (Char False False False False False True False False);

data Act a = In a | Out a | Sil a;

shows_pr :: Nat -> [Char] -> [Char];
shows_pr p =
  (if less_nat zero_nat p
    then shows_prec_char zero_nat
           (Char True False False True False True False False)
    else id);

shows_pl :: Nat -> [Char] -> [Char];
shows_pl p =
  (if less_nat zero_nat p
    then shows_prec_char zero_nat
           (Char False False False True False True False False)
    else id);

showsp_act ::
  forall a. (Nat -> a -> [Char] -> [Char]) -> Nat -> Act a -> [Char] -> [Char];
showsp_act show_a p (Sil x) =
  (((shows_pl p .
      shows_string
        [Char True True False False True False True False,
          Char True False False True False True True False,
          Char False False True True False True True False]) .
     shows_space) .
    show_a one_nat x) .
    shows_pr p;
showsp_act show_a p (Out x) =
  (((shows_pl p .
      shows_string
        [Char True True True True False False True False,
          Char True False True False True True True False,
          Char False False True False True True True False]) .
     shows_space) .
    show_a one_nat x) .
    shows_pr p;
showsp_act show_a p (In x) =
  (((shows_pl p .
      shows_string
        [Char True False False True False False True False,
          Char False True True True False True True False]) .
     shows_space) .
    show_a one_nat x) .
    shows_pr p;

shows_prec_act :: forall a. (Showa a) => Nat -> Act a -> [Char] -> [Char];
shows_prec_act = showsp_act shows_prec;

shows_list_act :: forall a. (Showa a) => [Act a] -> [Char] -> [Char];
shows_list_act = showsp_list shows_prec_act zero_nat;

instance (Showa a) => Showa (Act a) where {
  shows_prec = shows_prec_act;
  shows_list = shows_list_act;
};

bit_cut_integer :: Integer -> (Integer, Bool);
bit_cut_integer k =
  (if k == (0 :: Integer) then ((0 :: Integer), False)
    else (case divMod (abs k) (abs (2 :: Integer)) of {
           (r, s) ->
             ((if (0 :: Integer) < k then r else negate r - s),
               s == (1 :: Integer));
         }));

char_of_integer :: Integer -> Char;
char_of_integer k =
  (case bit_cut_integer k of {
    (q0, b0) ->
      (case bit_cut_integer q0 of {
        (q1, b1) ->
          (case bit_cut_integer q1 of {
            (q2, b2) ->
              (case bit_cut_integer q2 of {
                (q3, b3) ->
                  (case bit_cut_integer q3 of {
                    (q4, b4) ->
                      (case bit_cut_integer q4 of {
                        (q5, b5) ->
                          (case bit_cut_integer q5 of {
                            (q6, b6) ->
                              (case bit_cut_integer q6 of {
                                (_, a) -> Char b0 b1 b2 b3 b4 b5 b6 a;
                              });
                          });
                      });
                  });
              });
          });
      });
  });

explode :: String -> [Char];
explode s =
  map char_of_integer
    (map (let ord k | (k < 128) = Prelude.toInteger k in ord . (Prelude.fromEnum :: Prelude.Char -> Prelude.Int))
      s);

shows_prec_literal :: Nat -> String -> [Char] -> [Char];
shows_prec_literal p s = shows_string (explode s);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

shows_list_literal :: [String] -> [Char] -> [Char];
shows_list_literal = foldr (\ s -> shows_string (explode s));

instance Showa String where {
  shows_prec = shows_prec_literal;
  shows_list = shows_list_literal;
};

instance Countable String where {
};

typerep_prod :: forall a b. (Typerep a, Typerep b) => Itself (a, b) -> Typerepa;
typerep_prod t =
  Typerep "Product_Type.prod"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

instance (Countable a, Countable b) => Countable (a, b) where {
};

instance (Typerep a, Typerep b) => Typerep (a, b) where {
  typerep = typerep_prod;
};

instance (Heapa a, Heapa b) => Heapa (a, b) where {
};

showsp_prod ::
  forall a b.
    (Nat -> a -> [Char] -> [Char]) ->
      (Nat -> b -> [Char] -> [Char]) -> Nat -> (a, b) -> [Char] -> [Char];
showsp_prod s1 s2 p (x, y) =
  (((shows_string [Char False False False True False True False False] .
      s1 one_nat x) .
     shows_string
       [Char False False True True False True False False,
         Char False False False False False True False False]) .
    s2 one_nat y) .
    shows_string [Char True False False True False True False False];

shows_prec_prod ::
  forall a b. (Showa a, Showa b) => Nat -> (a, b) -> [Char] -> [Char];
shows_prec_prod = showsp_prod shows_prec shows_prec;

shows_list_prod ::
  forall a b. (Showa a, Showa b) => [(a, b)] -> [Char] -> [Char];
shows_list_prod = showsp_list shows_prec_prod zero_nat;

instance (Showa a, Showa b) => Showa (a, b) where {
  shows_prec = shows_prec_prod;
  shows_list = shows_list_prod;
};

def_hashmap_size_prod ::
  forall a b. (Hashable a, Hashable b) => Itself (a, b) -> Nat;
def_hashmap_size_prod =
  (\ _ ->
    plus_nat ((def_hashmap_size :: Itself a -> Nat) Type)
      ((def_hashmap_size :: Itself b -> Nat) Type));

hashcode_prod ::
  forall a b. (Hashable a, Hashable b) => (a, b) -> Uint32.Word32;
hashcode_prod x =
  hashcode (fst x) * (Prelude.fromInteger (33 :: Integer) :: Uint32.Word32) +
    hashcode (snd x);

instance (Hashable a, Hashable b) => Hashable (a, b) where {
  hashcode = hashcode_prod;
  def_hashmap_size = def_hashmap_size_prod;
};

one_integer :: Integer;
one_integer = (1 :: Integer);

instance One Integer where {
  one = one_integer;
};

instance Zero Integer where {
  zero = (0 :: Integer);
};

class (One a, Zero a) => Zero_neq_one a where {
};

instance Zero_neq_one Integer where {
};

data Bexp a b = Truea | Not (Bexp a b) | And (Bexp a b) (Bexp a b)
  | Or (Bexp a b) (Bexp a b) | Imply (Bexp a b) (Bexp a b)
  | Eqa (Exp a b) (Exp a b) | Lea (Exp a b) (Exp a b) | Lta (Exp a b) (Exp a b)
  | Ge (Exp a b) (Exp a b) | Gt (Exp a b) (Exp a b);

data Exp a b = Const b | Var a | If_then_else (Bexp a b) (Exp a b) (Exp a b)
  | Binop (b -> b -> b) (Exp a b) (Exp a b) | Unop (b -> b) (Exp a b);

shows_exp :: forall a b. (Showa a, Showa b) => Exp a b -> [Char];
shows_exp (Const c) = shows_prec zero_nat c [];
shows_exp (Var v) = shows_prec zero_nat v [];
shows_exp (If_then_else b e1 e2) =
  shows_bexp b ++
    [Char False False False False False True False False,
      Char True True True True True True False False,
      Char False False False False False True False False] ++
      shows_exp e1 ++
        [Char False False False False False True False False,
          Char False True False True True True False False,
          Char False False False False False True False False] ++
          shows_exp e2;
shows_exp (Binop uu e1 e2) =
  [Char False True False False False True True False,
    Char True False False True False True True False,
    Char False True True True False True True False,
    Char True True True True False True True False,
    Char False False False False True True True False,
    Char False False False False False True False False] ++
    shows_exp e1 ++
      [Char False False False False False True False False] ++ shows_exp e2;
shows_exp (Unop uv e) =
  [Char True False True False True True True False,
    Char False True True True False True True False,
    Char True True True True False True True False,
    Char False False False False True True True False,
    Char False False False False False True False False] ++
    shows_exp e;

shows_bexp :: forall a b. (Showa a, Showa b) => Bexp a b -> [Char];
shows_bexp (Lta a b) =
  shows_exp a ++
    [Char False False False False False True False False,
      Char False False True True True True False False,
      Char False False False False False True False False] ++
      shows_exp b;
shows_bexp (Lea a b) =
  shows_exp a ++
    [Char False False False False False True False False,
      Char False False True True True True False False,
      Char True False True True True True False False,
      Char False False False False False True False False] ++
      shows_exp b;
shows_bexp (Eqa a b) =
  shows_exp a ++
    [Char False False False False False True False False,
      Char True False True True True True False False,
      Char False False False False False True False False] ++
      shows_exp b;
shows_bexp (Ge a b) =
  shows_exp a ++
    [Char False False False False False True False False,
      Char False True True True True True False False,
      Char True False True True True True False False,
      Char False False False False False True False False] ++
      shows_exp b;
shows_bexp (Gt a b) =
  shows_exp a ++
    [Char False False False False False True False False,
      Char False True True True True True False False,
      Char False False False False False True False False] ++
      shows_exp b;
shows_bexp Truea =
  [Char False False True False True True True False,
    Char False True False False True True True False,
    Char True False True False True True True False,
    Char True False True False False True True False];
shows_bexp (Not b) =
  [Char True False False False False True False False,
    Char False False False False False True False False] ++
    shows_bexp b;
shows_bexp (And a b) =
  shows_bexp a ++
    [Char False False False False False True False False,
      Char False True True False False True False False,
      Char False True True False False True False False,
      Char False False False False False True False False] ++
      shows_bexp b;
shows_bexp (Or a b) =
  shows_bexp a ++
    [Char False False False False False True False False,
      Char False False True True True True True False,
      Char False False True True True True True False,
      Char False False False False False True False False] ++
      shows_bexp b;
shows_bexp (Imply a b) =
  shows_bexp a ++
    [Char False False False False False True False False,
      Char True False True True False True False False,
      Char False True True True True True False False,
      Char False False False False False True False False] ++
      shows_bexp b;

shows_prec_exp ::
  forall a b. (Showa a, Showa b) => Nat -> Exp a b -> [Char] -> [Char];
shows_prec_exp p e rest = shows_exp e ++ rest;

intersperse :: forall a. a -> [a] -> [a];
intersperse sep (x : y : xs) = x : sep : intersperse sep (y : xs);
intersperse uu [] = [];
intersperse uu [v] = [v];

shows_list_exp ::
  forall a b. (Showa a, Showa b) => [Exp a b] -> [Char] -> [Char];
shows_list_exp es s =
  [Char True True False True True False True False] ++
    concat
      (intersperse
        [Char False False True True False True False False,
          Char False False False False False True False False]
        (map shows_exp es)) ++
      [Char True False True True True False True False] ++ s;

instance (Showa a, Showa b) => Showa (Exp a b) where {
  shows_prec = shows_prec_exp;
  shows_list = shows_list_exp;
};

shows_prec_bexp ::
  forall a b. (Showa a, Showa b) => Nat -> Bexp a b -> [Char] -> [Char];
shows_prec_bexp p e rest = shows_bexp e ++ rest;

shows_list_bexp ::
  forall a b. (Showa a, Showa b) => [Bexp a b] -> [Char] -> [Char];
shows_list_bexp es s =
  [Char True True False True True False True False] ++
    concat
      (intersperse
        [Char False False True True False True False False,
          Char False False False False False True False False]
        (map shows_bexp es)) ++
      [Char True False True True True False True False] ++ s;

instance (Showa a, Showa b) => Showa (Bexp a b) where {
  shows_prec = shows_prec_bexp;
  shows_list = shows_list_bexp;
};

data Acconstraint a b = LT a b | LE a b | EQ a b | GT a b | GE a b;

showsp_acconstraint ::
  forall a b.
    (Nat -> a -> [Char] -> [Char]) ->
      (Nat -> b -> [Char] -> [Char]) ->
        Nat -> Acconstraint a b -> [Char] -> [Char];
showsp_acconstraint show_c show_t p (GE x y) =
  (((((shows_pl p .
        shows_string
          [Char True True True False False False True False,
            Char True False True False False False True False]) .
       shows_space) .
      show_c one_nat x) .
     shows_space) .
    show_t one_nat y) .
    shows_pr p;
showsp_acconstraint show_c show_t p (GT x y) =
  (((((shows_pl p .
        shows_string
          [Char True True True False False False True False,
            Char False False True False True False True False]) .
       shows_space) .
      show_c one_nat x) .
     shows_space) .
    show_t one_nat y) .
    shows_pr p;
showsp_acconstraint show_c show_t p (EQ x y) =
  (((((shows_pl p .
        shows_string
          [Char True False True False False False True False,
            Char True False False False True False True False]) .
       shows_space) .
      show_c one_nat x) .
     shows_space) .
    show_t one_nat y) .
    shows_pr p;
showsp_acconstraint show_c show_t p (LE x y) =
  (((((shows_pl p .
        shows_string
          [Char False False True True False False True False,
            Char True False True False False False True False]) .
       shows_space) .
      show_c one_nat x) .
     shows_space) .
    show_t one_nat y) .
    shows_pr p;
showsp_acconstraint show_c show_t p (LT x y) =
  (((((shows_pl p .
        shows_string
          [Char False False True True False False True False,
            Char False False True False True False True False]) .
       shows_space) .
      show_c one_nat x) .
     shows_space) .
    show_t one_nat y) .
    shows_pr p;

shows_prec_acconstraint ::
  forall a b. (Showa a, Showa b) => Nat -> Acconstraint a b -> [Char] -> [Char];
shows_prec_acconstraint = showsp_acconstraint shows_prec shows_prec;

shows_list_acconstraint ::
  forall a b. (Showa a, Showa b) => [Acconstraint a b] -> [Char] -> [Char];
shows_list_acconstraint = showsp_list shows_prec_acconstraint zero_nat;

instance (Showa a, Showa b) => Showa (Acconstraint a b) where {
  shows_prec = shows_prec_acconstraint;
  shows_list = shows_list_acconstraint;
};

data Set a = Set [a] | Coset [a];

data Sum a b = Inl a | Inr b;

data Message = ExploredState;

data Fract = Rata Bool Int Int;

data JSON = Object [([Char], JSON)] | Arraya [JSON] | Stringa [Char] | Int Int
  | Nata Nat | Rat Fract | Boolean Bool | Null;

data Heap_ext a =
  Heap_ext (Typerepa -> Nat -> [Nat]) (Typerepa -> Nat -> Nat) Nat a;

data Hashtable a b = HashTable (Heap.STArray Heap.RealWorld [(a, b)]) Nat;

data Result a = Result a | Error [String];

data Len_list a = LL Nat [a];

data Hashmap a b = HashMap (Array.ArrayType [(a, b)]) Nat;

data Label a = Del | Internal a | Bin a | Broad a;

data Gen_g_impl_ext a b c d = Gen_g_impl_ext a b c d;

data Resulta = Renaming_Failed | Preconds_Unsat | Sat | Unsat;

data Sexp a b c d = Trueb | Nota (Sexp a b c d)
  | Anda (Sexp a b c d) (Sexp a b c d) | Ora (Sexp a b c d) (Sexp a b c d)
  | Implya (Sexp a b c d) (Sexp a b c d) | Eqb c d | Leb c d | Ltb c d | Gea c d
  | Gta c d | Loc a b;

data Mode = Impl1 | Impl2 | Impl3 | Buechi | Debug;

data Formula a b c d = EX (Sexp a b c d) | EG (Sexp a b c d) | AX (Sexp a b c d)
  | AG (Sexp a b c d) | Leadsto (Sexp a b c d) (Sexp a b c d);

data State_space a = Reachable_Set [(([a], [Int]), [[DBMEntry Int]])]
  | Buechi_Set [(([a], [Int]), [([DBMEntry Int], Nat)])];

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex (Set xs) p = any p xs;

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

len ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a -> Heap.ST Heap.RealWorld Nat;
len a = do { 
          i <- Heap.lengthArray a;
          return (nat_of_integer i)
         };

new ::
  forall a.
    (Heapa a) => Nat ->
                   a -> Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
new = Heap.newArray . integer_of_nat;

ntha ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Nat -> Heap.ST Heap.RealWorld a;
ntha a n = Heap.readArray a (integer_of_nat n);

upd ::
  forall a.
    (Heapa a) => Nat ->
                   a -> Heap.STArray Heap.RealWorld a ->
                          Heap.ST Heap.RealWorld
                            (Heap.STArray Heap.RealWorld a);
upd i x a = do { 
              _ <- Heap.writeArray a (integer_of_nat i) x;
              return a
             };

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if equal_nat n zero_nat then [] else x : take (minus_nat n one_nat) xs);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

make ::
  forall a.
    (Heapa a) => Nat ->
                   (Nat -> a) ->
                     Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
make n f = Heap.newFunArray (integer_of_nat n) (f . nat_of_integer);

inj_on :: forall a b. (Eq a, Eq b) => (a -> b) -> Set a -> Bool;
inj_on f a =
  ball a (\ x -> ball a (\ y -> (if f x == f y then x == y else True)));

empty :: Heap_ext ();
empty = Heap_ext (\ _ _ -> []) (\ _ _ -> zero_nat) zero_nat ();

sub :: forall a. IArray.IArray a -> Nat -> a;
sub asa n = IArray.sub (asa, integer_of_nat n);

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);
map_of [] k = Nothing;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (inserta x xs);
remove x (Set xs) = Set (removeAll x xs);

fun_upd :: forall a b. (Eq a) => (a -> b) -> a -> b -> a -> b;
fun_upd f a b = (\ x -> (if x == a then b else f x));

ll_fuel :: forall a. Len_list a -> Nat;
ll_fuel (LL x1 x2) = x1;

bind :: forall a b c. Sum a b -> (b -> Sum a c) -> Sum a c;
bind m f = (case m of {
             Inl a -> Inl a;
             Inr a -> f a;
           });

ensure_cparser ::
  forall a b.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a)) ->
      Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a);
ensure_cparser p =
  (\ ts ->
    bind (p ts)
      (\ (x, tsa) ->
        (if less_nat (ll_fuel tsa) (ll_fuel ts) then Inr (x, tsa)
          else Inl (\ _ ->
                     shows_prec_list zero_nat
                       [Char False False True False False False True False,
                         Char True False False True True True True False,
                         Char False True True True False True True False,
                         Char True False False False False True True False,
                         Char True False True True False True True False,
                         Char True False False True False True True False,
                         Char True True False False False True True False,
                         Char False False False False False True False False,
                         Char False False False False True True True False,
                         Char True False False False False True True False,
                         Char False True False False True True True False,
                         Char True True False False True True True False,
                         Char True False True False False True True False,
                         Char False True False False True True True False,
                         Char False False False False False True False False,
                         Char True True False False False True True False,
                         Char False False False True False True True False,
                         Char True False True False False True True False,
                         Char True True False False False True True False,
                         Char True True False True False True True False,
                         Char False False False False False True False False,
                         Char False True True False False True True False,
                         Char True False False False False True True False,
                         Char True False False True False True True False,
                         Char False False True True False True True False,
                         Char True False True False False True True False,
                         Char False False True False False True True False]))));

sum_join :: forall a. Sum a a -> a;
sum_join (Inl x) = x;
sum_join (Inr x) = x;

returna ::
  forall a b. a -> Len_list b -> Sum (() -> [Char] -> [Char]) (a, Len_list b);
returna x = (\ ts -> Inr (x, ts));

ensure_parser ::
  forall a b.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a)) ->
      Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a);
ensure_parser p =
  (\ ts ->
    bind (p ts)
      (\ (x, tsa) ->
        (if less_eq_nat (ll_fuel tsa) (ll_fuel ts) then Inr (x, tsa)
          else Inl (\ _ ->
                     shows_prec_list zero_nat
                       [Char False False True False False False True False,
                         Char True False False True True True True False,
                         Char False True True True False True True False,
                         Char True False False False False True True False,
                         Char True False True True False True True False,
                         Char True False False True False True True False,
                         Char True True False False False True True False,
                         Char False False False False False True False False,
                         Char False False False False True True True False,
                         Char True False False False False True True False,
                         Char False True False False True True True False,
                         Char True True False False True True True False,
                         Char True False True False False True True False,
                         Char False True False False True True True False,
                         Char False False False False False True False False,
                         Char True True False False False True True False,
                         Char False False False True False True True False,
                         Char True False True False False True True False,
                         Char True True False False False True True False,
                         Char True True False True False True True False,
                         Char False False False False False True False False,
                         Char False True True False False True True False,
                         Char True False False False False True True False,
                         Char True False False True False True True False,
                         Char False False True True False True True False,
                         Char True False True False False True True False,
                         Char False False True False False True True False]))));

bindb ::
  forall a b c.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a)) ->
      (b -> Len_list a -> Sum (() -> [Char] -> [Char]) (c, Len_list a)) ->
        Len_list a -> Sum (() -> [Char] -> [Char]) (c, Len_list a);
bindb m f =
  (\ ts -> bind (ensure_parser m ts) (\ (x, a) -> ensure_parser (f x) a));

catch_error :: forall a b c. Sum a b -> (a -> Sum c b) -> Sum c b;
catch_error m f = (case m of {
                    Inl a -> f a;
                    Inr a -> Inr a;
                  });

alt ::
  forall a b c d.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list c)) ->
      (Len_list a -> Sum (() -> [Char] -> [Char]) (d, Len_list c)) ->
        Len_list a -> Sum (() -> [Char] -> [Char]) (Sum b d, Len_list c);
alt p1 p2 l =
  catch_error (bind (p1 l) (\ (r, la) -> Inr (Inl r, la)))
    (\ e1 ->
      catch_error (bind (p2 l) (\ (r, la) -> Inr (Inr r, la)))
        (\ e2 ->
          Inl (\ _ ->
                (e1 () .
                  shows_prec_list zero_nat
                    [Char False True False True False False False False,
                      Char False False False False False True False False,
                      Char False False False False False True False False,
                      Char False False True True True True True False,
                      Char False False False False False True False False]) .
                  e2 ())));

repeat ::
  forall a b.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a)) ->
      Len_list a -> Sum (() -> [Char] -> [Char]) ([b], Len_list a);
repeat p l =
  bindb (alt (bindb (ensure_cparser p)
               (\ a -> bindb (repeat p) (\ b -> returna (a : b))))
          (returna []))
    (\ x -> returna (sum_join x)) l;

ll_list :: forall a. Len_list a -> [a];
ll_list (LL x1 x2) = x2;

get_tokens ::
  forall a. Len_list a -> Sum (() -> [Char] -> [Char]) ([a], Len_list a);
get_tokens = (\ ll -> Inr (ll_list ll, ll));

error_aux ::
  forall a b.
    (() -> [Char] -> [Char]) ->
      Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a);
error_aux e = (\ _ -> Inl e);

shows_quote :: ([Char] -> [Char]) -> [Char] -> [Char];
shows_quote s =
  (shows_prec_char zero_nat (Char True True True False False True False False) .
    s) .
    shows_prec_char zero_nat (Char True True True False False True False False);

err_expecting_aux ::
  forall a b.
    (Showa a) => (() -> [Char] -> [Char]) ->
                   Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a);
err_expecting_aux msg =
  bindb get_tokens
    (\ ts ->
      error_aux
        (\ _ ->
          ((shows_string
              [Char True False True False False True True False,
                Char False False False True True True True False,
                Char False False False False True True True False,
                Char True False True False False True True False,
                Char True True False False False True True False,
                Char False False True False True True True False,
                Char True False False True False True True False,
                Char False True True True False True True False,
                Char True True True False False True True False,
                Char False False False False False True False False] .
             msg ()) .
            shows_string
              [Char False False True True False True False False,
                Char False False False False False True False False,
                Char False True False False False True True False,
                Char True False True False True True True False,
                Char False False True False True True True False,
                Char False False False False False True False False,
                Char False True True False False True True False,
                Char True True True True False True True False,
                Char True False True False True True True False,
                Char False True True True False True True False,
                Char False False True False False True True False,
                Char False True False True True True False False,
                Char False False False False False True False False]) .
            shows_quote
              (shows_prec_list zero_nat
                (take (nat_of_integer (100 :: Integer)) ts))));

get :: forall a. Len_list a -> Sum (() -> [Char] -> [Char]) (a, Len_list a);
get ll =
  (case ll of {
    LL nat list ->
      (if equal_nat nat zero_nat
        then Inl (\ _ ->
                   shows_string
                     [Char True False True False False False True False,
                       Char False False False True True True True False,
                       Char False False False False True True True False,
                       Char True False True False False True True False,
                       Char True True False False False True True False,
                       Char False False True False True True True False,
                       Char True False False True False True True False,
                       Char False True True True False True True False,
                       Char True True True False False True True False,
                       Char False False False False False True False False,
                       Char True False True True False True True False,
                       Char True True True True False True True False,
                       Char False True False False True True True False,
                       Char True False True False False True True False,
                       Char False False False False False True False False,
                       Char True False False True False True True False,
                       Char False True True True False True True False,
                       Char False False False False True True True False,
                       Char True False True False True True True False,
                       Char False False True False True True True False])
        else (case list of {
               [] -> Inl (\ _ ->
                           shows_string
                             [Char True False True False False False True False,
                               Char False False False True True True True False,
                               Char False False False False True True True
                                 False,
                               Char True False True False False True True False,
                               Char True True False False False True True False,
                               Char False False True False True True True False,
                               Char True False False True False True True False,
                               Char False True True True False True True False,
                               Char True True True False False True True False,
                               Char False False False False False True False
                                 False,
                               Char True False True True False True True False,
                               Char True True True True False True True False,
                               Char False True False False True True True False,
                               Char True False True False False True True False,
                               Char False False False False False True False
                                 False,
                               Char True False False True False True True False,
                               Char False True True True False True True False,
                               Char False False False False True True True
                                 False,
                               Char True False True False True True True False,
                               Char False False True False True True True
                                 False]);
               x : xs -> Inr (x, LL (minus_nat nat one_nat) xs);
             }));
  });

anya ::
  forall a.
    (Eq a,
      Showa a) => [a] ->
                    Len_list a -> Sum (() -> [Char] -> [Char]) (a, Len_list a);
anya ts =
  bindb get
    (\ t ->
      (if membera ts t then returna t
        else err_expecting_aux
               (\ _ ->
                 shows_string
                   [Char True True True True False False True False,
                     Char False True True True False True True False,
                     Char True False True False False True True False,
                     Char False False False False False True False False,
                     Char True True True True False True True False,
                     Char False True True False False True True False,
                     Char False False False False False True False False] .
                   shows_prec_list zero_nat ts)));

lx_ws :: Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
lx_ws =
  repeat
    (anya [Char False False False False False True False False,
            Char False True False True False False False False,
            Char True False False True False False False False,
            Char True False True True False False False False]);

fold_map ::
  forall a b.
    (a -> Heap.ST Heap.RealWorld b) -> [a] -> Heap.ST Heap.RealWorld [b];
fold_map f [] = return [];
fold_map f (x : xs) = do { 
                        y <- f x;
                        ys <- fold_map f xs;
                        return (y : ys)
                       };

freeze ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a -> Heap.ST Heap.RealWorld [a];
freeze a = do { 
             n <- len a;
             fold_map (ntha a) (upt zero_nat n)
            };

foldli :: forall a b. [a] -> (b -> Bool) -> (a -> b -> b) -> b -> b;
foldli [] c f sigma = sigma;
foldli (x : xs) c f sigma =
  (if c sigma then foldli xs c f (f x sigma) else sigma);

exactly ::
  forall a.
    (Eq a,
      Showa a) => [a] ->
                    Len_list a ->
                      Sum (() -> [Char] -> [Char]) ([a], Len_list a);
exactly ts =
  bindb (alt (foldr
               (\ t p ->
                 bindb get
                   (\ x ->
                     (if x == t then bindb p (\ xa -> returna (x : xa))
                       else error_aux (\ _ -> id))))
               ts (returna []))
          (err_expecting_aux
            (\ _ ->
              shows_string
                [Char True False True False False False True False,
                  Char False False False True True True True False,
                  Char True False False False False True True False,
                  Char True True False False False True True False,
                  Char False False True False True True True False,
                  Char False False True True False True True False,
                  Char True False False True True True True False,
                  Char False False False False False True False False] .
                shows_prec_list zero_nat ts)))
    (\ x -> returna (sum_join x));

of_bool :: forall a. (Zero_neq_one a) => Bool -> a;
of_bool True = one;
of_bool False = zero;

integer_of_char :: Char -> Integer;
integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) =
  ((((((of_bool b7 * (2 :: Integer) + of_bool b6) * (2 :: Integer) +
        of_bool b5) *
        (2 :: Integer) +
       of_bool b4) *
       (2 :: Integer) +
      of_bool b3) *
      (2 :: Integer) +
     of_bool b2) *
     (2 :: Integer) +
    of_bool b1) *
    (2 :: Integer) +
    of_bool b0;

nat_of_char :: Char -> Nat;
nat_of_char c = Nat (integer_of_char c);

range ::
  forall a.
    (Linorder a,
      Showa a) => a -> a -> Len_list a ->
                              Sum (() -> [Char] -> [Char]) (a, Len_list a);
range a b =
  bindb get
    (\ x ->
      (if less_eq a x && less_eq x b then returna x
        else err_expecting_aux
               (\ _ ->
                 ((shows_string
                     [Char False False True False True False True False,
                       Char True True True True False True True False,
                       Char True True False True False True True False,
                       Char True False True False False True True False,
                       Char False True True True False True True False,
                       Char False False False False False True False False,
                       Char True False False True False True True False,
                       Char False True True True False True True False,
                       Char False False False False False True False False,
                       Char False True False False True True True False,
                       Char True False False False False True True False,
                       Char False True True True False True True False,
                       Char True True True False False True True False,
                       Char True False True False False True True False,
                       Char False False False False False True False False] .
                    shows_prec zero_nat a) .
                   shows_string
                     [Char False False False False False True False False,
                       Char True False True True False True False False,
                       Char False False False False False True False False]) .
                   shows_prec zero_nat b)));

lx_digit :: Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
lx_digit =
  range (Char False False False False True True False False)
    (Char True False False True True True False False);

lx_nat_aux ::
  Nat -> Len_list Char -> Sum (() -> [Char] -> [Char]) (Nat, Len_list Char);
lx_nat_aux acc l =
  bindb (alt (bindb lx_digit
               (\ x ->
                 lx_nat_aux
                   (plus_nat (times_nat (nat_of_integer (10 :: Integer)) acc)
                     (minus_nat (nat_of_char x)
                       (nat_of_char
                         (Char False False False False True True False
                           False))))))
          (returna acc))
    (\ x -> returna (sum_join x)) l;

lx_nat :: Len_list Char -> Sum (() -> [Char] -> [Char]) (Nat, Len_list Char);
lx_nat =
  bindb lx_digit
    (\ x ->
      lx_nat_aux
        (minus_nat (nat_of_char x)
          (nat_of_char (Char False False False False True True False False))));

lx_int :: Len_list Char -> Sum (() -> [Char] -> [Char]) (Int, Len_list Char);
lx_int =
  bindb (alt (bindb (exactly [Char True False True True False True False False])
               (\ _ ->
                 bindb lx_nat (\ x -> returna ((uminus_int . int_of_nat) x))))
          (bindb lx_nat (\ x -> returna (int_of_nat x))))
    (\ x -> returna (sum_join x));

gen_token ::
  forall a b c.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a)) ->
      (Len_list a -> Sum (() -> [Char] -> [Char]) (c, Len_list a)) ->
        Len_list a -> Sum (() -> [Char] -> [Char]) (c, Len_list a);
gen_token ws p = bindb ws (\ _ -> p);

tk_div :: Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
tk_div =
  gen_token lx_ws (exactly [Char True True True True False True False False]);

extract :: forall a. (a -> Bool) -> [a] -> Maybe ([a], (a, [a]));
extract p (x : xs) =
  (if p x then Just ([], (x, xs))
    else (case extract p xs of {
           Nothing -> Nothing;
           Just (ys, (y, zs)) -> Just (x : ys, (y, zs));
         }));
extract p [] = Nothing;

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

uncurry :: forall a b c. (a -> b -> c) -> (a, b) -> c;
uncurry f = (\ (a, b) -> f a b);

mapa :: forall a b. (a -> b) -> [a] -> [b];
mapa = map;

tk_plus ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
tk_plus =
  gen_token lx_ws (exactly [Char True True False True False True False False]);

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (membera xs x) && distinct xs;

write_msg :: Message -> ();
write_msg m = ();

trace :: forall a. Message -> a -> a;
trace m x = let {
              _ = write_msg m;
            } in x;

tk_minus ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
tk_minus =
  gen_token lx_ws (exactly [Char True False True True False True False False]);

tk_times ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
tk_times =
  gen_token lx_ws (exactly [Char False True False True False True False False]);

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

implode :: [Char] -> String;
implode cs =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    (map integer_of_char cs);

tracea :: forall a. a -> a;
tracea = trace ExploredState;

v_dbm :: forall a b. (Zero a, Eq a, Ord a, Zero b) => a -> (a, a) -> DBMEntry b;
v_dbm n =
  (\ (i, j) ->
    (if i == j || (i == zero && less zero j || (less n i || less n j))
      then zero_DBMEntry else INF));

tk_lparen ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
tk_lparen =
  gen_token lx_ws
    (exactly [Char False False False True False True False False]);

tk_rparen ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
tk_rparen =
  gen_token lx_ws (exactly [Char True False False True False True False False]);

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

cODE_ABORT :: forall a. (() -> a) -> a;
cODE_ABORT _ = error "Misc.CODE_ABORT";

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

gen_pick ::
  forall a b c d e f.
    (a -> (Maybe b -> Bool) -> (c -> d -> Maybe c) -> Maybe e -> Maybe f) ->
      a -> f;
gen_pick it s =
  the (it s (\ a -> (case a of {
                      Nothing -> True;
                      Just _ -> False;
                    }))
         (\ x _ -> Just x)
        Nothing);

bracket_close ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
bracket_close =
  bindb lx_ws
    (\ _ -> exactly [Char True False True True True False True False]);

bracket_open ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
bracket_open =
  bindb lx_ws
    (\ _ -> exactly [Char True True False True True False True False]);

chainL1 ::
  forall a b.
    (Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a)) ->
      (Len_list a -> Sum (() -> [Char] -> [Char]) (b -> b -> b, Len_list a)) ->
        Len_list a -> Sum (() -> [Char] -> [Char]) (b, Len_list a);
chainL1 a f =
  bindb a
    (\ x ->
      bindb (repeat
              (bindb f (\ aa -> bindb a (\ b -> returna (\ ab -> aa ab b)))))
        (\ xs -> returna (foldl (\ aa fa -> fa aa) x xs)));

comma :: Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
comma =
  bindb lx_ws
    (\ _ -> exactly [Char False False True True False True False False]);

parse_list ::
  forall a.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      Len_list Char -> Sum (() -> [Char] -> [Char]) ([a], Len_list Char);
parse_list a =
  chainL1 (bindb a (\ x -> returna [x]))
    (bindb comma (\ _ -> returna (\ aa b -> aa ++ b)));

brace_close ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
brace_close =
  bindb lx_ws (\ _ -> exactly [Char True False True True True True True False]);

json_character ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
json_character =
  bindb get
    (\ x ->
      (if not (membera
                [Char False True False False False True False False,
                  Char False True False False True False False True,
                  Char False True False True False False False False]
                x)
        then returna x
        else err_expecting_aux
               (\ _ ->
                 shows_string
                   [Char False True False True False False True False,
                     Char True True False False True False True False,
                     Char True True True True False False True False,
                     Char False True True True False False True False,
                     Char False False False False False True False False,
                     Char True True False False True True True False,
                     Char False False True False True True True False,
                     Char False True False False True True True False,
                     Char True False False True False True True False,
                     Char False True True True False True True False,
                     Char True True True False False True True False,
                     Char False False False False False True False False,
                     Char True True False False False True True False,
                     Char False False False True False True True False,
                     Char True False False False False True True False,
                     Char False True False False True True True False,
                     Char True False False False False True True False,
                     Char True True False False False True True False,
                     Char False False True False True True True False,
                     Char True False True False False True True False,
                     Char False True False False True True True False])));

identifier ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
identifier =
  bindb (exactly [Char False True False False False True False False])
    (\ _ ->
      bindb json_character
        (\ x ->
          bindb (repeat json_character)
            (\ xa ->
              bindb (exactly
                      [Char False True False False False True False False])
                (\ _ -> returna (x : xa)))));

brace_open ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
brace_open =
  bindb lx_ws (\ _ -> exactly [Char True True False True True True True False]);

colon :: Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
colon =
  bindb lx_ws
    (\ _ -> exactly [Char False True False True True True False False]);

json_string ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
json_string =
  bindb (exactly [Char False True False False False True False False])
    (\ _ ->
      bindb (repeat json_character)
        (\ a ->
          bindb (exactly [Char False True False False False True False False])
            (\ _ -> returna a)));

nats_to_nat :: Nat -> [Nat] -> Nat;
nats_to_nat x [] = x;
nats_to_nat x (n : ns) =
  nats_to_nat (plus_nat (times_nat (nat_of_integer (10 :: Integer)) x) n) ns;

lx_rat :: Len_list Char -> Sum (() -> [Char] -> [Char]) (Fract, Len_list Char);
lx_rat =
  bindb lx_int
    (\ x ->
      bindb (exactly [Char False True True True False True False False])
        (\ _ ->
          bindb lx_digit
            (\ xa ->
              bindb (repeat
                      (bindb lx_digit
                        (\ xb ->
                          returna
                            (minus_nat (nat_of_char xb)
                              (nat_of_char
                                (Char False False False False True True False
                                  False))))))
                (\ xb ->
                  returna
                    (if less_eq_int zero_int x
                      then Rata True x
                             ((int_of_nat . nats_to_nat zero_nat)
                               (minus_nat (nat_of_char xa)
                                  (nat_of_char
                                    (Char False False False False True True
                                      False False)) :
                                 xb))
                      else Rata False x
                             ((int_of_nat . nats_to_nat zero_nat)
                               (minus_nat (nat_of_char xa)
                                  (nat_of_char
                                    (Char False False False False True True
                                      False False)) :
                                 xb)))))));

atom :: Len_list Char -> Sum (() -> [Char] -> [Char]) (JSON, Len_list Char);
atom =
  bindb lx_ws
    (\ _ ->
      bindb (alt (bindb json_string (\ x -> returna (Stringa x)))
              (bindb
                (alt (bindb lx_rat (\ x -> returna (Rat x)))
                  (bindb
                    (alt (bindb lx_nat (\ x -> returna (Nata x)))
                      (bindb
                        (alt (bindb lx_int (\ x -> returna (Int x)))
                          (bindb
                            (alt (bindb
                                   (exactly
                                     [Char False False True False True True True
False,
                                       Char False True False False True True
 True False,
                                       Char True False True False True True True
 False,
                                       Char True False True False False True
 True False])
                                   (\ _ -> returna (Boolean True)))
                              (bindb
                                (alt (bindb
                                       (exactly
 [Char False True True False False True True False,
   Char True False False False False True True False,
   Char False False True True False True True False,
   Char True True False False True True True False,
   Char True False True False False True True False])
                                       (\ _ -> returna (Boolean False)))
                                  (bindb
                                    (exactly
                                      [Char False True True True False True True
 False,
Char True False True False True True True False,
Char False False True True False True True False,
Char False False True True False True True False])
                                    (\ _ -> returna Null)))
                                (\ x -> returna (sum_join x))))
                            (\ x -> returna (sum_join x))))
                        (\ x -> returna (sum_join x))))
                    (\ x -> returna (sum_join x))))
                (\ x -> returna (sum_join x))))
        (\ x -> returna (sum_join x)));

seq :: Len_list Char -> Sum (() -> [Char] -> [Char]) (JSON, Len_list Char);
seq l =
  bindb bracket_open
    (\ _ ->
      bindb (alt (parse_list json) (bindb lx_ws (\ _ -> returna [])))
        (\ x -> bindb bracket_close (\ _ -> returna (Arraya (sum_join x)))))
    l;

json :: Len_list Char -> Sum (() -> [Char] -> [Char]) (JSON, Len_list Char);
json l =
  bindb (alt atom (bindb (alt seq dict) (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x)) l;

dict :: Len_list Char -> Sum (() -> [Char] -> [Char]) (JSON, Len_list Char);
dict l =
  bindb brace_open
    (\ _ ->
      bindb (alt (parse_list
                   (bindb lx_ws
                     (\ _ ->
                       bindb identifier
                         (\ a ->
                           bindb colon
                             (\ _ -> bindb json (\ b -> returna (a, b)))))))
              (bindb lx_ws (\ _ -> returna [])))
        (\ x -> bindb brace_close (\ _ -> returna (Object (sum_join x)))))
    l;

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update [] i y = [];
list_update (x : xs) i y =
  (if equal_nat i zero_nat then y : xs
    else x : list_update xs (minus_nat i one_nat) y);

find_index :: forall a. (a -> Bool) -> [a] -> Nat;
find_index uu [] = zero_nat;
find_index p (x : xs) =
  (if p x then zero_nat else plus_nat (find_index p xs) one_nat);

index :: forall a. (Eq a) => [a] -> a -> Nat;
index xs = (\ a -> find_index (\ x -> x == a) xs);

println :: String -> ();
println x = Printing.print (x ++ "\n");

ht_new_sz ::
  forall a b.
    (Hashable a, Heapa a,
      Heapa b) => Nat -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_new_sz n = let {
                l = replicate n [];
              } in do { 
                     a <- Heap.newListArray l;
                     return (HashTable a zero_nat)
                    };

ht_new ::
  forall a b.
    (Hashable a, Heapa a, Heapa b) => Heap.ST Heap.RealWorld (Hashtable a b);
ht_new = ht_new_sz ((def_hashmap_size :: Itself a -> Nat) Type);

nat_of_uint32 :: Uint32.Word32 -> Nat;
nat_of_uint32 x = nat_of_integer (Prelude.toInteger x);

nat_of_hashcode :: Uint32.Word32 -> Nat;
nat_of_hashcode = nat_of_uint32;

bounded_hashcode_nat :: forall a. (Hashable a) => Nat -> a -> Nat;
bounded_hashcode_nat n x = modulo_nat (nat_of_hashcode (hashcode x)) n;

the_array :: forall a b. Hashtable a b -> Heap.STArray Heap.RealWorld [(a, b)];
the_array (HashTable a uu) = a;

ls_update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> ([(a, b)], Bool);
ls_update k v [] = ([(k, v)], False);
ls_update k v ((l, w) : ls) =
  (if k == l then ((k, v) : ls, True) else let {
     r = ls_update k v ls;
   } in ((l, w) : fst r, snd r));

the_size :: forall a b. Hashtable a b -> Nat;
the_size (HashTable uu n) = n;

ht_upd ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> b -> Hashtable a b ->
                              Heap.ST Heap.RealWorld (Hashtable a b);
ht_upd k v ht =
  do { 
    m <- len (the_array ht);
    let { i = bounded_hashcode_nat m k };
    l <- ntha (the_array ht) i;
    let { la = ls_update k v l };
    _ <- upd i (fst la) (the_array ht);
    let { n = (if snd la then the_size ht else suc (the_size ht)) };
    return (HashTable (the_array ht) n)
   };

map_default :: forall a b. a -> (b -> Maybe a) -> b -> a;
map_default b f a = (case f a of {
                      Nothing -> b;
                      Just ba -> ba;
                    });

ht_insls ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => [(a, b)] ->
                    Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_insls [] ht = return ht;
ht_insls ((k, v) : l) ht = ht_upd k v ht >>= ht_insls l;

ht_copy ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => Nat ->
                    Hashtable a b ->
                      Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_copy n src dst =
  (if equal_nat n zero_nat then return dst
    else do { 
           l <- ntha (the_array src) (minus_nat n one_nat);
           ht_insls l dst >>= ht_copy (minus_nat n one_nat) src
          });

execute ::
  forall a. Heap.ST Heap.RealWorld a -> Heap_ext () -> Maybe (a, Heap_ext ());
execute _ _ = error "Heap_Monad.execute";

product_lists :: forall a. [[a]] -> [[a]];
product_lists [] = [[]];
product_lists (xs : xss) =
  concatMap (\ x -> map (\ a -> x : a) (product_lists xss)) xs;

app :: forall a b. (a -> b) -> a -> b;
app f a = f a;

hm_isEmpty :: forall a b. Hashtable a b -> Heap.ST Heap.RealWorld Bool;
hm_isEmpty ht = return (equal_nat (the_size ht) zero_nat);

tRACE_impl :: Heap.ST Heap.RealWorld ();
tRACE_impl = return (tracea ());

array_get :: forall a. Array.ArrayType a -> Nat -> a;
array_get a = Array.array_get a . integer_of_nat;

array_set :: forall a. Array.ArrayType a -> Nat -> a -> Array.ArrayType a;
array_set a = Array.array_set a . integer_of_nat;

new_array :: forall a. a -> Nat -> Array.ArrayType a;
new_array v = Array.new_array v . integer_of_nat;

ls_delete :: forall a b. (Eq a) => a -> [(a, b)] -> ([(a, b)], Bool);
ls_delete k [] = ([], False);
ls_delete k ((l, w) : ls) =
  (if k == l then (ls, True) else let {
                                    r = ls_delete k ls;
                                  } in ((l, w) : fst r, snd r));

ht_delete ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_delete k ht =
  do { 
    m <- len (the_array ht);
    let { i = bounded_hashcode_nat m k };
    l <- ntha (the_array ht) i;
    let { la = ls_delete k l };
    _ <- upd i (fst la) (the_array ht);
    let { n = (if snd la then minus_nat (the_size ht) one_nat else the_size ht)
      };
    return (HashTable (the_array ht) n)
   };

ls_lookup :: forall a b. (Eq a) => a -> [(a, b)] -> Maybe b;
ls_lookup x [] = Nothing;
ls_lookup x ((k, v) : l) = (if x == k then Just v else ls_lookup x l);

ht_lookup ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> Hashtable a b -> Heap.ST Heap.RealWorld (Maybe b);
ht_lookup x ht = do { 
                   m <- len (the_array ht);
                   let { i = bounded_hashcode_nat m x };
                   l <- ntha (the_array ht) i;
                   return (ls_lookup x l)
                  };

ht_rehash ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_rehash ht =
  do { 
    n <- len (the_array ht);
    ht_new_sz (times_nat (nat_of_integer (2 :: Integer)) n) >>= ht_copy n ht
   };

load_factor :: Nat;
load_factor = nat_of_integer (75 :: Integer);

ht_update ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> b -> Hashtable a b ->
                              Heap.ST Heap.RealWorld (Hashtable a b);
ht_update k v ht =
  do { 
    m <- len (the_array ht);
    (if less_eq_nat (times_nat m load_factor)
          (times_nat (the_size ht) (nat_of_integer (100 :: Integer)))
      then ht_rehash ht else return ht) >>=
      ht_upd k v
   };

map_act :: forall a b. (a -> b) -> Act a -> Act b;
map_act f (In x1) = In (f x1);
map_act f (Out x2) = Out (f x2);
map_act f (Sil x3) = Sil (f x3);

bot_set :: forall a. Set a;
bot_set = Set [];

set_act :: forall a. (Eq a) => Act a -> Set a;
set_act (In x1) = insert x1 bot_set;
set_act (Out x2) = insert x2 bot_set;
set_act (Sil x3) = insert x3 bot_set;

uncurry0 :: forall a. a -> () -> a;
uncurry0 c = (\ _ -> c);

start_timer :: () -> ();
start_timer uu = ();

save_time :: String -> ();
save_time s = ();

time_it :: forall a. String -> (() -> a) -> a;
time_it s f = let {
                _ = start_timer ();
                r = f ();
                _ = save_time s;
              } in r;

array_copy ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
array_copy a = array_copya a;

array_copya ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
array_copya = array_copy;

array_grow :: forall a. Array.ArrayType a -> Nat -> a -> Array.ArrayType a;
array_grow a = Array.array_grow a . integer_of_nat;

binda :: forall a b. Result a -> (a -> Result b) -> Result b;
binda m f = (case m of {
              Result a -> f a;
              Error a -> Error a;
            });

hm_it_adjust ::
  forall a b.
    (Hashable a, Heapa a,
      Heapa b) => Nat -> Hashtable a b -> Heap.ST Heap.RealWorld Nat;
hm_it_adjust v ht =
  (if equal_nat v zero_nat then return zero_nat
    else do { 
           a <- ntha (the_array ht) (suc (minus_nat v one_nat));
           (case a of {
             [] -> hm_it_adjust (minus_nat (suc (minus_nat v one_nat)) one_nat)
                     ht;
             _ : _ -> return (suc (minus_nat v one_nat));
           })
          });

op_list_rev :: forall a. [a] -> [a];
op_list_rev = reverse;

all_interval_nat :: (Nat -> Bool) -> Nat -> Nat -> Bool;
all_interval_nat p i j = less_eq_nat j i || p i && all_interval_nat p (suc i) j;

map_index :: forall a b. Nat -> (Nat -> a -> b) -> [a] -> [b];
map_index n f [] = [];
map_index n f (x : xs) = f n x : map_index (suc n) f xs;

pred_act :: forall a. (Eq a) => (a -> Bool) -> Act a -> Bool;
pred_act = (\ p x -> ball (set_act x) p);

eoi ::
  forall a.
    (Showa a) => Len_list a -> Sum (() -> [Char] -> [Char]) ((), Len_list a);
eoi = bindb get_tokens
        (\ tks ->
          (if null tks then returna ()
            else err_expecting_aux
                   (\ _ ->
                     shows_string
                       [Char True False True False False True True False,
                         Char False True True True False True True False,
                         Char False False True False False True True False,
                         Char False False False False False True False False,
                         Char True True True True False True True False,
                         Char False True True False False True True False,
                         Char False False False False False True False False,
                         Char True False False True False True True False,
                         Char False True True True False True True False,
                         Char False False False False True True True False,
                         Char True False True False True True True False,
                         Char False False True False True True True False])));

pR_CONST :: forall a. a -> a;
pR_CONST x = x;

op_map_lookup :: forall a b. a -> (a -> Maybe b) -> Maybe b;
op_map_lookup = (\ k m -> m k);

swap :: forall a b. (a, b) -> (b, a);
swap p = (snd p, fst p);

while :: forall a. (a -> Bool) -> (a -> a) -> a -> a;
while b c s = (if b s then while b c (c s) else s);

array_length :: forall a. Array.ArrayType a -> Nat;
array_length = nat_of_integer . Array.array_length;

array_shrink :: forall a. Array.ArrayType a -> Nat -> Array.ArrayType a;
array_shrink a = Array.array_shrink a . integer_of_nat;

assert :: Bool -> String -> Result ();
assert b m = (if b then Result () else Error [m]);

op_list_empty :: forall a. [a];
op_list_empty = [];

as_get :: forall a. (Array.ArrayType a, Nat) -> Nat -> a;
as_get s i = (case s of {
               (a, _) -> array_get a i;
             });

as_shrink :: forall a. (Array.ArrayType a, Nat) -> (Array.ArrayType a, Nat);
as_shrink s =
  (case s of {
    (a, n) ->
      let {
        aa = (if less_eq_nat (times_nat (nat_of_integer (128 :: Integer)) n)
                   (array_length a) &&
                   less_nat (nat_of_integer (4 :: Integer)) n
               then array_shrink a n else a);
      } in (aa, n);
  });

as_pop :: forall a. (Array.ArrayType a, Nat) -> (Array.ArrayType a, Nat);
as_pop s = (case s of {
             (a, n) -> as_shrink (a, minus_nat n one_nat);
           });

as_set ::
  forall a. (Array.ArrayType a, Nat) -> Nat -> a -> (Array.ArrayType a, Nat);
as_set s i x = (case s of {
                 (a, b) -> (array_set a i x, b);
               });

as_top :: forall a. (Array.ArrayType a, Nat) -> a;
as_top s = (case s of {
             (a, n) -> array_get a (minus_nat n one_nat);
           });

hm_it_next_key ::
  forall a b.
    (Hashable a, Heapa a, Heapa b) => Hashtable a b -> Heap.ST Heap.RealWorld a;
hm_it_next_key ht =
  do { 
    n <- len (the_array ht);
    (if equal_nat n zero_nat then error "Map is empty!"
      else do { 
             i <- hm_it_adjust (minus_nat n one_nat) ht;
             a <- ntha (the_array ht) i;
             (case a of {
               [] -> error "Map is empty!";
               x : _ -> return (fst x);
             })
            })
   };

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

imp_for_int_innera ::
  forall a.
    Integer ->
      Integer ->
        (Integer -> a -> Heap.ST Heap.RealWorld a) ->
          a -> Heap.ST Heap.RealWorld a;
imp_for_int_innera i u f s =
  (if u <= i then return s
    else f i s >>= imp_for_int_innera (i + (1 :: Integer)) u f);

imp_for_inta ::
  forall a.
    Nat ->
      Nat ->
        (Nat -> a -> Heap.ST Heap.RealWorld a) -> a -> Heap.ST Heap.RealWorld a;
imp_for_inta i u f s =
  imp_for_int_innera (integer_of_nat i) (integer_of_nat u) (f . nat_of_integer)
    s;

mtx_tabulate ::
  forall a b.
    (One a, Plus a, Zero a, Zero b,
      Heapa b) => Nat ->
                    Nat ->
                      ((a, Nat) -> b) ->
                        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld b);
mtx_tabulate n m c =
  do { 
    ma <- new (times_nat n m) zero;
    (_, (_, a)) <-
      imp_for_inta zero_nat (times_nat n m)
        (\ k (i, (j, maa)) ->
          do { 
            _ <- upd k (c (i, j)) maa;
            let { ja = plus_nat j one_nat };
            (if less_nat ja m then return (i, (ja, maa))
              else return (plus i one, (zero_nat, maa)))
           })
        (zero, (zero_nat, ma));
    return a
   };

v_dbm_impl ::
  forall a.
    (Linordered_cancel_ab_monoid_add a,
      Heapa a) => Nat ->
                    Heap.ST Heap.RealWorld
                      (Heap.STArray Heap.RealWorld (DBMEntry a));
v_dbm_impl n = mtx_tabulate (suc n) (suc n) (v_dbm n);

combine2_gen ::
  forall a b c. (a -> b -> Result c) -> Result a -> Result b -> Result c;
combine2_gen comb (Error e1) (Error e2) = Error (e1 ++ e2);
combine2_gen comb (Error e) (Result uu) = Error e;
combine2_gen comb (Result uv) (Error e) = Error e;
combine2_gen comb (Result a) (Result b) = comb a b;

combine :: forall a. [Result a] -> Result [a];
combine [] = Result [];
combine (x : xs) = combine2_gen (\ xa xsa -> Result (xa : xsa)) x (combine xs);

err_msg :: forall a. String -> Result a -> Result a;
err_msg m (Error es) = Error (m : es);
err_msg m (Result v) = Result v;

stat_stop :: () -> ();
stat_stop = (\ _ -> ());

hms_lookup ::
  forall a b c d.
    (a -> b -> Heap.ST Heap.RealWorld (Maybe c)) ->
      (c -> Heap.ST Heap.RealWorld d) ->
        a -> b -> Heap.ST Heap.RealWorld (Maybe d);
hms_lookup lookup copy k m = do { 
                               a <- lookup k m;
                               (case a of {
                                 Nothing -> return Nothing;
                                 Just v -> do { 
     va <- copy v;
     return (Just va)
    };
                               })
                              };

op_list_concat :: forall a. [a] -> [a] -> [a];
op_list_concat = (\ a b -> a ++ b);

as_push :: forall a. (Array.ArrayType a, Nat) -> a -> (Array.ArrayType a, Nat);
as_push s x =
  (case s of {
    (a, n) ->
      let {
        aa = (if equal_nat n (array_length a)
               then array_grow a
                      (max (nat_of_integer (4 :: Integer))
                        (times_nat (nat_of_integer (2 :: Integer)) n))
                      x
               else a);
        ab = array_set aa n x;
      } in (ab, plus_nat n one_nat);
  });

as_take ::
  forall a. Nat -> (Array.ArrayType a, Nat) -> (Array.ArrayType a, Nat);
as_take m s = (case s of {
                (a, n) -> (if less_nat m n then as_shrink (a, m) else (a, n));
              });

rev_append :: forall a. [a] -> [a] -> [a];
rev_append [] ac = ac;
rev_append (x : xs) ac = rev_append xs (x : ac);

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

combine2 :: forall a b. Result a -> Result b -> Result (a, b);
combine2 = combine2_gen (\ a b -> Result (a, b));

stat_start :: () -> ();
stat_start = (\ _ -> ());

hms_extract ::
  forall a b c.
    (a -> b -> Heap.ST Heap.RealWorld (Maybe c)) ->
      (a -> b -> Heap.ST Heap.RealWorld b) ->
        a -> b -> Heap.ST Heap.RealWorld (Maybe c, b);
hms_extract lookup delete k m = do { 
                                  a <- lookup k m;
                                  (case a of {
                                    Nothing -> return (Nothing, m);
                                    Just v -> do { 
        ma <- delete k m;
        return (Just v, ma)
       };
                                  })
                                 };

mtx_get ::
  forall a.
    (Heapa a) => Nat ->
                   Heap.STArray Heap.RealWorld a ->
                     (Nat, Nat) -> Heap.ST Heap.RealWorld a;
mtx_get m mtx e = ntha mtx (plus_nat (times_nat (fst e) m) (snd e));

mtx_set ::
  forall a.
    (Heapa a) => Nat ->
                   Heap.STArray Heap.RealWorld a ->
                     (Nat, Nat) ->
                       a -> Heap.ST Heap.RealWorld
                              (Heap.STArray Heap.RealWorld a);
mtx_set m mtx e v = upd (plus_nat (times_nat (fst e) m) (snd e)) v mtx;

op_list_prepend :: forall a. a -> [a] -> [a];
op_list_prepend = (\ a b -> a : b);

idx_iteratei_aux ::
  forall a b c.
    (a -> Nat -> b) ->
      Nat -> Nat -> a -> (c -> Bool) -> (b -> c -> c) -> c -> c;
idx_iteratei_aux get sz i l c f sigma =
  (if equal_nat i zero_nat || not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nat) l c f
           (f (get l (minus_nat sz i)) sigma));

idx_iteratei ::
  forall a b c.
    (a -> Nat -> b) ->
      (a -> Nat) -> a -> (c -> Bool) -> (b -> c -> c) -> c -> c;
idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

as_empty :: forall a b. (Zero b) => () -> (Array.ArrayType a, b);
as_empty uu = (Array.array_of_list [], zero);

as_length :: forall a. (Array.ArrayType a, Nat) -> Nat;
as_length = snd;

last_seg_tr ::
  forall a.
    ((Array.ArrayType a, Nat),
      ((Array.ArrayType Nat, Nat),
        (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))) ->
      [a];
last_seg_tr s =
  (case s of {
    (a, (aa, (_, _))) ->
      (case while (\ (xe, _) ->
                    less_nat xe
                      (if equal_nat
                            (plus_nat (minus_nat (as_length aa) one_nat)
                              one_nat)
                            (as_length aa)
                        then as_length a
                        else as_get aa
                               (plus_nat (minus_nat (as_length aa) one_nat)
                                 one_nat)))
              (\ (ac, bc) -> let {
                               xa = as_get a ac;
                             } in (suc ac, xa : bc))
              (as_get aa (minus_nat (as_length aa) one_nat), [])
        of {
        (_, bc) -> bc;
      });
  });

list_map_update_aux ::
  forall a b. (a -> a -> Bool) -> a -> b -> [(a, b)] -> [(a, b)] -> [(a, b)];
list_map_update_aux eq k v [] accu = (k, v) : accu;
list_map_update_aux eq k v (x : xs) accu =
  (if eq (fst x) k then (k, v) : xs ++ accu
    else list_map_update_aux eq k v xs (x : accu));

list_map_update ::
  forall a b. (a -> a -> Bool) -> a -> b -> [(a, b)] -> [(a, b)];
list_map_update eq k v m = list_map_update_aux eq k v m [];

list_map_lookup :: forall a b. (a -> a -> Bool) -> a -> [(a, b)] -> Maybe b;
list_map_lookup eq uu [] = Nothing;
list_map_lookup eq k (y : ys) =
  (if eq (fst y) k then Just (snd y) else list_map_lookup eq k ys);

ahm_update_aux ::
  forall a b.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) -> Hashmap a b -> a -> b -> Hashmap a b;
ahm_update_aux eq bhc (HashMap a n) k v =
  let {
    h = bhc (array_length a) k;
    m = array_get a h;
    insert = is_none (list_map_lookup eq k m);
  } in HashMap (array_set a h (list_map_update eq k v m))
         (if insert then plus_nat n one_nat else n);

ahm_iteratei_aux ::
  forall a b c.
    Array.ArrayType [(a, b)] -> (c -> Bool) -> ((a, b) -> c -> c) -> c -> c;
ahm_iteratei_aux a c f sigma =
  idx_iteratei array_get array_length a c (\ x -> foldli x c f) sigma;

ahm_rehash_auxa ::
  forall a b.
    (Nat -> a -> Nat) ->
      Nat -> (a, b) -> Array.ArrayType [(a, b)] -> Array.ArrayType [(a, b)];
ahm_rehash_auxa bhc n kv a = let {
                               h = bhc n (fst kv);
                             } in array_set a h (kv : array_get a h);

ahm_rehash_aux ::
  forall a b.
    (Nat -> a -> Nat) ->
      Array.ArrayType [(a, b)] -> Nat -> Array.ArrayType [(a, b)];
ahm_rehash_aux bhc a sz =
  ahm_iteratei_aux a (\ _ -> True) (ahm_rehash_auxa bhc sz) (new_array [] sz);

ahm_rehash ::
  forall a b. (Nat -> a -> Nat) -> Hashmap a b -> Nat -> Hashmap a b;
ahm_rehash bhc (HashMap a n) sz = HashMap (ahm_rehash_aux bhc a sz) n;

load_factora :: Nat;
load_factora = nat_of_integer (75 :: Integer);

ahm_filled :: forall a b. Hashmap a b -> Bool;
ahm_filled (HashMap a n) =
  less_eq_nat (times_nat (array_length a) load_factora)
    (times_nat n (nat_of_integer (100 :: Integer)));

hm_grow :: forall a b. Hashmap a b -> Nat;
hm_grow (HashMap a n) =
  plus_nat (times_nat (nat_of_integer (2 :: Integer)) (array_length a))
    (nat_of_integer (3 :: Integer));

ahm_update ::
  forall a b.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) -> a -> b -> Hashmap a b -> Hashmap a b;
ahm_update eq bhc k v hm =
  let {
    hma = ahm_update_aux eq bhc hm k v;
  } in (if ahm_filled hma then ahm_rehash bhc hma (hm_grow hma) else hma);

pop_tr ::
  forall a.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) ->
        ((Array.ArrayType a, Nat),
          ((Array.ArrayType Nat, Nat),
            (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))) ->
          ((Array.ArrayType a, Nat),
            ((Array.ArrayType Nat, Nat),
              (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat))));
pop_tr node_eq_impl node_hash_impl s =
  (case s of {
    (a, (aa, (ab, bb))) ->
      let {
        x = minus_nat (as_length aa) one_nat;
        xa = (case while (\ (xe, _) ->
                           less_nat xe
                             (if equal_nat (plus_nat x one_nat) (as_length aa)
                               then as_length a
                               else as_get aa (plus_nat x one_nat)))
                     (\ (ac, bc) ->
                       (suc ac,
                         ahm_update node_eq_impl node_hash_impl (as_get a ac)
                           (uminus_int one_int) bc))
                     (as_get aa x, ab)
               of {
               (_, bc) -> bc;
             });
        xb = as_take (as_top aa) a;
        xc = as_pop aa;
      } in (xb, (xc, (xa, bb)));
  });

op_list_is_empty :: forall a. [a] -> Bool;
op_list_is_empty = null;

glist_delete_aux :: forall a. (a -> a -> Bool) -> a -> [a] -> [a] -> [a];
glist_delete_aux eq x [] asa = asa;
glist_delete_aux eq x (y : ys) asa =
  (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y : asa));

glist_delete :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
glist_delete eq x l = glist_delete_aux eq x l [];

lx_uppercase ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
lx_uppercase =
  range (Char True False False False False False True False)
    (Char False True False True True False True False);

lx_lowercase ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
lx_lowercase =
  range (Char True False False False False True True False)
    (Char False True False True True True True False);

lx_alpha :: Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
lx_alpha = bindb (alt lx_lowercase lx_uppercase) (\ x -> returna (sum_join x));

imp_nfoldli ::
  forall a b.
    [a] ->
      (b -> Heap.ST Heap.RealWorld Bool) ->
        (a -> b -> Heap.ST Heap.RealWorld b) -> b -> Heap.ST Heap.RealWorld b;
imp_nfoldli (x : ls) c f s =
  do { 
    b <- c s;
    (if b then f x s >>= imp_nfoldli ls c f else return s)
   };
imp_nfoldli [] c f s = return s;

is_Nil :: forall a. [a] -> Bool;
is_Nil a = (case a of {
             [] -> True;
             _ : _ -> False;
           });

norm_diag :: forall a. (Zero a, Eq a, Linorder a) => DBMEntry a -> DBMEntry a;
norm_diag e =
  (if dbm_lt e (Le zero) then Lt zero
    else (if equal_DBMEntry e (Le zero) then e else INF));

fold_error :: forall a b. (a -> b -> Result b) -> [a] -> b -> Result b;
fold_error f [] a = Result a;
fold_error f (x : xs) a = binda (f x a) (fold_error f xs);

the_errors :: forall a. Result a -> [String];
the_errors (Error es) = es;

find_max_nat :: Nat -> (Nat -> Bool) -> Nat;
find_max_nat n uu =
  (if equal_nat n zero_nat then zero_nat
    else (if uu (minus_nat n one_nat) then minus_nat n one_nat
           else find_max_nat (minus_nat n one_nat) uu));

stat_newnode :: () -> ();
stat_newnode = (\ _ -> ());

amtx_copy ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
amtx_copy = array_copy;

amtx_dflt ::
  forall a.
    (Heapa a) => Nat ->
                   Nat ->
                     a -> Heap.ST Heap.RealWorld
                            (Heap.STArray Heap.RealWorld a);
amtx_dflt n m v = make (times_nat n m) (\ _ -> v);

lso_bex_impl ::
  forall a.
    (a -> Heap.ST Heap.RealWorld Bool) -> [a] -> Heap.ST Heap.RealWorld Bool;
lso_bex_impl pi li =
  imp_nfoldli li (\ sigma -> return (not sigma)) (\ xa _ -> pi xa) False;

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

ll_from_list :: forall a. [a] -> Len_list a;
ll_from_list l = LL (size_list l) l;

show_pres :: forall a b c. Sum a (b, c) -> Sum a b;
show_pres (Inr (ll, uu)) = Inr ll;
show_pres (Inl e) = Inl e;

parse_all ::
  forall a b.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      (Len_list Char -> Sum (() -> [Char] -> [Char]) (b, Len_list Char)) ->
        String -> Sum (() -> [Char] -> [Char]) b;
parse_all ws p =
  ((show_pres .
     bindb p (\ a -> bindb ws (\ _ -> bindb eoi (\ _ -> returna a)))) .
    ll_from_list) .
    explode;

save_time_impl :: String -> Heap.ST Heap.RealWorld ();
save_time_impl = return . save_time;

is_None :: forall a. Maybe a -> Bool;
is_None a = (case a of {
              Nothing -> True;
              Just _ -> False;
            });

norm_lower :: forall a. (Linorder a) => DBMEntry a -> a -> DBMEntry a;
norm_lower e t = (if dbm_lt e (Lt t) then Lt t else e);

norm_upper :: forall a. (Linorder a) => DBMEntry a -> a -> DBMEntry a;
norm_upper e t = (if dbm_lt (Le t) e then INF else e);

min_int_entry :: DBMEntry Int -> DBMEntry Int -> DBMEntry Int;
min_int_entry (Lt x) (Lt y) = (if less_eq_int x y then Lt x else Lt y);
min_int_entry (Lt x) (Le y) = (if less_eq_int x y then Lt x else Le y);
min_int_entry (Le x) (Lt y) = (if less_int x y then Le x else Lt y);
min_int_entry (Le x) (Le y) = (if less_eq_int x y then Le x else Le y);
min_int_entry INF x = x;
min_int_entry (Le v) INF = Le v;
min_int_entry (Lt v) INF = Lt v;

and_entry_impl ::
  Nat ->
    Nat ->
      Nat ->
        DBMEntry Int ->
          Heap.STArray Heap.RealWorld (DBMEntry Int) ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
and_entry_impl =
  (\ n ai bib bia bi -> do { 
                          x <- mtx_get (suc n) bi (ai, bib);
                          mtx_set (suc n) bi (ai, bib) (min_int_entry x bia)
                         });

free_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
free_impl_int =
  (\ n ai bi ->
    imp_for_inta zero_nat (suc n)
      (\ xa sigma ->
        (if not (equal_nat xa bi)
          then mtx_get (suc n) sigma (xa, zero_nat) >>=
                 mtx_set (suc n) sigma (xa, bi)
          else return sigma))
      ai >>=
      imp_for_inta zero_nat (suc n)
        (\ xb sigma ->
          (if not (equal_nat xb bi) then mtx_set (suc n) sigma (bi, xb) INF
            else return sigma)));

dbm_lt_int :: DBMEntry Int -> DBMEntry Int -> Bool;
dbm_lt_int (Le a) (Le b) = less_int a b;
dbm_lt_int (Le a) (Lt b) = less_int a b;
dbm_lt_int (Lt a) (Le b) = less_eq_int a b;
dbm_lt_int (Lt a) (Lt b) = less_int a b;
dbm_lt_int INF uu = False;
dbm_lt_int (Le v) INF = True;
dbm_lt_int (Lt v) INF = True;

upd_integer ::
  forall a.
    (Heapa a) => Integer ->
                   a -> Heap.STArray Heap.RealWorld a ->
                          Heap.ST Heap.RealWorld
                            (Heap.STArray Heap.RealWorld a);
upd_integer n x a = upd (nat_of_integer n) x a;

nth_integer ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Integer -> Heap.ST Heap.RealWorld a;
nth_integer a n = ntha a (nat_of_integer n);

dbm_add_int :: DBMEntry Int -> DBMEntry Int -> DBMEntry Int;
dbm_add_int INF uu = INF;
dbm_add_int (Le v) INF = INF;
dbm_add_int (Lt v) INF = INF;
dbm_add_int (Le a) (Le b) = Le (plus_int a b);
dbm_add_int (Le a) (Lt b) = Lt (plus_int a b);
dbm_add_int (Lt a) (Le b) = Lt (plus_int a b);
dbm_add_int (Lt a) (Lt b) = Lt (plus_int a b);

fw_upd_impl_integer ::
  Integer ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Integer ->
        Integer ->
          Integer ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
fw_upd_impl_integer n a k i j =
  let {
    na = n + (1 :: Integer);
    ia = i * na + j;
  } in do { 
         y <- nth_integer a (i * na + k);
         z <- nth_integer a (k * na + j);
         x <- nth_integer a ia;
         let { m = dbm_add_int y z };
         (if dbm_lt_int m x then upd_integer ia m a else return a)
        };

fwi_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
fwi_impl_int n a k =
  let {
    na = integer_of_nat n;
    n_plus_1 = na + (1 :: Integer);
  } in imp_for_int_innera (0 :: Integer) n_plus_1
         (\ i ->
           imp_for_int_innera (0 :: Integer) n_plus_1
             (\ ia xa -> fw_upd_impl_integer na xa (integer_of_nat k) i ia))
         a;

repair_pair_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Nat ->
          Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
repair_pair_impl_int = (\ n ai bia bi -> do { 
   x <- fwi_impl_int n ai bi;
   fwi_impl_int n x bia
  });

restrict_zero_impl ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
restrict_zero_impl n =
  (\ ai bi -> do { 
                x <- and_entry_impl n bi zero_nat (Le zero_int) ai;
                x_a <- and_entry_impl n zero_nat bi (Le zero_int) x;
                repair_pair_impl_int n x_a bi zero_nat
               });

pre_reset_impl ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
pre_reset_impl n = (\ ai bi -> do { 
                                 x <- restrict_zero_impl n ai bi;
                                 free_impl_int n x bi
                                });

gi_E :: forall a b c d. Gen_g_impl_ext a b c d -> b;
gi_E (Gen_g_impl_ext gi_V gi_E gi_V0 more) = gi_E;

more :: forall a b c d. Gen_g_impl_ext a b c d -> d;
more (Gen_g_impl_ext gi_V gi_E gi_V0 more) = more;

combine_map :: forall a b. (a -> Result b) -> [a] -> Result [b];
combine_map f xs = combine (map f xs);

as_is_empty :: forall a. (Array.ArrayType a, Nat) -> Bool;
as_is_empty s = equal_nat (snd s) zero_nat;

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

part :: forall a b. (Linorder b) => (a -> b) -> b -> [a] -> ([a], ([a], [a]));
part f pivot (x : xs) =
  (case part f pivot xs of {
    (lts, (eqs, gts)) ->
      let {
        xa = f x;
      } in (if less xa pivot then (x : lts, (eqs, gts))
             else (if less pivot xa then (lts, (eqs, x : gts))
                    else (lts, (x : eqs, gts))));
  });
part f pivot [] = ([], ([], []));

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      (case part f
              (f (nth xs
                   (divide_nat (size_list xs) (nat_of_integer (2 :: Integer)))))
              xs
        of {
        (lts, (eqs, gts)) -> sort_key f lts ++ eqs ++ sort_key f gts;
      });
  });

heap_WHILET ::
  forall a.
    (a -> Heap.ST Heap.RealWorld Bool) ->
      (a -> Heap.ST Heap.RealWorld a) -> a -> Heap.ST Heap.RealWorld a;
heap_WHILET b f s = do { 
                      bv <- b s;
                      (if bv then f s >>= heap_WHILET b f else return s)
                     };

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);
minus_set a (Set xs) = fold remove xs a;

heap_map ::
  forall a b.
    (a -> Heap.ST Heap.RealWorld b) -> [a] -> Heap.ST Heap.RealWorld [b];
heap_map copy xs =
  do { 
    xsa <-
      imp_nfoldli xs (\ _ -> return True) (\ x xsa -> do { 
                xa <- copy x;
                return (xa : xsa)
               })
        [];
    return (reverse xsa)
   };

run_heap :: forall a. Heap.ST Heap.RealWorld a -> a;
run_heap h = fst (the (execute h empty));

gi_V0 :: forall a b c d. Gen_g_impl_ext a b c d -> c;
gi_V0 (Gen_g_impl_ext gi_V gi_E gi_V0 more) = gi_V0;

select_edge_tr ::
  forall a.
    (a -> a -> Bool) ->
      ((Array.ArrayType a, Nat),
        ((Array.ArrayType Nat, Nat),
          (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))) ->
        (Maybe a,
          ((Array.ArrayType a, Nat),
            ((Array.ArrayType Nat, Nat),
              (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))));
select_edge_tr node_eq_impl s =
  (case s of {
    (a, (aa, (ab, bb))) ->
      (if as_is_empty bb then (Nothing, (a, (aa, (ab, bb))))
        else (case as_top bb of {
               (ac, bc) ->
                 (if less_eq_nat (as_get aa (minus_nat (as_length aa) one_nat))
                       ac
                   then let {
                          xa = gen_pick (\ x -> foldli (id x)) bc;
                          xb = glist_delete node_eq_impl xa bc;
                          xc = (if is_Nil xb then as_pop bb
                                 else as_set bb
(minus_nat (as_length bb) one_nat) (ac, xb));
                        } in (Just xa, (a, (aa, (ab, xc))))
                   else (Nothing, (a, (aa, (ab, bb)))));
             }));
  });

ahm_lookup_aux ::
  forall a b.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) -> a -> Array.ArrayType [(a, b)] -> Maybe b;
ahm_lookup_aux eq bhc k a =
  list_map_lookup eq k (array_get a (bhc (array_length a) k));

ahm_lookup ::
  forall a b.
    (a -> a -> Bool) -> (Nat -> a -> Nat) -> a -> Hashmap a b -> Maybe b;
ahm_lookup eq bhc k (HashMap a uu) = ahm_lookup_aux eq bhc k a;

idx_of_tr ::
  forall a.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) ->
        a -> ((Array.ArrayType a, Nat),
               ((Array.ArrayType Nat, Nat),
                 (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))) ->
               Nat;
idx_of_tr node_eq_impl node_hash_impl s v =
  (case v of {
    (_, (aa, (ab, _))) ->
      let {
        x = (case ahm_lookup node_eq_impl node_hash_impl s ab of {
              Just i ->
                (if less_eq_int zero_int i then nat i else error "undefined");
            });
        xa = find_max_nat (as_length aa) (\ j -> less_eq_nat (as_get aa j) x);
      } in xa;
  });

collapse_tr ::
  forall a.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) ->
        a -> ((Array.ArrayType a, Nat),
               ((Array.ArrayType Nat, Nat),
                 (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))) ->
               ((Array.ArrayType a, Nat),
                 ((Array.ArrayType Nat, Nat),
                   (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat))));
collapse_tr node_eq_impl node_hash_impl v s =
  (case s of {
    (a, (aa, (ab, bb))) ->
      let {
        x = idx_of_tr node_eq_impl node_hash_impl v (a, (aa, (ab, bb)));
        xa = as_take (plus_nat x one_nat) aa;
      } in (a, (xa, (ab, bb)));
  });

as_singleton :: forall a b. (One b) => a -> (Array.ArrayType a, b);
as_singleton x = (Array.array_of_list [x], one);

new_hashmap_with :: forall a b. Nat -> Hashmap a b;
new_hashmap_with size = HashMap (new_array [] size) zero_nat;

ahm_empty :: forall a b. Nat -> Hashmap a b;
ahm_empty def_size = new_hashmap_with def_size;

push_code ::
  forall a b.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) ->
        Gen_g_impl_ext (a -> Bool) (a -> [a]) [a] b ->
          a -> ((Array.ArrayType a, Nat),
                 ((Array.ArrayType Nat, Nat),
                   (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat)))) ->
                 ((Array.ArrayType a, Nat),
                   ((Array.ArrayType Nat, Nat),
                     (Hashmap a Int, (Array.ArrayType (Nat, [a]), Nat))));
push_code node_eq_impl node_hash_impl g_impl =
  (\ x (xa, (xb, (xc, xd))) ->
    let {
      _ = stat_newnode ();
      y_a = as_length xa;
      y_b = as_push xa x;
      y_c = as_push xb y_a;
      y_d = ahm_update node_eq_impl node_hash_impl x (int_of_nat y_a) xc;
      y_e = (if is_Nil (gi_E g_impl x) then xd
              else as_push xd (y_a, gi_E g_impl x));
    } in (y_b, (y_c, (y_d, y_e))));

compute_SCC_tr ::
  forall a b.
    (a -> a -> Bool) ->
      (Nat -> a -> Nat) ->
        Nat -> Gen_g_impl_ext (a -> Bool) (a -> [a]) [a] b -> [[a]];
compute_SCC_tr node_eq_impl node_hash_impl node_def_hash_size g =
  let {
    _ = stat_start ();
    xa = ([], ahm_empty node_def_hash_size);
  } in (case foldli (id (gi_V0 g)) (\ _ -> True)
               (\ xb (a, b) ->
                 (if not (case ahm_lookup node_eq_impl node_hash_impl xb b of {
                           Nothing -> False;
                           Just i ->
                             (if less_eq_int zero_int i then False else True);
                         })
                   then let {
                          xc = (a, (as_singleton xb,
                                     (as_singleton zero_nat,
                                       (ahm_update node_eq_impl node_hash_impl
  xb (int_of_nat zero_nat) b,
 (if is_Nil (gi_E g xb) then as_empty ()
   else as_singleton (zero_nat, gi_E g xb))))));
                        } in (case while (\ (_, xf) ->
   not (as_is_empty (case xf of {
                      (xg, (_, (_, _))) -> xg;
                    })))
                                     (\ (aa, ba) ->
                                       (case select_edge_tr node_eq_impl ba of {
 (Nothing, bb) -> let {
                    xf = last_seg_tr bb;
                    xg = pop_tr node_eq_impl node_hash_impl bb;
                    xh = xf : aa;
                  } in (xh, xg);
 (Just xf, bb) ->
   (if (case ahm_lookup node_eq_impl node_hash_impl xf
               (case bb of {
                 (_, (_, (xl, _))) -> xl;
               })
         of {
         Nothing -> False;
         Just i -> (if less_eq_int zero_int i then True else False);
       })
     then let {
            ab = collapse_tr node_eq_impl node_hash_impl xf bb;
          } in (aa, ab)
     else (if not (case ahm_lookup node_eq_impl node_hash_impl xf
                          (case bb of {
                            (_, (_, (xl, _))) -> xl;
                          })
                    of {
                    Nothing -> False;
                    Just i -> (if less_eq_int zero_int i then False else True);
                  })
            then (aa, push_code node_eq_impl node_hash_impl g xf bb)
            else (aa, bb)));
                                       }))
                                     xc
                               of {
                               (aa, (_, (_, (ad, _)))) -> (aa, ad);
                             })
                   else (a, b)))
               xa
         of {
         (a, _) -> let {
                     _ = stat_stop ();
                   } in a;
       });

constraint_clk :: forall a b. Acconstraint a b -> a;
constraint_clk (LT c uu) = c;
constraint_clk (LE c uv) = c;
constraint_clk (EQ c uw) = c;
constraint_clk (GE c ux) = c;
constraint_clk (GT c uy) = c;

start_timer_impl :: () -> Heap.ST Heap.RealWorld ();
start_timer_impl = return . start_timer;

neg_dbm_entry_int :: DBMEntry Int -> DBMEntry Int;
neg_dbm_entry_int (Le a) = Lt (uminus_int a);
neg_dbm_entry_int (Lt a) = Le (uminus_int a);
neg_dbm_entry_int INF = INF;

and_entry_repair_impl ::
  Nat ->
    Nat ->
      Nat ->
        DBMEntry Int ->
          Heap.STArray Heap.RealWorld (DBMEntry Int) ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
and_entry_repair_impl =
  (\ n ai bib bia bi -> do { 
                          x <- and_entry_impl n ai bib bia bi;
                          repair_pair_impl_int n x ai bib
                         });

upd_entry_impl_int ::
  Nat ->
    Nat ->
      Nat ->
        Heap.STArray Heap.RealWorld (DBMEntry Int) ->
          Heap.STArray Heap.RealWorld (DBMEntry Int) ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
upd_entry_impl_int =
  (\ n ai bib bia bi ->
    do { 
      x <- mtx_get (suc n) bi (ai, bib);
      amtx_copy bia >>= and_entry_repair_impl n bib ai (neg_dbm_entry_int x)
     });

upd_entries_impl ::
  Nat ->
    Nat ->
      Nat ->
        Heap.STArray Heap.RealWorld (DBMEntry Int) ->
          [Heap.STArray Heap.RealWorld (DBMEntry Int)] ->
            Heap.ST Heap.RealWorld [Heap.STArray Heap.RealWorld (DBMEntry Int)];
upd_entries_impl =
  (\ n ai bib bia bi ->
    do { 
      x <- imp_nfoldli bi (\ _ -> return True)
             (\ xa sigma -> do { 
                              x_b <- upd_entry_impl_int n ai bib xa bia;
                              return (x_b : sigma)
                             })
             op_list_empty;
      imp_nfoldli x (\ _ -> return True) (\ xb sigma -> return (xb : sigma))
        op_list_empty
     });

map_exp :: forall a b c. (a -> b) -> Exp a c -> Exp b c;
map_exp f (Const x1) = Const x1;
map_exp f (Var x2) = Var (f x2);
map_exp f (If_then_else x31 x32 x33) =
  If_then_else (map_bexp f x31) (map_exp f x32) (map_exp f x33);
map_exp f (Binop x41 x42 x43) = Binop x41 (map_exp f x42) (map_exp f x43);
map_exp f (Unop x51 x52) = Unop x51 (map_exp f x52);

map_bexp :: forall a b c. (a -> b) -> Bexp a c -> Bexp b c;
map_bexp f Truea = Truea;
map_bexp f (Not x2) = Not (map_bexp f x2);
map_bexp f (And x31 x32) = And (map_bexp f x31) (map_bexp f x32);
map_bexp f (Or x41 x42) = Or (map_bexp f x41) (map_bexp f x42);
map_bexp f (Imply x51 x52) = Imply (map_bexp f x51) (map_bexp f x52);
map_bexp f (Eqa x61 x62) = Eqa (map_exp f x61) (map_exp f x62);
map_bexp f (Lea x71 x72) = Lea (map_exp f x71) (map_exp f x72);
map_bexp f (Lta x81 x82) = Lta (map_exp f x81) (map_exp f x82);
map_bexp f (Ge x91 x92) = Ge (map_exp f x91) (map_exp f x92);
map_bexp f (Gt x101 x102) = Gt (map_exp f x101) (map_exp f x102);

set_exp :: forall a b. (Eq a) => Exp a b -> Set a;
set_exp (Const x1) = bot_set;
set_exp (Var x2) = insert x2 bot_set;
set_exp (If_then_else x31 x32 x33) =
  sup_set (sup_set (set_bexp x31) (set_exp x32)) (set_exp x33);
set_exp (Binop x41 x42 x43) = sup_set (set_exp x42) (set_exp x43);
set_exp (Unop x51 x52) = set_exp x52;

set_bexp :: forall a b. (Eq a) => Bexp a b -> Set a;
set_bexp Truea = bot_set;
set_bexp (Not x2) = set_bexp x2;
set_bexp (And x31 x32) = sup_set (set_bexp x31) (set_bexp x32);
set_bexp (Or x41 x42) = sup_set (set_bexp x41) (set_bexp x42);
set_bexp (Imply x51 x52) = sup_set (set_bexp x51) (set_bexp x52);
set_bexp (Eqa x61 x62) = sup_set (set_exp x61) (set_exp x62);
set_bexp (Lea x71 x72) = sup_set (set_exp x71) (set_exp x72);
set_bexp (Lta x81 x82) = sup_set (set_exp x81) (set_exp x82);
set_bexp (Ge x91 x92) = sup_set (set_exp x91) (set_exp x92);
set_bexp (Gt x101 x102) = sup_set (set_exp x101) (set_exp x102);

constraint_pair :: forall a b. Acconstraint a b -> (a, b);
constraint_pair (LT x m) = (x, m);
constraint_pair (LE x m) = (x, m);
constraint_pair (EQ x m) = (x, m);
constraint_pair (GE x m) = (x, m);
constraint_pair (GT x m) = (x, m);

maxa :: forall a. (Linorder a) => Set a -> a;
maxa (Set (x : xs)) = fold max xs x;

print_check :: String -> Bool -> ();
print_check s b = println ((s ++ ": ") ++ (if b then "passed" else "failed"));

run_map_heap :: forall a b. (a -> Heap.ST Heap.RealWorld b) -> [a] -> [b];
run_map_heap f xs = mapa (run_heap . f) xs;

dbm_lt_0 :: DBMEntry Int -> Bool;
dbm_lt_0 INF = False;
dbm_lt_0 (Lt x) = less_eq_int x zero_int;
dbm_lt_0 (Le x) = less_int x zero_int;

imp_for_int_inner ::
  forall a.
    Integer ->
      Integer ->
        (a -> Heap.ST Heap.RealWorld Bool) ->
          (Integer -> a -> Heap.ST Heap.RealWorld a) ->
            a -> Heap.ST Heap.RealWorld a;
imp_for_int_inner i u c f s =
  (if u <= i then return s
    else do { 
           ctn <- c s;
           (if ctn then f i s >>= imp_for_int_inner (i + (1 :: Integer)) u c f
             else return s)
          });

imp_for_int ::
  forall a.
    Nat ->
      Nat ->
        (a -> Heap.ST Heap.RealWorld Bool) ->
          (Nat -> a -> Heap.ST Heap.RealWorld a) ->
            a -> Heap.ST Heap.RealWorld a;
imp_for_int i u c f s =
  imp_for_int_inner (integer_of_nat i) (integer_of_nat u) c (f . nat_of_integer)
    s;

check_diag_impl_inta ::
  Nat ->
    Nat ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) -> Heap.ST Heap.RealWorld Bool;
check_diag_impl_inta =
  (\ n ai bi ->
    imp_for_int zero_nat (suc ai) (\ sigma -> return (not sigma))
      (\ xb sigma -> do { 
                       x <- mtx_get (suc n) bi (xb, xb);
                       return (dbm_lt_0 x || sigma)
                      })
      False);

dbm_le_int :: DBMEntry Int -> DBMEntry Int -> Bool;
dbm_le_int (Lt a) (Lt b) = less_eq_int a b;
dbm_le_int (Lt a) (Le b) = less_eq_int a b;
dbm_le_int (Le a) (Lt b) = less_int a b;
dbm_le_int (Le a) (Le b) = less_eq_int a b;
dbm_le_int uu INF = True;
dbm_le_int INF (Le v) = False;
dbm_le_int INF (Lt v) = False;

dbm_subset_impl_inta ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) -> Heap.ST Heap.RealWorld Bool;
dbm_subset_impl_inta =
  (\ m a b ->
    imp_for_int zero_nat (times_nat (plus_nat m one_nat) (plus_nat m one_nat))
      return (\ i _ -> do { 
                         x <- ntha a i;
                         y <- ntha b i;
                         return (dbm_le_int x y)
                        })
      True);

get_entries_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Heap.ST Heap.RealWorld [(Nat, Nat)];
get_entries_impl_int =
  (\ n xi ->
    do { 
      x <- imp_for_inta zero_nat (suc n)
             (\ xc sigma ->
               do { 
                 x <- imp_for_inta zero_nat (suc n)
                        (\ xf sigmaa ->
                          do { 
                            x <- mtx_get (suc n) xi (xc, xf);
                            return
                              ((if (less_nat zero_nat xc ||
                                     less_nat zero_nat xf) &&
                                     not (equal_DBMEntry x INF)
                                 then op_list_prepend (xc, xf) op_list_empty
                                 else op_list_empty) :
                                sigmaa)
                           })
                        op_list_empty;
                 x_c <-
                   imp_nfoldli (op_list_rev (op_list_rev x))
                     (\ _ -> return True) (\ xf sigmaa -> return (xf ++ sigmaa))
                     op_list_empty;
                 return (x_c : sigma)
                })
             op_list_empty;
      imp_nfoldli (op_list_rev (op_list_rev x)) (\ _ -> return True)
        (\ xc sigma -> return (xc ++ sigma)) op_list_empty
     });

dbm_minus_canonical_impl ::
  Nat ->
    [Heap.STArray Heap.RealWorld (DBMEntry Int)] ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) ->
        Heap.ST Heap.RealWorld [Heap.STArray Heap.RealWorld (DBMEntry Int)];
dbm_minus_canonical_impl =
  (\ n ai bi ->
    do { 
      x <- get_entries_impl_int n bi;
      xa <- imp_nfoldli x (\ _ -> return True)
              (\ xb sigma ->
                do { 
                  xa <- upd_entries_impl n (fst xb) (snd xb) bi ai;
                  x_c <-
                    imp_nfoldli xa (\ _ -> return True)
                      (\ xe sigmaa -> return (xe : sigmaa)) op_list_empty;
                  return (x_c ++ sigma)
                 })
              op_list_empty;
      xb <- imp_nfoldli xa (\ _ -> return True)
              (\ xb sigma -> return (xb : sigma)) op_list_empty;
      xc <- imp_nfoldli xb (\ _ -> return True)
              (\ xba sigma ->
                do { 
                  xc <- check_diag_impl_inta n n xba;
                  return (if not xc then op_list_prepend xba sigma else sigma)
                 })
              op_list_empty;
      imp_nfoldli xc (\ _ -> return True) (\ xba sigma -> return (xba : sigma))
        op_list_empty
     });

dbm_subset_fed_impl ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      [Heap.STArray Heap.RealWorld (DBMEntry Int)] ->
        Heap.ST Heap.RealWorld Bool;
dbm_subset_fed_impl n =
  (\ ai bi ->
    do { 
      x <- imp_nfoldli bi (\ _ -> return True)
             (\ xa sigma ->
               do { 
                 x <- check_diag_impl_inta n n xa;
                 return (if not x then op_list_prepend xa sigma else sigma)
                })
             op_list_empty;
      let { xa = op_list_rev x };
      (if op_list_is_empty xa then check_diag_impl_inta n n ai
        else do { 
               x_b <-
                 imp_nfoldli xa (\ sigma -> return (not sigma))
                   (\ xc sigma -> do { 
                                    x_d <- dbm_subset_impl_inta n ai xc;
                                    return (if x_d then True else sigma)
                                   })
                   False;
               (if x_b then return True
                 else do { 
                        x_c <-
                          imp_nfoldli xa (\ _ -> return True)
                            (\ xd sigma -> dbm_minus_canonical_impl n sigma xd)
                            (op_list_prepend ai op_list_empty);
                        return (op_list_is_empty x_c)
                       })
              })
     });

pre_reset_list_impl ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      [Nat] ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
pre_reset_list_impl n =
  (\ ai bi ->
    imp_nfoldli bi (\ _ -> return True) (\ x sigma -> pre_reset_impl n sigma x)
      ai);

is_result :: forall a. Result a -> Bool;
is_result (Result x1) = True;
is_result (Error x2) = False;

compute_SCC_tra ::
  forall a b.
    (Eq a, Hashable a) => Gen_g_impl_ext (a -> Bool) (a -> [a]) [a] b -> [[a]];
compute_SCC_tra =
  compute_SCC_tr (\ a b -> a == b) bounded_hashcode_nat
    ((def_hashmap_size :: Itself a -> Nat) Type);

collect_clock_pairs :: forall a b. [Acconstraint a b] -> Set (a, b);
collect_clock_pairs cc = image constraint_pair (Set cc);

list_of_map_impl ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => Hashtable a b -> Heap.ST Heap.RealWorld [(a, b)];
list_of_map_impl =
  (\ xi ->
    do { 
      (a1, _) <-
        heap_WHILET (\ (_, a2) -> do { 
                                    x_a <- hm_isEmpty a2;
                                    return (not x_a)
                                   })
          (\ (a1, a2) -> do { 
                           x_a <- hm_it_next_key a2;
                           (a1a, b) <- hms_extract ht_lookup ht_delete x_a a2;
                           return ((x_a, the a1a) : a1, b)
                          })
          ([], xi);
      return a1
     });

print_check_impl :: String -> Bool -> Heap.ST Heap.RealWorld ();
print_check_impl = (\ ai bi -> return (print_check ai bi));

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

parallel_fold_map ::
  forall a b.
    (a -> Heap.ST Heap.RealWorld b) -> [a] -> Heap.ST Heap.RealWorld [b];
parallel_fold_map = fold_map;

sup_seta :: forall a. (Eq a) => Set (Set a) -> Set a;
sup_seta (Set xs) = fold sup_set xs bot_set;

make_string ::
  forall a.
    (Linordered_ab_group_add a, Eq a,
      Heapa a) => (Nat -> [Char]) ->
                    (a -> [Char]) -> DBMEntry a -> Nat -> Nat -> Maybe [Char];
make_string show_clock show_num e i j =
  (if equal_nat i j
    then (if less_DBMEntry e zero_DBMEntry
           then Just [Char True False True False False False True False,
                       Char True False True True False False True False,
                       Char False False False False True False True False,
                       Char False False True False True False True False,
                       Char True False False True True False True False]
           else Nothing)
    else (if equal_nat i zero_nat
           then (case e of {
                  Le a ->
                    (if a == zero then Nothing
                      else Just (show_clock j ++
                                  [Char False False False False False True False
                                     False,
                                    Char False True True True True True False
                                      False,
                                    Char True False True True True True False
                                      False,
                                    Char False False False False False True
                                      False False] ++
                                    show_num (uminus a)));
                  Lt a ->
                    Just (show_clock j ++
                           [Char False False False False False True False False,
                             Char False True True True True True False False,
                             Char False False False False False True False
                               False] ++
                             show_num (uminus a));
                  INF -> Nothing;
                })
           else (if equal_nat j zero_nat
                  then (case e of {
                         Le a ->
                           Just (show_clock i ++
                                  [Char False False False False False True False
                                     False,
                                    Char False False True True True True False
                                      False,
                                    Char True False True True True True False
                                      False,
                                    Char False False False False False True
                                      False False] ++
                                    show_num a);
                         Lt a ->
                           Just (show_clock i ++
                                  [Char False False False False False True False
                                     False,
                                    Char False False True True True True False
                                      False,
                                    Char False False False False False True
                                      False False] ++
                                    show_num a);
                         INF -> Nothing;
                       })
                  else (case e of {
                         Le a ->
                           Just (show_clock i ++
                                  [Char False False False False False True False
                                     False,
                                    Char True False True True False True False
                                      False,
                                    Char False False False False False True
                                      False False] ++
                                    show_clock j ++
                                      [Char False False False False False True
 False False,
Char False False True True True True False False,
Char True False True True True True False False,
Char False False False False False True False False] ++
show_num a);
                         Lt a ->
                           Just (show_clock i ++
                                  [Char False False False False False True False
                                     False,
                                    Char True False True True False True False
                                      False,
                                    Char False False False False False True
                                      False False] ++
                                    show_clock j ++
                                      [Char False False False False False True
 False False,
Char False False True True True True False False,
Char False False False False False True False False] ++
show_num a);
                         INF -> Nothing;
                       }))));

geta :: forall a b. (Showa a) => (a -> Maybe b) -> a -> Result b;
geta m x =
  (case m x of {
    Nothing ->
      Error ["(Get) key not found: " ++ implode (shows_prec zero_nat x [])];
    Just a -> Result a;
  });

norm_upd_impl ::
  forall a.
    (Linordered_ab_group_add a, Eq a,
      Heapa a) => Nat ->
                    Heap.STArray Heap.RealWorld (DBMEntry a) ->
                      IArray.IArray a ->
                        Nat ->
                          Heap.ST Heap.RealWorld
                            (Heap.STArray Heap.RealWorld (DBMEntry a));
norm_upd_impl n =
  (\ ai bia bi ->
    do { 
      x <- mtx_get (suc n) ai (zero_nat, zero_nat);
      xa <- mtx_set (suc n) ai (zero_nat, zero_nat) (norm_diag x);
      imp_for_inta one_nat (suc bi)
        (\ xc sigma ->
          do { 
            xb <- mtx_get (suc n) sigma (zero_nat, xc);
            mtx_set (suc n) sigma (zero_nat, xc)
              (norm_lower (norm_upper xb zero) (uminus (sub bia xc)))
           })
        xa >>=
        imp_for_inta one_nat (suc bi)
          (\ xb sigma ->
            do { 
              xc <- mtx_get (suc n) sigma (xb, zero_nat);
              mtx_set (suc n) sigma (xb, zero_nat)
                (norm_lower (norm_upper xc (sub bia xb)) (uminus zero)) >>=
                imp_for_inta one_nat (suc bi)
                  (\ xe sigmaa ->
                    (if not (equal_nat xb xe)
                      then do { 
                             xd <- mtx_get (suc n) sigmaa (xb, xe);
                             mtx_set (suc n) sigmaa (xb, xe)
                               (norm_lower (norm_upper xd (sub bia xb))
                                 (uminus (sub bia xe)))
                            }
                      else do { 
                             xd <- mtx_get (suc n) sigmaa (xb, xe);
                             mtx_set (suc n) sigmaa (xb, xe) (norm_diag xd)
                            }))
             })
     });

dbm_list_to_string ::
  forall a.
    (Linordered_ab_group_add a, Eq a,
      Heapa a) => Nat ->
                    (Nat -> [Char]) -> (a -> [Char]) -> [DBMEntry a] -> [Char];
dbm_list_to_string n show_clock show_num xs =
  app ((((concat .
           intersperse
             [Char False False True True False True False False,
               Char False False False False False True False False]) .
          reverse) .
         snd) .
        snd)
    (fold (\ e (i, (j, acc)) ->
            let {
              v = make_string show_clock show_num e i j;
              ja = modulo_nat (plus_nat j one_nat) (plus_nat n one_nat);
              ia = (if equal_nat ja zero_nat then plus_nat i one_nat else i);
            } in (case v of {
                   Nothing -> (ia, (ja, acc));
                   Just s -> (ia, (ja, s : acc));
                 }))
      xs (zero_nat, (zero_nat, [])));

dbm_to_list_impl ::
  forall a.
    (Linordered_ab_monoid_add a,
      Heapa a) => Nat ->
                    Heap.STArray Heap.RealWorld a -> Heap.ST Heap.RealWorld [a];
dbm_to_list_impl n =
  (\ xi ->
    do { 
      x <- imp_for_inta zero_nat (suc n)
             (\ xc ->
               imp_for_inta zero_nat (suc n)
                 (\ xe sigma -> do { 
                                  x_e <- mtx_get (suc n) xi (xc, xe);
                                  return (x_e : sigma)
                                 }))
             [];
      return (op_list_rev x)
     });

show_dbm_impl ::
  forall a.
    (Linordered_ab_group_add a, Eq a,
      Heapa a) => Nat ->
                    (Nat -> [Char]) ->
                      (a -> [Char]) ->
                        Heap.STArray Heap.RealWorld (DBMEntry a) ->
                          Heap.ST Heap.RealWorld [Char];
show_dbm_impl n show_clock show_num =
  (\ xi -> do { 
             x <- dbm_to_list_impl n xi;
             return (dbm_list_to_string n show_clock show_num x)
            });

scan_parens ::
  forall a.
    [Char] ->
      [Char] ->
        (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
          Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char);
scan_parens lparen rparen inner =
  bindb (gen_token lx_ws (exactly lparen))
    (\ _ ->
      bindb (gen_token lx_ws inner)
        (\ a -> bindb (gen_token lx_ws (exactly rparen)) (\ _ -> returna a)));

lx_underscore ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
lx_underscore =
  bindb (exactly [Char True True True True True False True False])
    (\ _ -> returna (Char True True True True True False True False));

lx_hyphen ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Char, Len_list Char);
lx_hyphen =
  bindb (exactly [Char True False True True False True False False])
    (\ _ -> returna (Char True False True True False True False False));

ta_var_ident ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
ta_var_ident =
  bindb (alt (bindb (alt lx_alpha lx_digit) (\ x -> returna (sum_join x)))
          lx_underscore)
    (\ x ->
      bindb (repeat
              (bindb
                (alt (bindb (alt lx_alpha lx_digit)
                       (\ xa -> returna (sum_join xa)))
                  (bindb (alt lx_underscore lx_hyphen)
                    (\ xa -> returna (sum_join xa))))
                (\ xa -> returna (sum_join xa))))
        (\ xa -> returna (uncurry (\ a b -> a : b) (sum_join x, xa))));

scan_var ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) ([Char], Len_list Char);
scan_var = ta_var_ident;

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

scan_infix_pair ::
  forall a b.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      (Len_list Char -> Sum (() -> [Char] -> [Char]) (b, Len_list Char)) ->
        [Char] ->
          Len_list Char -> Sum (() -> [Char] -> [Char]) ((a, b), Len_list Char);
scan_infix_pair a b s =
  bindb (gen_token lx_ws a)
    (\ aa ->
      bindb (gen_token lx_ws (exactly s))
        (\ _ -> bindb (gen_token lx_ws b) (\ ba -> returna (aa, ba))));

aexp ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Exp String Int, Len_list Char);
aexp l =
  bindb (alt (bindb (gen_token lx_ws lx_int) (\ x -> returna (Const x)))
          (bindb
            (alt (bindb (gen_token lx_ws scan_var)
                   (\ x -> returna ((Var . implode) x)))
              (bindb
                (alt (bindb
                       (scan_parens
                         [Char False False False True False True False False]
                         [Char True False False True False True False False]
                         (bindb (gen_token lx_ws scan_exp)
                           (\ a ->
                             bindb (gen_token lx_ws
                                     (exactly
                                       [Char True True True True True True False
  False]))
                               (\ _ ->
                                 bindb (gen_token lx_ws scan_7)
                                   (\ x ->
                                     bindb (gen_token lx_ws
     (exactly [Char False True False True True True False False]))
                                       (\ _ ->
 bindb scan_exp (\ xa -> returna (a, (x, xa)))))))))
                       (\ x -> returna (case x of {
 (e1, (b, a)) -> If_then_else b e1 a;
                                       })))
                  (bindb (gen_token lx_ws tk_lparen)
                    (\ _ ->
                      bindb (gen_token lx_ws scan_exp)
                        (\ a -> bindb tk_rparen (\ _ -> returna a)))))
                (\ x -> returna (sum_join x))))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x)) l;

mexp ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Exp String Int, Len_list Char);
mexp l =
  chainL1 aexp
    (bindb
      (alt (bindb tk_times (\ _ -> returna times_int))
        (bindb tk_div (\ _ -> returna divide_int)))
      (\ x -> returna (Binop (sum_join x))))
    l;

scan_exp ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Exp String Int, Len_list Char);
scan_exp l =
  chainL1 mexp
    (bindb
      (alt (bindb tk_plus (\ _ -> returna plus_int))
        (bindb tk_minus (\ _ -> returna minus_int)))
      (\ x -> returna (Binop (sum_join x))))
    l;

scan_0 ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) (Bexp String Int, Len_list Char);
scan_0 l =
  bindb (alt (bindb
               (gen_token lx_ws
                 (bindb
                   (alt (exactly
                          [Char False True True True True True True False])
                     (exactly
                       [Char True False False False False True False False]))
                   (\ x -> returna (sum_join x))))
               (\ _ ->
                 bindb (scan_parens
                         [Char False False False True False True False False]
                         [Char True False False True False True False False]
                         scan_7)
                   (\ x -> returna (Not x))))
          (bindb
            (alt (bindb
                   (gen_token lx_ws
                     (exactly
                       [Char False False True False True True True False,
                         Char False True False False True True True False,
                         Char True False True False True True True False,
                         Char True False True False False True True False]))
                   (\ _ -> returna Truea))
              (bindb
                (alt (bindb
                       (scan_infix_pair aexp aexp
                         [Char False False True True True True False False,
                           Char True False True True True True False False])
                       (\ x -> returna (uncurry Lea x)))
                  (bindb
                    (alt (bindb
                           (scan_infix_pair aexp aexp
                             [Char False False True True True True False False])
                           (\ x -> returna (uncurry Lta x)))
                      (bindb
                        (alt (bindb
                               (scan_infix_pair aexp aexp
                                 [Char True False True True True True False
                                    False,
                                   Char True False True True True True False
                                     False])
                               (\ x -> returna (uncurry Eqa x)))
                          (bindb
                            (alt (bindb
                                   (scan_infix_pair aexp aexp
                                     [Char False True True True True True False
False])
                                   (\ x -> returna (uncurry Gt x)))
                              (bindb
                                (alt (bindb
                                       (scan_infix_pair aexp aexp
 [Char False True True True True True False False,
   Char True False True True True True False False])
                                       (\ x -> returna (uncurry Ge x)))
                                  (scan_parens
                                    [Char False False False True False True
                                       False False]
                                    [Char True False False True False True False
                                       False]
                                    scan_7))
                                (\ x -> returna (sum_join x))))
                            (\ x -> returna (sum_join x))))
                        (\ x -> returna (sum_join x))))
                    (\ x -> returna (sum_join x))))
                (\ x -> returna (sum_join x))))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x)) l;

scan_6 ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) (Bexp String Int, Len_list Char);
scan_6 l =
  bindb (alt (bindb
               (scan_infix_pair scan_0 scan_6
                 [Char False True True False False True False False,
                   Char False True True False False True False False])
               (\ x -> returna (uncurry And x)))
          scan_0)
    (\ x -> returna (sum_join x)) l;

scan_7 ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) (Bexp String Int, Len_list Char);
scan_7 l =
  bindb (alt (bindb
               (scan_infix_pair scan_6 scan_7
                 [Char True False True True False True False False,
                   Char False True True True True True False False])
               (\ x -> returna (uncurry Imply x)))
          (bindb
            (alt (bindb
                   (scan_infix_pair scan_6 scan_7
                     [Char False False True True True True True False,
                       Char False False True True True True True False])
                   (\ x -> returna (uncurry Or x)))
              scan_6)
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x)) l;

vars_of_exp :: forall a b. (Eq a) => Exp a b -> Set a;
vars_of_exp (Const c) = bot_set;
vars_of_exp (Var x) = insert x bot_set;
vars_of_exp (If_then_else b e1 e2) =
  sup_set (sup_set (vars_of_bexp b) (vars_of_exp e1)) (vars_of_exp e2);
vars_of_exp (Binop uu e1 e2) = sup_set (vars_of_exp e1) (vars_of_exp e2);
vars_of_exp (Unop uv e) = vars_of_exp e;

vars_of_bexp :: forall a b. (Eq a) => Bexp a b -> Set a;
vars_of_bexp (Not e) = vars_of_bexp e;
vars_of_bexp (And e1 e2) = sup_set (vars_of_bexp e1) (vars_of_bexp e2);
vars_of_bexp (Or e1 e2) = sup_set (vars_of_bexp e1) (vars_of_bexp e2);
vars_of_bexp (Imply e1 e2) = sup_set (vars_of_bexp e1) (vars_of_bexp e2);
vars_of_bexp (Eqa i x) = sup_set (vars_of_exp i) (vars_of_exp x);
vars_of_bexp (Lea i x) = sup_set (vars_of_exp i) (vars_of_exp x);
vars_of_bexp (Lta i x) = sup_set (vars_of_exp i) (vars_of_exp x);
vars_of_bexp (Ge i x) = sup_set (vars_of_exp i) (vars_of_exp x);
vars_of_bexp (Gt i x) = sup_set (vars_of_exp i) (vars_of_exp x);
vars_of_bexp Truea = bot_set;

parse ::
  forall a.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      String -> Result a;
parse parser s =
  (case parse_all lx_ws parser s of {
    Inl e ->
      Error [implode
               (e () [Char False False False False True False True False,
                       Char True False False False False True True False,
                       Char False True False False True True True False,
                       Char True True False False True True True False,
                       Char True False True False False True True False,
                       Char False True False False True True True False,
                       Char False True False True True True False False,
                       Char False False False False False True False False])];
    Inr a -> Result a;
  });

default_map_of :: forall a b. (Eq b) => a -> [(b, a)] -> b -> a;
default_map_of a xs = map_default a (map_of xs);

automaton_of ::
  forall a b c d e.
    (Eq d) => ([a], ([b], ([c], [(d, [e])]))) ->
                (Set a, (Set b, (Set c, d -> [e])));
automaton_of =
  (\ (committed, (urgent, (trans, inv))) ->
    (Set committed, (Set urgent, (Set trans, default_map_of [] inv))));

bvali :: forall a. (Eq a, Linorder a) => [a] -> Bexp Nat a -> Bool;
bvali s Truea = True;
bvali s (Not e) = not (bvali s e);
bvali s (And e1 e2) = bvali s e1 && bvali s e2;
bvali s (Or e1 e2) = bvali s e1 || bvali s e2;
bvali s (Imply e1 e2) = (if bvali s e1 then bvali s e2 else True);
bvali s (Eqa i x) = evali s i == evali s x;
bvali s (Lea i x) = less_eq (evali s i) (evali s x);
bvali s (Lta i x) = less (evali s i) (evali s x);
bvali s (Ge i x) = less_eq (evali s x) (evali s i);
bvali s (Gt i x) = less (evali s x) (evali s i);

evali :: forall a. (Eq a, Linorder a) => [a] -> Exp Nat a -> a;
evali s (Const c) = c;
evali s (Var x) = nth s x;
evali s (If_then_else b e1 e2) = (if bvali s b then evali s e1 else evali s e2);
evali s (Binop f e1 e2) = f (evali s e1) (evali s e2);
evali s (Unop f e) = f (evali s e);

map_sexp ::
  forall a b c d e f.
    (Nat -> a -> b) -> (c -> d) -> (e -> f) -> Sexp Nat a c e -> Sexp Nat b d f;
map_sexp uu uv uw Trueb = Trueb;
map_sexp f g h (Nota e) = Nota (map_sexp f g h e);
map_sexp f g h (Anda e1 e2) = Anda (map_sexp f g h e1) (map_sexp f g h e2);
map_sexp f g h (Ora e1 e2) = Ora (map_sexp f g h e1) (map_sexp f g h e2);
map_sexp f g h (Implya e1 e2) = Implya (map_sexp f g h e1) (map_sexp f g h e2);
map_sexp f g h (Eqb i x) = Eqb (g i) (h x);
map_sexp f g h (Ltb i x) = Ltb (g i) (h x);
map_sexp f g h (Leb i x) = Leb (g i) (h x);
map_sexp f g h (Gea i x) = Gea (g i) (h x);
map_sexp f g h (Gta i x) = Gta (g i) (h x);
map_sexp f g h (Loc i x) = Loc i (f i x);

mk_st_string :: String -> String -> String;
mk_st_string s1 s2 = ((("<" ++ s1) ++ ", ") ++ s2) ++ ">";

calc_shortest_scc_paths ::
  forall a.
    (Plus a, Zero a,
      Ord a) => Gen_g_impl_ext (Nat -> Bool) (Nat -> [Nat]) [Nat]
                  (Nat -> Nat -> a) ->
                  Nat -> [Maybe a];
calc_shortest_scc_paths g n =
  let {
    sccs = compute_SCC_tra g;
    d = replicate n Nothing ++ [Just zero];
    da = fold (fold (\ u ->
                      fold (\ v da ->
                             (case nth da u of {
                               Nothing -> da;
                               Just du ->
                                 (case nth da v of {
                                   Nothing ->
                                     list_update da v
                                       (Just (plus du (more g u v)));
                                   Just dv ->
                                     (if less (plus du (more g u v)) dv
                                       then list_update da v
      (Just (plus du (more g u v)))
                                       else da);
                                 });
                             }))
                        (gi_E g u)))
           sccs d;
    db = fold (\ vs db ->
                let {
                  dscc =
                    fold (\ v dscc ->
                           (case dscc of {
                             Nothing -> nth db v;
                             Just daa -> (case nth db v of {
   Nothing -> dscc;
   Just dv -> Just (min dv daa);
 });
                           }))
                      vs Nothing;
                } in fold (\ v dc -> list_update dc v dscc) vs db)
           sccs da;
  } in db;

of_nat :: JSON -> Result Nat;
of_nat json = (case json of {
                Object _ -> Error ["of_nat: expected natural number"];
                Arraya _ -> Error ["of_nat: expected natural number"];
                Stringa _ -> Error ["of_nat: expected natural number"];
                Int _ -> Error ["of_nat: expected natural number"];
                Nata a -> Result a;
                Rat _ -> Error ["of_nat: expected natural number"];
                Boolean _ -> Error ["of_nat: expected natural number"];
                Null -> Error ["of_nat: expected natural number"];
              });

find_remove :: forall a. (a -> Bool) -> [a] -> Maybe (a, [a]);
find_remove p = map_option (\ (xs, (x, ys)) -> (x, xs ++ ys)) . extract p;

merge_pairs :: forall a b. (Eq a) => [(a, [b])] -> [(a, [b])] -> [(a, [b])];
merge_pairs [] ys = ys;
merge_pairs ((k, v) : xs) ys =
  (case find_remove (\ (ka, _) -> ka == k) ys of {
    Nothing -> (k, v) : merge_pairs xs ys;
    Just ((_, va), ysa) -> (k, v ++ va) : merge_pairs xs ysa;
  });

conv_urge ::
  forall a b c d e f g h i j k.
    (Eq c,
      Zero j) => a -> (b, ([c], ([(d, (e, (f, (g, (h, ([a], i))))))],
                                  [(c, [Acconstraint a j])]))) ->
                        (b, ([k], ([(d, (e, (f, (g, (h, ([a], i))))))],
                                    [(c, [Acconstraint a j])])));
conv_urge urge =
  (\ (committed, (urgent, (trans, inv))) ->
    (committed,
      ([], (map (\ (l, (b, (g, (a, (f, (r, la)))))) ->
                  (l, (b, (g, (a, (f, (urge : r, la)))))))
              trans,
             merge_pairs (map (\ l -> (l, [LE urge zero])) urgent) inv))));

dbm_subset_impl ::
  forall a.
    (Linordered_cancel_ab_monoid_add a, Eq a,
      Heapa a) => Nat ->
                    Heap.STArray Heap.RealWorld (DBMEntry a) ->
                      Heap.STArray Heap.RealWorld (DBMEntry a) ->
                        Heap.ST Heap.RealWorld Bool;
dbm_subset_impl n =
  (\ ai bi ->
    imp_for_int zero_nat (suc n) return
      (\ xb _ ->
        imp_for_int zero_nat (suc n) return
          (\ xe _ -> do { 
                       x_f <- mtx_get (suc n) ai (xb, xe);
                       x_g <- mtx_get (suc n) bi (xb, xe);
                       return (less_eq_DBMEntry x_f x_g)
                      })
          True)
      True);

map_sexpa ::
  forall a b c d e f g h.
    (a -> b) ->
      (c -> d) -> (e -> f) -> (g -> h) -> Sexp a c e g -> Sexp b d f h;
map_sexpa f1 f2 f3 f4 Trueb = Trueb;
map_sexpa f1 f2 f3 f4 (Nota x2) = Nota (map_sexpa f1 f2 f3 f4 x2);
map_sexpa f1 f2 f3 f4 (Anda x31 x32) =
  Anda (map_sexpa f1 f2 f3 f4 x31) (map_sexpa f1 f2 f3 f4 x32);
map_sexpa f1 f2 f3 f4 (Ora x41 x42) =
  Ora (map_sexpa f1 f2 f3 f4 x41) (map_sexpa f1 f2 f3 f4 x42);
map_sexpa f1 f2 f3 f4 (Implya x51 x52) =
  Implya (map_sexpa f1 f2 f3 f4 x51) (map_sexpa f1 f2 f3 f4 x52);
map_sexpa f1 f2 f3 f4 (Eqb x61 x62) = Eqb (f3 x61) (f4 x62);
map_sexpa f1 f2 f3 f4 (Leb x71 x72) = Leb (f3 x71) (f4 x72);
map_sexpa f1 f2 f3 f4 (Ltb x81 x82) = Ltb (f3 x81) (f4 x82);
map_sexpa f1 f2 f3 f4 (Gea x91 x92) = Gea (f3 x91) (f4 x92);
map_sexpa f1 f2 f3 f4 (Gta x101 x102) = Gta (f3 x101) (f4 x102);
map_sexpa f1 f2 f3 f4 (Loc x111 x112) = Loc (f1 x111) (f2 x112);

map_formulaa ::
  forall a b c d e f g h.
    (a -> b) ->
      (c -> d) -> (e -> f) -> (g -> h) -> Formula a c e g -> Formula b d f h;
map_formulaa f1 f2 f3 f4 (EX x1) = EX (map_sexpa f1 f2 f3 f4 x1);
map_formulaa f1 f2 f3 f4 (EG x2) = EG (map_sexpa f1 f2 f3 f4 x2);
map_formulaa f1 f2 f3 f4 (AX x3) = AX (map_sexpa f1 f2 f3 f4 x3);
map_formulaa f1 f2 f3 f4 (AG x4) = AG (map_sexpa f1 f2 f3 f4 x4);
map_formulaa f1 f2 f3 f4 (Leadsto x51 x52) =
  Leadsto (map_sexpa f1 f2 f3 f4 x51) (map_sexpa f1 f2 f3 f4 x52);

rename_locs_sexp ::
  forall a b c d e.
    (a -> b -> Result c) -> Sexp a b d e -> Result (Sexp a c d e);
rename_locs_sexp f (Nota a) =
  binda (rename_locs_sexp f a) (\ aa -> Result (Nota aa));
rename_locs_sexp f (Implya a b) =
  binda (rename_locs_sexp f a)
    (\ aa -> binda (rename_locs_sexp f b) (\ ba -> Result (Implya aa ba)));
rename_locs_sexp f (Ora a b) =
  binda (rename_locs_sexp f a)
    (\ aa -> binda (rename_locs_sexp f b) (\ ba -> Result (Ora aa ba)));
rename_locs_sexp f (Anda a b) =
  binda (rename_locs_sexp f a)
    (\ aa -> binda (rename_locs_sexp f b) (\ ba -> Result (Anda aa ba)));
rename_locs_sexp f (Loc n x) = binda (f n x) (\ xa -> Result (Loc n xa));
rename_locs_sexp f (Eqb a b) = Result (Eqb a b);
rename_locs_sexp f (Ltb a b) = Result (Ltb a b);
rename_locs_sexp f (Leb a b) = Result (Leb a b);
rename_locs_sexp f (Gea a b) = Result (Gea a b);
rename_locs_sexp f (Gta a b) = Result (Gta a b);

rename_locs_formula ::
  forall a b c d e.
    (a -> b -> Result c) -> Formula a b d e -> Result (Formula a c d e);
rename_locs_formula f (EX phi) = binda (rename_locs_sexp f phi) (Result . EX);
rename_locs_formula f (EG phi) = binda (rename_locs_sexp f phi) (Result . EG);
rename_locs_formula f (AX phi) = binda (rename_locs_sexp f phi) (Result . AX);
rename_locs_formula f (AG phi) = binda (rename_locs_sexp f phi) (Result . AG);
rename_locs_formula f (Leadsto phi psi) =
  binda (rename_locs_sexp f phi)
    (\ phia ->
      binda (rename_locs_sexp f psi) (\ psia -> Result (Leadsto phia psia)));

locs_of_sexp :: forall a b c d. (Eq a) => Sexp a b c d -> Set a;
locs_of_sexp (Nota e) = locs_of_sexp e;
locs_of_sexp (Anda e1 e2) = sup_set (locs_of_sexp e1) (locs_of_sexp e2);
locs_of_sexp (Ora e1 e2) = sup_set (locs_of_sexp e1) (locs_of_sexp e2);
locs_of_sexp (Implya e1 e2) = sup_set (locs_of_sexp e1) (locs_of_sexp e2);
locs_of_sexp (Loc i x) = insert i bot_set;
locs_of_sexp Trueb = bot_set;
locs_of_sexp (Eqb v va) = bot_set;
locs_of_sexp (Leb v va) = bot_set;
locs_of_sexp (Ltb v va) = bot_set;
locs_of_sexp (Gea v va) = bot_set;
locs_of_sexp (Gta v va) = bot_set;

locs_of_formula :: forall a b c d. (Eq a) => Formula a b c d -> Set a;
locs_of_formula (EX phi) = locs_of_sexp phi;
locs_of_formula (EG phi) = locs_of_sexp phi;
locs_of_formula (AX phi) = locs_of_sexp phi;
locs_of_formula (AG phi) = locs_of_sexp phi;
locs_of_formula (Leadsto phi psi) =
  sup_set (locs_of_sexp phi) (locs_of_sexp psi);

sexp_to_acconstraint ::
  Sexp String String String Int -> Acconstraint String Int;
sexp_to_acconstraint (Ltb a b) = LT a b;
sexp_to_acconstraint (Leb a b) = LE a b;
sexp_to_acconstraint (Eqb a b) = EQ a b;
sexp_to_acconstraint (Gea a b) = GE a b;
sexp_to_acconstraint (Gta a b) = GT a b;

sexp_to_bexp :: Sexp String String String Int -> Result (Bexp String Int);
sexp_to_bexp (Ltb a b) = Result (Lta (Var a) (Const b));
sexp_to_bexp (Leb a b) = Result (Lea (Var a) (Const b));
sexp_to_bexp (Eqb a b) = Result (Eqa (Var a) (Const b));
sexp_to_bexp (Gea a b) = Result (Ge (Var a) (Const b));
sexp_to_bexp (Gta a b) = Result (Gt (Var a) (Const b));
sexp_to_bexp (Anda a b) =
  binda (sexp_to_bexp a)
    (\ aa -> binda (sexp_to_bexp b) (\ ba -> Result (And aa ba)));
sexp_to_bexp (Ora a b) =
  binda (sexp_to_bexp a)
    (\ aa -> binda (sexp_to_bexp b) (\ ba -> Result (Or aa ba)));
sexp_to_bexp (Implya a b) =
  binda (sexp_to_bexp a)
    (\ aa -> binda (sexp_to_bexp b) (\ ba -> Result (Imply aa ba)));
sexp_to_bexp Trueb = Error ["Illegal construct in binary operation"];
sexp_to_bexp (Nota v) = Error ["Illegal construct in binary operation"];
sexp_to_bexp (Loc v va) = Error ["Illegal construct in binary operation"];

chop_sexp ::
  forall a b c d e f.
    (Eq a) => [a] ->
                Sexp b c a d ->
                  ([Sexp e f a d], [Sexp b c a d]) ->
                    ([Sexp e f a d], [Sexp b c a d]);
chop_sexp clocks (Anda a b) (cs, es) =
  chop_sexp clocks b (chop_sexp clocks a (cs, es));
chop_sexp clocks (Eqb a b) (cs, es) =
  (if membera clocks a then (Eqb a b : cs, es) else (cs, Eqb a b : es));
chop_sexp clocks (Leb a b) (cs, es) =
  (if membera clocks a then (Leb a b : cs, es) else (cs, Leb a b : es));
chop_sexp clocks (Ltb a b) (cs, es) =
  (if membera clocks a then (Ltb a b : cs, es) else (cs, Ltb a b : es));
chop_sexp clocks (Gea a b) (cs, es) =
  (if membera clocks a then (Gea a b : cs, es) else (cs, Gea a b : es));
chop_sexp clocks (Gta a b) (cs, es) =
  (if membera clocks a then (Gta a b : cs, es) else (cs, Gta a b : es));
chop_sexp clocks Trueb (cs, es) = (cs, Trueb : es);
chop_sexp clocks (Nota v) (cs, es) = (cs, Nota v : es);
chop_sexp clocks (Ora v va) (cs, es) = (cs, Ora v va : es);
chop_sexp clocks (Implya v va) (cs, es) = (cs, Implya v va : es);
chop_sexp clocks (Loc v va) (cs, es) = (cs, Loc v va : es);

compile_invariant ::
  [String] ->
    [String] ->
      Sexp String String String Int ->
        Result ([Acconstraint String Int], Bexp String Int);
compile_invariant clocks vars inv =
  (case chop_sexp clocks inv ([], []) of {
    (cs, es) ->
      let {
        g = map sexp_to_acconstraint cs;
      } in (if null es then Result (g, Truea)
             else let {
                    e = fold Anda (tl es) (hd es);
                  } in binda (sexp_to_bexp e)
                         (\ b ->
                           binda (assert (less_eq_set (set_bexp b) (Set vars))
                                   (implode
                                     ([Char True False True False True False
 True False,
Char False True True True False True True False,
Char True True False True False True True False,
Char False True True True False True True False,
Char True True True True False True True False,
Char True True True False True True True False,
Char False True True True False True True False,
Char False False False False False True False False,
Char False True True False True True True False,
Char True False False False False True True False,
Char False True False False True True True False,
Char True False False True False True True False,
Char True False False False False True True False,
Char False True False False False True True False,
Char False False True True False True True False,
Char True False True False False True True False,
Char False False False False False True False False,
Char True False False True False True True False,
Char False True True True False True True False,
Char False False False False False True False False,
Char False True False False False True True False,
Char True False True False False True True False,
Char False False False True True True True False,
Char False False False False True True True False,
Char False True False True True True False False,
Char False False False False False True False False] ++
                                       shows_prec_bexp zero_nat b [])))
                             (\ _ -> Result (g, b))));
  });

scan_acconstraint ::
  forall a b.
    Len_list Char ->
      Sum (() -> [Char] -> [Char]) (Sexp a b String Int, Len_list Char);
scan_acconstraint =
  bindb (alt (bindb (gen_token lx_ws scan_var)
               (\ x ->
                 bindb (gen_token lx_ws
                         (exactly
                           [Char False False True True True True False False]))
                   (\ _ ->
                     bindb (gen_token lx_ws lx_int)
                       (\ xa -> returna (Ltb (implode x) xa)))))
          (bindb
            (alt (bindb (gen_token lx_ws scan_var)
                   (\ x ->
                     bindb (gen_token lx_ws
                             (exactly
                               [Char False False True True True True False
                                  False,
                                 Char True False True True True True False
                                   False]))
                       (\ _ ->
                         bindb (gen_token lx_ws lx_int)
                           (\ xa -> returna (Leb (implode x) xa)))))
              (bindb
                (alt (bindb (gen_token lx_ws scan_var)
                       (\ x ->
                         bindb (gen_token lx_ws
                                 (exactly
                                   [Char True False True True True True False
                                      False,
                                     Char True False True True True True False
                                       False]))
                           (\ _ ->
                             bindb (gen_token lx_ws lx_int)
                               (\ xa -> returna (Eqb (implode x) xa)))))
                  (bindb
                    (alt (bindb (gen_token lx_ws scan_var)
                           (\ x ->
                             bindb (gen_token lx_ws
                                     (exactly
                                       [Char True False True True True True
  False False]))
                               (\ _ ->
                                 bindb (gen_token lx_ws lx_int)
                                   (\ xa -> returna (Eqb (implode x) xa)))))
                      (bindb
                        (alt (bindb (gen_token lx_ws scan_var)
                               (\ x ->
                                 bindb (gen_token lx_ws
 (exactly
   [Char False True True True True True False False,
     Char True False True True True True False False]))
                                   (\ _ ->
                                     bindb (gen_token lx_ws lx_int)
                                       (\ xa -> returna (Gea (implode x) xa)))))
                          (bindb (gen_token lx_ws scan_var)
                            (\ x ->
                              bindb (gen_token lx_ws
                                      (exactly
[Char False True True True True True False False]))
                                (\ _ ->
                                  bindb (gen_token lx_ws lx_int)
                                    (\ xa -> returna (Gta (implode x) xa))))))
                        (\ x -> returna (sum_join x))))
                    (\ x -> returna (sum_join x))))
                (\ x -> returna (sum_join x))))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x));

scan_loc ::
  forall a b.
    Len_list Char ->
      Sum (() -> [Char] -> [Char]) (Sexp String String a b, Len_list Char);
scan_loc =
  bindb (gen_token lx_ws scan_var)
    (\ x ->
      bindb (exactly [Char False True True True False True False False])
        (\ _ ->
          bindb scan_var (\ xa -> returna (Loc (implode x) (implode xa)))));

scan_bexp_elem ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) (Sexp String String String Int, Len_list Char);
scan_bexp_elem =
  bindb (alt scan_acconstraint scan_loc) (\ x -> returna (sum_join x));

scan_7a ::
  forall a.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      (a -> a -> a) ->
        (a -> a -> a) ->
          (a -> a -> a) ->
            (a -> a) ->
              Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char);
scan_7a elem imply or and nota l =
  bindb (alt (bindb
               (scan_infix_pair (scan_6a elem imply or and nota)
                 (scan_7a elem imply or and nota)
                 [Char True False True True False True False False,
                   Char False True True True True True False False])
               (\ x -> returna (uncurry imply x)))
          (bindb
            (alt (bindb
                   (scan_infix_pair (scan_6a elem imply or and nota)
                     (scan_7a elem imply or and nota)
                     [Char False False True True True True True False,
                       Char False False True True True True True False])
                   (\ x -> returna (uncurry or x)))
              (scan_6a elem imply or and nota))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x)) l;

scan_0a ::
  forall a.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      (a -> a -> a) ->
        (a -> a -> a) ->
          (a -> a -> a) ->
            (a -> a) ->
              Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char);
scan_0a elem imply or and nota l =
  bindb (alt (bindb
               (gen_token lx_ws
                 (bindb
                   (alt (exactly
                          [Char False True True True True True True False])
                     (exactly
                       [Char True False False False False True False False]))
                   (\ x -> returna (sum_join x))))
               (\ _ ->
                 bindb (scan_parens
                         [Char False False False True False True False False]
                         [Char True False False True False True False False]
                         (scan_7a elem imply or and nota))
                   (\ x -> returna (nota x))))
          (bindb
            (alt elem
              (scan_parens [Char False False False True False True False False]
                [Char True False False True False True False False]
                (scan_7a elem imply or and nota)))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x)) l;

scan_6a ::
  forall a.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      (a -> a -> a) ->
        (a -> a -> a) ->
          (a -> a -> a) ->
            (a -> a) ->
              Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char);
scan_6a elem imply or and nota l =
  bindb (alt (bindb
               (scan_infix_pair (scan_0a elem imply or and nota)
                 (scan_6a elem imply or and nota)
                 [Char False True True False False True False False,
                   Char False True True False False True False False])
               (\ x -> returna (uncurry and x)))
          (scan_0a elem imply or and nota))
    (\ x -> returna (sum_join x)) l;

compile_invarianta ::
  [String] ->
    [String] -> String -> Result ([Acconstraint String Int], Bexp String Int);
compile_invarianta clocks vars inv =
  (if inv == "" then Result ([], Truea)
    else binda (err_msg ("Failed to parse guard in " ++ inv)
                 (parse (scan_7a scan_bexp_elem Implya Ora Anda Nota) inv))
           (compile_invariant clocks vars));

of_string :: JSON -> Result String;
of_string json = (case json of {
                   Object _ -> Error ["of_array: expected sequence"];
                   Arraya _ -> Error ["of_array: expected sequence"];
                   Stringa s -> Result (implode s);
                   Int _ -> Error ["of_array: expected sequence"];
                   Nata _ -> Error ["of_array: expected sequence"];
                   Rat _ -> Error ["of_array: expected sequence"];
                   Boolean _ -> Error ["of_array: expected sequence"];
                   Null -> Error ["of_array: expected sequence"];
                 });

of_object :: JSON -> Result ([Char] -> Maybe JSON);
of_object json = (case json of {
                   Object asa -> Result (map_of asa);
                   Arraya _ -> Error ["json_to_map: expected object"];
                   Stringa _ -> Error ["json_to_map: expected object"];
                   Int _ -> Error ["json_to_map: expected object"];
                   Nata _ -> Error ["json_to_map: expected object"];
                   Rat _ -> Error ["json_to_map: expected object"];
                   Boolean _ -> Error ["json_to_map: expected object"];
                   Null -> Error ["json_to_map: expected object"];
                 });

convert_node ::
  [String] ->
    [String] -> JSON -> Result ((String, Nat), [Acconstraint String Int]);
convert_node clocks vars n =
  binda (of_object n)
    (\ na ->
      binda (binda
              (geta na
                [Char True False False True False True True False,
                  Char False False True False False True True False])
              of_nat)
        (\ ida ->
          binda (binda
                  (geta na
                    [Char False True True True False True True False,
                      Char True False False False False True True False,
                      Char True False True True False True True False,
                      Char True False True False False True True False])
                  of_string)
            (\ name ->
              binda (binda
                      (geta na
                        [Char True False False True False True True False,
                          Char False True True True False True True False,
                          Char False True True False True True True False,
                          Char True False False False False True True False,
                          Char False True False False True True True False,
                          Char True False False True False True True False,
                          Char True False False False False True True False,
                          Char False True True True False True True False,
                          Char False False True False True True True False])
                      of_string)
                (\ inv ->
                  binda (err_msg "Failed to parse invariant!"
                          (compile_invarianta clocks vars inv))
                    (\ (inva, inv_vars) ->
                      binda (assert (case inv_vars of {
                                      Truea -> True;
                                      Not _ -> False;
                                      And _ _ -> False;
                                      Or _ _ -> False;
                                      Imply _ _ -> False;
                                      Eqa _ _ -> False;
                                      Lea _ _ -> False;
                                      Lta _ _ -> False;
                                      Ge _ _ -> False;
                                      Gt _ _ -> False;
                                    })
                              "State invariants on nodes are not supported")
                        (\ _ -> Result ((name, ida), inva)))))));

scan_update ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) ((String, Exp String Int), Len_list Char);
scan_update =
  bindb (gen_token lx_ws scan_var)
    (\ x ->
      bindb (gen_token lx_ws
              (bindb
                (alt (exactly [Char True False True True True True False False])
                  (exactly
                    [Char False True False True True True False False,
                      Char True False True True True True False False]))
                (\ xa -> returna (sum_join xa))))
        (\ _ -> bindb scan_exp (\ xa -> returna (implode x, xa))));

scan_action ::
  Len_list Char -> Sum (() -> [Char] -> [Char]) (Act String, Len_list Char);
scan_action =
  bindb (alt (bindb scan_var
               (\ x ->
                 bindb (gen_token lx_ws
                         (exactly
                           [Char True True True True True True False False]))
                   (\ _ -> returna ((In . implode) x))))
          (bindb
            (alt (bindb scan_var
                   (\ x ->
                     bindb (gen_token lx_ws
                             (exactly
                               [Char True False False False False True False
                                  False]))
                       (\ _ -> returna ((Out . implode) x))))
              (bindb scan_var (\ x -> returna ((Sil . implode) x))))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x));

convert_edge ::
  [String] ->
    [String] ->
      JSON ->
        Result
          (Nat, (Bexp String Int,
                  ([Acconstraint String Int],
                    (Act String,
                      ([(String, Exp String Int)], ([String], Nat))))));
convert_edge clocks vars e =
  binda (of_object e)
    (\ ea ->
      binda (binda
              (geta ea
                [Char True True False False True True True False,
                  Char True True True True False True True False,
                  Char True False True False True True True False,
                  Char False True False False True True True False,
                  Char True True False False False True True False,
                  Char True False True False False True True False])
              of_nat)
        (\ source ->
          binda (binda
                  (geta ea
                    [Char False False True False True True True False,
                      Char True False False False False True True False,
                      Char False True False False True True True False,
                      Char True True True False False True True False,
                      Char True False True False False True True False,
                      Char False False True False True True True False])
                  of_nat)
            (\ target ->
              binda (binda
                      (geta ea
                        [Char True True True False False True True False,
                          Char True False True False True True True False,
                          Char True False False False False True True False,
                          Char False True False False True True True False,
                          Char False False True False False True True False])
                      of_string)
                (\ guard ->
                  binda (binda
                          (geta ea
                            [Char False False True True False True True False,
                              Char True False False False False True True False,
                              Char False True False False False True True False,
                              Char True False True False False True True False,
                              Char False False True True False True True False])
                          of_string)
                    (\ label ->
                      binda (binda
                              (geta ea
                                [Char True False True False True True True
                                   False,
                                  Char False False False False True True True
                                    False,
                                  Char False False True False False True True
                                    False,
                                  Char True False False False False True True
                                    False,
                                  Char False False True False True True True
                                    False,
                                  Char True False True False False True True
                                    False])
                              of_string)
                        (\ update ->
                          binda (if label == "" then Result (Sil "")
                                  else err_msg
 ("Failed to parse label in " ++ label) (parse scan_action label))
                            (\ labela ->
                              binda (err_msg "Failed to parse guard!"
                                      (compile_invarianta clocks vars guard))
                                (\ (g, check) ->
                                  binda (if update == "" then Result []
  else err_msg ("Failed to parse update in " ++ update)
         (parse (parse_list scan_update) update))
                                    (\ upd ->
                                      let {
resets = filter (\ x -> membera clocks (fst x)) upd;
                                      } in
binda (assert (all (\ (_, Const x) -> equal_int x zero_int) resets)
        "Clock resets to values different from zero are not supported")
  (\ _ ->
    let {
      resetsa = map fst resets;
      upds = filter (\ x -> not (membera clocks (fst x))) upd;
    } in binda (assert (all (\ (x, _) -> membera vars x) upds)
                 ("Unknown variable in update: " ++ update))
           (\ _ ->
             Result
               (source,
                 (check, (g, (labela, (upds, (resetsa, target)))))))))))))))));

of_array :: JSON -> Result [JSON];
of_array json = (case json of {
                  Object _ -> Error ["of_array: expected sequence"];
                  Arraya a -> Result a;
                  Stringa _ -> Error ["of_array: expected sequence"];
                  Int _ -> Error ["of_array: expected sequence"];
                  Nata _ -> Error ["of_array: expected sequence"];
                  Rat _ -> Error ["of_array: expected sequence"];
                  Boolean _ -> Error ["of_array: expected sequence"];
                  Null -> Error ["of_array: expected sequence"];
                });

defaulta :: forall a. a -> Result a -> a;
defaulta def x = (case x of {
                   Result s -> s;
                   Error _ -> def;
                 });

convert_automaton ::
  [String] ->
    [String] ->
      ([Char] -> Maybe JSON) ->
        Result
          (String -> Maybe Nat,
            (Nat -> Maybe String,
              ([Nat],
                ([Nat],
                  ([(Nat, (Bexp String Int,
                            ([Acconstraint String Int],
                              (Act String,
                                ([(String, Exp String Int)],
                                  ([String], Nat))))))],
                    [(Nat, [Acconstraint String Int])])))));
convert_automaton clocks vars a =
  binda (binda
          (geta a
            [Char False True True True False True True False,
              Char True True True True False True True False,
              Char False False True False False True True False,
              Char True False True False False True True False,
              Char True True False False True True True False])
          of_array)
    (\ nodes ->
      binda (binda
              (geta a
                [Char True False True False False True True False,
                  Char False False True False False True True False,
                  Char True True True False False True True False,
                  Char True False True False False True True False,
                  Char True True False False True True True False])
              of_array)
        (\ edges ->
          binda (combine_map (convert_node clocks vars) nodes)
            (\ nodesa ->
              let {
                invs =
                  map (\ (aa, b) -> (case aa of {
                                      (_, ab) -> (\ ba -> (ab, ba));
                                    })
                                      b)
                    nodesa;
                names_to_ids = map fst nodesa;
              } in binda (assert
                           (distinct
                             (filter (\ s -> not (s == ""))
                               (map fst names_to_ids)))
                           ("Node names are ambiguous" ++
                             implode
                               (shows_prec_list zero_nat (map fst names_to_ids)
                                 [])))
                     (\ _ ->
                       binda (assert (distinct (map snd names_to_ids))
                               "Duplicate node id")
                         (\ _ ->
                           let {
                             ids_to_names = map_of (map swap names_to_ids);
                             names_to_idsa = map_of names_to_ids;
                             committed =
                               defaulta []
                                 (binda
                                   (geta a
                                     [Char True True False False False True True
False,
                                       Char True True True True False True True
 False,
                                       Char True False True True False True True
 False,
                                       Char True False True True False True True
 False,
                                       Char True False False True False True
 True False,
                                       Char False False True False True True
 True False,
                                       Char False False True False True True
 True False,
                                       Char True False True False False True
 True False,
                                       Char False False True False False True
 True False])
                                   of_array);
                           } in binda (combine_map of_nat committed)
                                  (\ committeda ->
                                    let {
                                      urgent =
defaulta []
  (binda
    (geta a
      [Char True False True False True True True False,
        Char False True False False True True True False,
        Char True True True False False True True False,
        Char True False True False False True True False,
        Char False True True True False True True False,
        Char False False True False True True True False])
    of_array);
                                    } in binda (combine_map of_nat urgent)
   (\ urgenta ->
     binda (combine_map (convert_edge clocks vars) edges)
       (\ edgesa ->
         Result
           (names_to_idsa,
             (ids_to_names, (committeda, (urgenta, (edgesa, invs)))))))))))));

trace_level :: Int -> (() -> Heap.ST Heap.RealWorld String) -> ();
trace_level i f = ();

scan_prefix ::
  forall a.
    (Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char)) ->
      [Char] ->
        Len_list Char -> Sum (() -> [Char] -> [Char]) (a, Len_list Char);
scan_prefix p head = bindb (gen_token lx_ws (exactly head)) (\ _ -> p);

scan_formula ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char])
      (Formula String String String Int, Len_list Char);
scan_formula =
  bindb (alt (bindb
               (scan_prefix (scan_7a scan_bexp_elem Implya Ora Anda Nota)
                 [Char True False True False False False True False,
                   Char False False True True True True False False,
                   Char False True True True True True False False])
               (\ x -> returna (EX x)))
          (bindb
            (alt (bindb
                   (scan_prefix (scan_7a scan_bexp_elem Implya Ora Anda Nota)
                     [Char True False True False False False True False,
                       Char True True False True True False True False,
                       Char True False True True True False True False])
                   (\ x -> returna (EG x)))
              (bindb
                (alt (bindb
                       (scan_prefix
                         (scan_7a scan_bexp_elem Implya Ora Anda Nota)
                         [Char True False False False False False True False,
                           Char False False True True True True False False,
                           Char False True True True True True False False])
                       (\ x -> returna (AX x)))
                  (bindb
                    (alt (bindb
                           (scan_prefix
                             (scan_7a scan_bexp_elem Implya Ora Anda Nota)
                             [Char True False False False False False True
                                False,
                               Char True True False True True False True False,
                               Char True False True True True False True False])
                           (\ x -> returna (AG x)))
                      (bindb
                        (scan_infix_pair
                          (scan_7a scan_bexp_elem Implya Ora Anda Nota)
                          (scan_7a scan_bexp_elem Implya Ora Anda Nota)
                          [Char True False True True False True False False,
                            Char True False True True False True False False,
                            Char False True True True True True False False])
                        (\ x -> returna (uncurry Leadsto x))))
                    (\ x -> returna (sum_join x))))
                (\ x -> returna (sum_join x))))
            (\ x -> returna (sum_join x))))
    (\ x -> returna (sum_join x));

parse_bound ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) (([Char], (Int, Int)), Len_list Char);
parse_bound =
  bindb ta_var_ident
    (\ a ->
      bindb (exactly [Char True True False True True False True False])
        (\ _ ->
          bindb lx_int
            (\ x ->
              bindb (exactly [Char False True False True True True False False])
                (\ _ ->
                  bindb lx_int
                    (\ xa ->
                      bindb (exactly
                              [Char True False True True True False True False])
                        (\ _ -> returna (a, (x, xa))))))));

parse_bounds ::
  Len_list Char ->
    Sum (() -> [Char] -> [Char]) ([(String, (Int, Int))], Len_list Char);
parse_bounds =
  bindb (alt (parse_list
               (bindb lx_ws
                 (\ _ ->
                   bindb parse_bound
                     (\ x -> returna (case x of {
                                       (s, a) -> (implode s, a);
                                     })))))
          (bindb lx_ws (\ _ -> returna [])))
    (\ x -> returna (sum_join x));

convert ::
  JSON ->
    Result
      (Nat -> Nat -> String,
        (String -> Nat,
          ([String],
            ([([Nat],
                ([Nat],
                  ([(Nat, (Bexp String Int,
                            ([Acconstraint String Int],
                              (Act String,
                                ([(String, Exp String Int)],
                                  ([String], Nat))))))],
                    [(Nat, [Acconstraint String Int])])))],
              ([(String, (Int, Int))],
                (Formula Nat Nat String Int, ([Nat], [(String, Int)])))))));
convert json =
  binda (of_object json)
    (\ alla ->
      binda (geta alla
              [Char True False False False False True True False,
                Char True False True False True True True False,
                Char False False True False True True True False,
                Char True True True True False True True False,
                Char True False True True False True True False,
                Char True False False False False True True False,
                Char False False True False True True True False,
                Char True False False False False True True False])
        (\ automata ->
          binda (of_array automata)
            (\ automataa ->
              let {
                broadcast =
                  defaulta []
                    (binda
                      (geta alla
                        [Char False True False False False True True False,
                          Char False True False False True True True False,
                          Char True True True True False True True False,
                          Char True False False False False True True False,
                          Char False False True False False True True False,
                          Char True True False False False True True False,
                          Char True False False False False True True False,
                          Char True True False False True True True False,
                          Char False False True False True True True False])
                      of_array);
              } in binda (combine_map of_string broadcast)
                     (\ broadcasta ->
                       let {
                         _ = trace_level (Int_of_integer (3 :: Integer))
                               (\ _ ->
                                 return
                                   ("Broadcast channels " ++
                                     implode
                                       (shows_prec_list zero_nat broadcasta
 [])));
                         bounds =
                           defaulta ""
                             (binda
                               (geta alla
                                 [Char False True True False True True True
                                    False,
                                   Char True False False False False True True
                                     False,
                                   Char False True False False True True True
                                     False,
                                   Char True True False False True True True
                                     False])
                               of_string);
                       } in binda (err_msg "Failed to parse bounds"
                                    (parse parse_bounds bounds))
                              (\ boundsa ->
                                binda (geta alla
[Char True True False False False True True False,
  Char False False True True False True True False,
  Char True True True True False True True False,
  Char True True False False False True True False,
  Char True True False True False True True False,
  Char True True False False True True True False])
                                  (\ clocks ->
                                    binda (of_string clocks)
                                      (\ clocksa ->
binda (err_msg "Failed to parse clocks"
        (parse
          (parse_list
            (bindb lx_ws
              (\ _ -> bindb ta_var_ident (\ x -> returna (implode x)))))
          clocksa))
  (\ clocksb ->
    binda (geta alla
            [Char False True True False False True True False,
              Char True True True True False True True False,
              Char False True False False True True True False,
              Char True False True True False True True False,
              Char True False True False True True True False,
              Char False False True True False True True False,
              Char True False False False False True True False])
      (\ formula ->
        binda (of_string formula)
          (\ formulaa ->
            binda (err_msg "Failed to parse formula"
                    (parse scan_formula formulaa))
              (\ formulab ->
                binda (combine_map of_object automataa)
                  (\ automatab ->
                    binda (combine_map
                            (\ a ->
                              binda (geta a
                                      [Char False True True True False True True
 False,
Char True False False False False True True False,
Char True False True True False True True False,
Char True False True False False True True False])
                                of_string)
                            automatab)
                      (\ process_names ->
                        binda (assert (distinct process_names)
                                "Process names are ambiguous")
                          (\ _ ->
                            binda (assert
                                    (less_eq_set (locs_of_formula formulab)
                                      (Set process_names))
                                    "Unknown process name in formula")
                              (\ _ ->
                                let {
                                  process_names_to_index = index process_names;
                                } in binda (combine_map
     (\ a ->
       binda (geta a
               [Char True False False True False True True False,
                 Char False True True True False True True False,
                 Char True False False True False True True False,
                 Char False False True False True True True False,
                 Char True False False True False True True False,
                 Char True False False False False True True False,
                 Char False False True True False True True False])
         (\ x -> binda (of_nat x) Result))
     automatab)
                                       (\ init_locs ->
 let {
   formulac = map_formulaa process_names_to_index id id id formulab;
   vars = map fst boundsa;
   init_vars = map (\ x -> (x, zero_int)) vars;
 } in binda (combine_map (convert_automaton clocksb vars) automatab)
        (\ names_automata ->
          let {
            automatac = map (snd . snd) names_automata;
            names = map fst names_automata;
            ids_to_names = map (fst . snd) names_automata;
            ids_to_namesa =
              (\ p i -> (case nth ids_to_names p i of {
                          Nothing -> implode (shows_prec_nat zero_nat i []);
                          Just n -> n;
                        }));
          } in binda (rename_locs_formula (\ i -> geta (nth names i)) formulac)
                 (\ formulad ->
                   Result
                     (ids_to_namesa,
                       (process_names_to_index,
                         (broadcasta,
                           (automatac,
                             (boundsa,
                               (formulad,
                                 (init_locs, init_vars)))))))))))))))))))))))));

extract_certificate_impl ::
  forall a b.
    (Heapa a, Eq b, Hashable b,
      Heapa b) => (a -> Heap.ST Heap.RealWorld [a]) ->
                    Heap.ST Heap.RealWorld a ->
                      (a -> Heap.ST Heap.RealWorld Bool) ->
                        (a -> a -> Heap.ST Heap.RealWorld Bool) ->
                          (a -> Heap.ST Heap.RealWorld Bool) ->
                            (a -> Heap.ST Heap.RealWorld b) ->
                              (a -> Heap.ST Heap.RealWorld a) ->
                                ([Char] -> a -> Heap.ST Heap.RealWorld ()) ->
                                  () -> Heap.ST Heap.RealWorld [(b, [a])];
extract_certificate_impl succsi a_0i fi lei emptyi keyi copyi tracei =
  uncurry0
    (do { 
       x <- a_0i;
       xa <- emptyi x;
       xaa <- a_0i;
       xab <- fi xaa;
       (_, a) <-
         (if not xa && xab then do { 
                                  x_b <- ht_new;
                                  return (True, x_b)
                                 }
           else do { 
                  xb <- a_0i;
                  x_a <- emptyi xb;
                  (if x_a then do { 
                                 x_c <- ht_new;
                                 return (False, x_c)
                                }
                    else do { 
                           xc <- a_0i;
                           xd <- keyi xc;
                           xac <- a_0i;
                           xba <- ht_new;
                           xe <- ht_update xd [xac] xba;
                           xad <- a_0i;
                           (a1a, (_, a2b)) <-
                             heap_WHILET
                               (\ (_, (a1b, a2b)) ->
                                 return (not a2b && not (op_list_is_empty a1b)))
                               (\ (a1a, (a1b, a2b)) ->
                                 (case (case a1b of {
 [] -> cODE_ABORT (\ _ -> (hd a1b, tl a1b));
 a : b -> (a, b);
                                       })
                                   of {
                                   (a1c, a2c) ->
                                     do { 
                                       x_e <- emptyi a1c;
                                       (if x_e then return (a1a, (a2c, a2b))
 else do { 
        _ <- tRACE_impl;
        _ <- tracei
               [Char True False True False False False True False,
                 Char False False False True True True True False,
                 Char False False False False True True True False,
                 Char False False True True False True True False,
                 Char True True True True False True True False,
                 Char False True False False True True True False,
                 Char True False True False False True True False,
                 Char False False True False False True True False]
               a1c;
        x_h <- succsi a1c;
        imp_nfoldli x_h (\ (_, (_, b)) -> return (not b))
          (\ xl (a1d, (a1e, _)) ->
            do { 
              x_k <- emptyi xl;
              (if x_k then return (a1d, (a1e, False))
                else do { 
                       x_l <- fi xl;
                       (if x_l then return (a1d, (a1e, True))
                         else do { 
                                x_m <- keyi xl;
                                a <- hms_extract ht_lookup ht_delete x_m a1d;
                                (case a of {
                                  (Nothing, a2f) ->
                                    do { 
                                      xf <- copyi xl;
                                      x_o <- ht_update x_m [xf] a2f;
                                      return
(x_o, (op_list_prepend xl a1e, False))
                                     };
                                  (Just x_o, a2f) ->
                                    do { 
                                      x_p <- lso_bex_impl (lei xl) x_o;
                                      (if x_p
then do { 
       x_q <- ht_update x_m x_o a2f;
       return (x_q, (a1e, False))
      }
else do { 
       xf <- copyi xl;
       x_q <- ht_update x_m (xf : x_o) a2f;
       return (x_q, (op_list_prepend xl a1e, False))
      })
                                     };
                                })
                               })
                      })
             })
          (a1a, (a2c, False))
       })
                                      };
                                 }))
                               (xe, (op_list_prepend xad [], False));
                           return (a2b, a1a)
                          })
                 });
       list_of_map_impl a
      });

mk_updsi :: [Int] -> [(Nat, Exp Nat Int)] -> [Int];
mk_updsi s upds =
  fold (\ (x, upd) sa -> list_update sa x (evali sa upd)) upds s;

map_formula ::
  forall a b c d e f.
    (Nat -> a -> b) ->
      (c -> d) -> (e -> f) -> Formula Nat a c e -> Formula Nat b d f;
map_formula f g h (EX phi) = EX (map_sexp f g h phi);
map_formula f g h (EG phi) = EG (map_sexp f g h phi);
map_formula f g h (AX phi) = AX (map_sexp f g h phi);
map_formula f g h (AG phi) = AG (map_sexp f g h phi);
map_formula f g h (Leadsto phi psi) =
  Leadsto (map_sexp f g h phi) (map_sexp f g h psi);

map_acconstraint ::
  forall a b c d. (a -> b) -> (c -> d) -> Acconstraint a c -> Acconstraint b d;
map_acconstraint f1 f2 (LT x11 x12) = LT (f1 x11) (f2 x12);
map_acconstraint f1 f2 (LE x21 x22) = LE (f1 x21) (f2 x22);
map_acconstraint f1 f2 (EQ x31 x32) = EQ (f1 x31) (f2 x32);
map_acconstraint f1 f2 (GT x41 x42) = GT (f1 x41) (f2 x42);
map_acconstraint f1 f2 (GE x51 x52) = GE (f1 x51) (f2 x52);

mem_assoc :: forall a b. (Eq a) => a -> [(a, b)] -> Bool;
mem_assoc x = any (\ (y, _) -> x == y);

show_locs :: forall a b. (Showa b) => (Nat -> a -> b) -> [a] -> [Char];
show_locs inv_renum_states =
  (\ x -> shows_prec_list zero_nat x []) . map_index zero_nat inv_renum_states;

show_vars :: forall a b. (Showa a, Showa b) => (Nat -> a) -> [b] -> [Char];
show_vars inv_renum_vars =
  (\ x -> shows_prec_list zero_nat x []) .
    map_index zero_nat
      (\ i v ->
        shows_prec zero_nat (inv_renum_vars i) [] ++
          [Char True False True True True True False False] ++
            shows_prec zero_nat v []);

fw_upd_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Nat ->
          Nat ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
fw_upd_impl_int n =
  (\ ai bib bia bi ->
    do { 
      xa <- mtx_get (suc n) ai (bia, bib);
      xb <- mtx_get (suc n) ai (bib, bi);
      x <- mtx_get (suc n) ai (bia, bi);
      let { e = dbm_add_int xa xb };
      (if less_DBMEntry e x then mtx_set (suc n) ai (bia, bi) e else return ai)
     });

fw_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
fw_impl_int n =
  imp_for_inta zero_nat (plus_nat n one_nat)
    (\ xb ->
      imp_for_inta zero_nat (plus_nat n one_nat)
        (\ xd ->
          imp_for_inta zero_nat (plus_nat n one_nat)
            (\ xf sigma -> fw_upd_impl_int n sigma xb xd xf)));

check_final_impl ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => ((a, b) -> Heap.ST Heap.RealWorld Bool) ->
                    (b -> Heap.ST Heap.RealWorld b) ->
                      [a] -> Hashtable a [b] -> Heap.ST Heap.RealWorld Bool;
check_final_impl fi copyi =
  (\ ai bi ->
    imp_nfoldli ai return
      (\ xb _ ->
        do { 
          a <- hms_lookup ht_lookup (heap_map copyi) xb bi;
          (case a of {
            Nothing -> return True;
            Just x_e ->
              imp_nfoldli x_e return (\ xh _ -> do { 
          x_i <- fi (xb, xh);
          return (not x_i)
         })
                True;
          })
         })
      True);

distr :: forall a. (Eq a, Linorder a) => [a] -> [(a, Nat)];
distr xs =
  (case fold (\ x (m, d) ->
               (case m x of {
                 Nothing -> (fun_upd m x (Just one_nat), x : d);
                 Just y -> (fun_upd m x (Just (plus_nat y one_nat)), d);
               }))
          xs ((\ _ -> Nothing), [])
    of {
    (m, d) -> map (\ x -> (x, the (m x))) (sort_key (\ x -> x) d);
  });

show_clock :: forall a b. (Showa b) => (a -> b) -> a -> [Char];
show_clock inv_renum_clocks =
  (\ x -> shows_prec zero_nat x []) . inv_renum_clocks;

show_state ::
  forall a b c d.
    (Showa b, Showa c,
      Showa d) => (Nat -> a -> b) -> (Nat -> c) -> ([a], [d]) -> [Char];
show_state inv_renum_states inv_renum_vars =
  (\ (l, vs) ->
    let {
      la = show_locs inv_renum_states l;
      vsa = show_vars inv_renum_vars vs;
    } in [Char False False True True True True False False] ++
           la ++ [Char False True True True True True False False,
                   Char False False True True False True False False,
                   Char False False False False False True False False,
                   Char False False True True True True False False] ++
                   vsa ++ [Char False True True True True True False False]);

bounds_map :: [(Nat, (Int, Int))] -> Nat -> (Int, Int);
bounds_map bounds = the . map_of bounds;

check_boundedi :: [(Nat, (Int, Int))] -> [Int] -> Bool;
check_boundedi bounds s =
  all_interval_nat
    (\ x ->
      less_eq_int (fst (bounds_map bounds x)) (nth s x) &&
        less_eq_int (nth s x) (snd (bounds_map bounds x)))
    zero_nat (size_list s);

pairs_by_action_impl ::
  forall a b c d e.
    [(Nat, (Int, Int))] ->
      [a] ->
        [Int] ->
          [(Nat, (Bexp Nat Int,
                   ([b], (c, ([(Nat, Exp Nat Int)], ([d], a))))))] ->
            [(Nat, (Bexp Nat Int,
                     ([b], (e, ([(Nat, Exp Nat Int)], ([d], a))))))] ->
              [([b], (Label e, ([d], ([a], [Int]))))];
pairs_by_action_impl bounds l s out ina =
  concatMap
    (\ (p, (b1, (g1, (a1, (f1, (r1, l1)))))) ->
      map_filter
        (\ (q, (b2, (g2, (_, (f2, (r2, l2)))))) ->
          (if equal_nat p q then Nothing
            else let {
                   sa = mk_updsi (mk_updsi s f1) f2;
                 } in (if bvali s b1 && bvali s b2 && check_boundedi bounds sa
                        then Just (g1 ++ g2,
                                    (Bin a1,
                                      (r1 ++ r2,
(list_update (list_update l p l1) q l2, sa))))
                        else Nothing)))
        out)
    ina;

actions_by_state ::
  forall a b c d.
    a -> [(b, (c, (Nat, d)))] ->
           [[(a, (b, (c, (Nat, d))))]] -> [[(a, (b, (c, (Nat, d))))]];
actions_by_state i =
  fold (\ t acc ->
         list_update acc (fst (snd (snd t)))
           ((i, t) : nth acc (fst (snd (snd t)))));

all_actions_from_vec ::
  forall a b c d e.
    Nat ->
      (a -> b -> [(c, (d, (Nat, e)))]) ->
        [(a, b)] -> [[(a, (c, (d, (Nat, e))))]];
all_actions_from_vec num_actions t vec =
  fold (\ (p, l) -> actions_by_state p (t p l)) vec
    (map (\ _ -> []) (upt zero_nat num_actions));

all_actions_by_state ::
  forall a b c d.
    [Nat] ->
      [(Nat, (Int, Int))] ->
        [([Nat],
           ([Nat],
             ([(Nat, (Bexp Nat Int,
                       ([Acconstraint Nat Int],
                         (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
               [(Nat, [Acconstraint Nat Int])])))] ->
          Nat ->
            (Nat -> a -> [(b, (c, (Nat, d)))]) ->
              [a] -> [[(Nat, (b, (c, (Nat, d))))]];
all_actions_by_state broadcast bounds automata num_actions t l =
  fold (\ i -> actions_by_state i (t i (nth l i)))
    (upt zero_nat (size_list automata))
    (map (\ _ -> []) (upt zero_nat num_actions));

compute_upds_impl ::
  forall a b c d e f.
    [(Nat, (Int, Int))] ->
      ([a], (b, ([c], ([d], [Int])))) ->
        [[(Nat, (e, ([a], (f, ([(Nat, Exp Nat Int)], ([c], d))))))]] ->
          [([a], (b, ([c], ([d], [Int]))))];
compute_upds_impl bounds init =
  map_filter
    (\ comb ->
      (case fold (\ (q, (_, (g2, (_, (f2, (r2, l2)))))) (g1, (a, (r1, (l, s))))
                   -> (g1 ++ g2,
                        (a, (r1 ++ r2, (list_update l q l2, mk_updsi s f2)))))
              comb init
        of {
        (g, (a, (r, (l, s)))) ->
          (if check_boundedi bounds s then Just (g, (a, (r, (l, s))))
            else Nothing);
      }));

actions_by_statea ::
  forall a b c. Nat -> [(a, (b, (Nat, c)))] -> [[(a, (b, (Nat, c)))]];
actions_by_statea num_actions xs =
  fold (\ t acc ->
         list_update acc (fst (snd (snd t))) (t : nth acc (fst (snd (snd t)))))
    xs (map (\ _ -> []) (upt zero_nat num_actions));

get_committed ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        [Nat] -> [(Nat, Nat)];
get_committed broadcast bounds automata l =
  map_filter
    (\ p ->
      let {
        la = nth l p;
      } in (if membera (fst (nth automata p)) la then Just (p, la)
             else Nothing))
    (upt zero_nat (size_list automata));

bin_actions :: [Nat] -> Nat -> [Nat];
bin_actions broadcast num_actions =
  filter (\ a -> not (membera broadcast a)) (upt zero_nat num_actions);

make_combs ::
  forall a.
    [Nat] ->
      [(Nat, (Int, Int))] ->
        [([Nat],
           ([Nat],
             ([(Nat, (Bexp Nat Int,
                       ([Acconstraint Nat Int],
                         (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
               [(Nat, [Acconstraint Nat Int])])))] ->
          Nat -> Nat -> [[[a]]] -> [[(Nat, a)]];
make_combs broadcast bounds automata p a xs =
  let {
    ys = map_filter
           (\ i ->
             (if equal_nat i p then Nothing
               else (if null (nth (nth xs i) a) then Nothing
                      else Just (map (\ aa -> (i, aa)) (nth (nth xs i) a)))))
           (upt zero_nat (size_list automata));
  } in (if null ys then [] else product_lists ys);

union_map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe [b];
union_map_of xs =
  fold (\ (x, y) m -> (case m x of {
                        Nothing -> fun_upd m x (Just [y]);
                        Just ys -> fun_upd m x (Just (y : ys));
                      }))
    xs (\ _ -> Nothing);

trans_map ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat ->
      Nat ->
        [(Bexp Nat Int,
           ([Acconstraint Nat Int],
             (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat)))))];
trans_map automata i = let {
                         m = union_map_of (fst (snd (snd (nth automata i))));
                       } in (\ j -> (case m j of {
                                      Nothing -> [];
                                      Just xs -> xs;
                                    }));

reset_canonical_upd_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Nat ->
          Int ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
reset_canonical_upd_impl_int =
  (\ n ai bib bia bi ->
    do { 
      x <- mtx_set (suc n) ai (bia, zero_nat) (Le bi);
      mtx_set (suc n) x (zero_nat, bia) (Le (uminus_int bi)) >>=
        imp_for_inta one_nat (plus_nat bib one_nat)
          (\ xb sigma ->
            (if equal_nat xb bia then return sigma
              else do { 
                     x_d <- mtx_get (suc n) sigma (zero_nat, xb);
                     x_e <- mtx_get (suc n) sigma (xb, zero_nat);
                     x_f <-
                       mtx_set (suc n) sigma (bia, xb)
                         (dbm_add_int (Le bi) x_d);
                     mtx_set (suc n) x_f (xb, bia)
                       (dbm_add_int (Le (uminus_int bi)) x_e)
                    }))
     });

up_canonical_upd_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
up_canonical_upd_impl_int =
  (\ n ai bi ->
    imp_for_inta one_nat (plus_nat bi one_nat)
      (\ xa sigma -> mtx_set (suc n) sigma (xa, zero_nat) INF) ai);

check_diag_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) -> Heap.ST Heap.RealWorld Bool;
check_diag_impl_int =
  (\ n xi ->
    imp_for_int zero_nat (suc n) (\ sigma -> return (not sigma))
      (\ xc sigma -> do { 
                       x <- mtx_get (suc n) xi (xc, xc);
                       return (dbm_lt_0 x || sigma)
                      })
      False);

abstra_upd_impl_int ::
  Nat ->
    Acconstraint Nat Int ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
abstra_upd_impl_int =
  (\ n ai bi ->
    (case ai of {
      LT x41a x42a ->
        do { 
          x <- mtx_get (suc n) bi (x41a, zero_nat);
          mtx_set (suc n) bi (x41a, zero_nat) (min_int_entry x (Lt x42a))
         };
      LE x41a x42a ->
        do { 
          x <- mtx_get (suc n) bi (x41a, zero_nat);
          mtx_set (suc n) bi (x41a, zero_nat) (min_int_entry x (Le x42a))
         };
      EQ x41a x42a ->
        do { 
          x <- mtx_get (suc n) bi (zero_nat, x41a);
          x_a <- mtx_get (suc n) bi (x41a, zero_nat);
          x_b <-
            mtx_set (suc n) bi (zero_nat, x41a)
              (min_int_entry x (Le (uminus_int x42a)));
          mtx_set (suc n) x_b (x41a, zero_nat) (min_int_entry x_a (Le x42a))
         };
      GT x41a x42a ->
        do { 
          x <- mtx_get (suc n) bi (zero_nat, x41a);
          mtx_set (suc n) bi (zero_nat, x41a)
            (min_int_entry x (Lt (uminus_int x42a)))
         };
      GE x41a x42a ->
        do { 
          x <- mtx_get (suc n) bi (zero_nat, x41a);
          mtx_set (suc n) bi (zero_nat, x41a)
            (min_int_entry x (Le (uminus_int x42a)))
         };
    }));

tracei ::
  forall a b.
    (Linordered_ab_group_add b, Eq b, Heapa b,
      Showa b) => Nat ->
                    (a -> [Char]) ->
                      (Nat -> [Char]) ->
                        [Char] ->
                          (a, Heap.STArray Heap.RealWorld (DBMEntry b)) ->
                            Heap.ST Heap.RealWorld ();
tracei n show_state show_clock typea =
  (\ (l, m) ->
    let {
      _ = trace_level (Int_of_integer (5 :: Integer))
            (\ _ ->
              let {
                st = show_state l;
              } in do { 
                     ma <- show_dbm_impl n show_clock
                             (\ x -> shows_prec zero_nat x []) m;
                     let { s =
                       typea ++
                         [Char False True False True True True False False,
                           Char False False False False False True False False,
                           Char False False False True False True False
                             False] ++
                           st ++ [Char False False True True False True False
                                    False,
                                   Char False False False False False True False
                                     False,
                                   Char False False True True True True False
                                     False] ++
                                   ma ++ [Char False True True True True True
    False False,
   Char True False False True False True False False]
                       };
                     let { a = implode s };
                     return a
                    });
    } in return ());

n_vs :: forall a. [(a, (Int, Int))] -> Nat;
n_vs bounds = size_list bounds;

check_sexpi :: forall a. (Eq a) => Sexp Nat a Nat Int -> [a] -> [Int] -> Bool;
check_sexpi Trueb uu uv = True;
check_sexpi (Nota e) l s = not (check_sexpi e l s);
check_sexpi (Anda e1 e2) l s = check_sexpi e1 l s && check_sexpi e2 l s;
check_sexpi (Ora e1 e2) l s = check_sexpi e1 l s || check_sexpi e2 l s;
check_sexpi (Implya e1 e2) l s =
  (if check_sexpi e1 l s then check_sexpi e2 l s else True);
check_sexpi (Eqb i x) l s = equal_int (nth s i) x;
check_sexpi (Leb i x) l s = less_eq_int (nth s i) x;
check_sexpi (Ltb i x) l s = less_int (nth s i) x;
check_sexpi (Gea i x) l s = less_eq_int x (nth s i);
check_sexpi (Gta i x) l s = less_int x (nth s i);
check_sexpi (Loc i x) l s = nth l i == x;

hd_of_formulai ::
  forall a. (Eq a) => Formula Nat a Nat Int -> [a] -> [Int] -> Bool;
hd_of_formulai (EX phi) l s = check_sexpi phi l s;
hd_of_formulai (EG phi) l s = check_sexpi phi l s;
hd_of_formulai (AX phi) l s = not (check_sexpi phi l s);
hd_of_formulai (AG phi) l s = not (check_sexpi phi l s);
hd_of_formulai (Leadsto phi uu) l s = check_sexpi phi l s;

state_space ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [[[Nat]]] ->
                [Nat] ->
                  [(Nat, Int)] ->
                    Formula Nat Nat Nat Int ->
                      (Nat -> [Char]) ->
                        (([Nat], [Int]) -> [Char]) ->
                          () -> Heap.ST Heap.RealWorld
                                  [(([Nat], [Int]),
                                     [(([Nat], [Int]),
Heap.STArray Heap.RealWorld (DBMEntry Int))])];
state_space broadcast bounds automata m num_states num_actions k l_0 s_0 formula
  show_clock show_state =
  let {
    succsi =
      let {
        n_ps = size_list automata;
        k_i = IArray.of_list
                (map (IArray.of_list . map (IArray.of_list . map int_of_nat))
                  k);
        invs =
          IArray.of_list
            (map (\ i ->
                   let {
                     ma = default_map_of [] (snd (snd (snd (nth automata i))));
                     mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
                   } in mb)
              (upt zero_nat n_ps));
        inv_fun =
          (\ (l, _) ->
            concatMap (\ i -> sub (sub invs i) (nth l i)) (upt zero_nat n_ps));
        trans_mapa = trans_map automata;
        trans_i_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                }))
              (trans_mapa i j));
        int_trans_from_loc_impl =
          (\ p l la s ->
            let {
              a = trans_i_map p l;
            } in map_filter
                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                     let {
                       sa = mk_updsi s f;
                     } in (if bvali s b && check_boundedi bounds sa
                            then Just (g,
(Internal aa, (r, (list_update la p lb, sa))))
                            else Nothing))
                   a);
        int_trans_from_vec_impl =
          (\ pairs l s ->
            concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
        int_trans_from_all_impl =
          (\ l s ->
            concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nat n_ps));
        trans_out_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_in_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_out_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        trans_in_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        broad_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              out = map (\ p -> trans_out_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
              outa = map (map (filter (\ (b, _) -> bvali s b))) out;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            concatMap
                              (\ p ->
                                let {
                                  outs = nth (nth outa p) a;
                                } in (if null outs then []
                                       else let {
      combs = make_combs broadcast bounds automata p a inb;
      outsa = map (\ aa -> (p, aa)) outs;
      combsa =
        (if null combs then map (\ x -> [x]) outsa
          else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
      init = ([], (Broad a, ([], (l, s))));
    } in compute_upds_impl bounds init combsa))
                              (upt zero_nat n_ps))
                          (upt zero_nat num_actions)
                   else concatMap
                          (\ a ->
                            let {
                              ins_committed =
                                map_filter
                                  (\ (p, _) ->
                                    (if not (null (nth (nth inb p) a))
                                      then Just p else Nothing))
                                  pairs;
                              always_committed =
                                less_nat one_nat (size_list ins_committed);
                            } in concatMap
                                   (\ p ->
                                     let {
                                       outs = nth (nth outa p) a;
                                     } in (if null outs then []
    else (if not always_committed &&
               (ins_committed == [p] || null ins_committed) &&
                 not (any (\ (q, _) -> equal_nat q p) pairs)
           then []
           else let {
                  combs = make_combs broadcast bounds automata p a inb;
                  outsa = map (\ aa -> (p, aa)) outs;
                  combsa =
                    (if null combs then map (\ x -> [x]) outsa
                      else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                  init = ([], (Broad a, ([], (l, s))));
                } in compute_upds_impl bounds init combsa)))
                                   (upt zero_nat n_ps))
                          (upt zero_nat num_actions)));
        bin_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
              out = all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let {
                          in2 = all_actions_from_vec num_actions trans_in_map
                                  pairs;
                          out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        } in concatMap
                               (\ a ->
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                               (bin_actions broadcast num_actions) ++
                               concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                                 (bin_actions broadcast num_actions)));
        int_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
            } in (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s));
        trans_impl =
          (\ st ->
            int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
        e_op_impl =
          (\ ai bic bib bia bi ->
            do { 
              x <- up_canonical_upd_impl_int m bi m;
              xa <- imp_nfoldli (inv_fun ai) (\ _ -> return True)
                      (\ aia bid ->
                        do { 
                          xa <- abstra_upd_impl_int m aia bid;
                          repair_pair_impl_int m xa zero_nat
                            (constraint_clk aia)
                         })
                      x;
              xaa <- check_diag_impl_inta m m xa;
              x_a <-
                (if xaa
                  then mtx_set (suc m) xa (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bib (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            })
                         xa);
              xb <- check_diag_impl_inta m m x_a;
              x_b <-
                (if xb
                  then mtx_set (suc m) x_a (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bic (\ _ -> return True)
                         (\ xc sigma ->
                           reset_canonical_upd_impl_int m sigma m xc zero_int)
                         x_a >>=
                         imp_nfoldli (inv_fun bia) (\ _ -> return True)
                           (\ aia bid ->
                             do { 
                               xc <- abstra_upd_impl_int m aia bid;
                               repair_pair_impl_int m xc zero_nat
                                 (constraint_clk aia)
                              }));
              x_c <- check_diag_impl_inta m m x_b;
              (if x_c
                then mtx_set (suc m) x_b (zero_nat, zero_nat) (Lt zero_int)
                else norm_upd_impl m x_b
                       (case bia of {
                         (l, _) ->
                           IArray.of_list
                             (map (\ c ->
                                    maxa (image
   (\ i -> sub (sub (sub k_i i) (nth l i)) c) (Set (upt zero_nat n_ps))))
                               (upt zero_nat (plus_nat m one_nat)));
                       })
                       m >>=
                       fw_impl_int m)
             });
      } in (\ (a1, a2) ->
             imp_nfoldli (trans_impl a1) (\ _ -> return True)
               (\ xc sigma ->
                 (case xc of {
                   (a1a, (_, (a1c, a2c))) ->
                     do { 
                       x <- amtx_copy a2;
                       xa <- e_op_impl a1 a1c a1a a2c x;
                       return (op_list_prepend (a2c, xa) sigma)
                      };
                 }))
               []);
    a_0i =
      do { 
        x_a <- amtx_dflt (suc m) (suc m) (Le zero_int);
        return ((l_0, map (the . map_of s_0) (upt zero_nat (n_vs bounds))), x_a)
       };
    fi = (\ xi -> return (case xi of {
                           ((a, b), _) -> hd_of_formulai formula a b;
                         }));
    lei = (\ ai bi ->
            (case ai of {
              (a1, a2) ->
                (case bi of {
                  (a1a, a2a) ->
                    (if a1 == a1a then dbm_subset_impl m a2 a2a
                      else return False);
                });
            }));
    emptyi = (\ (_, a) -> check_diag_impl_int m a);
    keyi = return . fst;
    copyi = (\ (a1, a2) -> do { 
                             x <- amtx_copy a2;
                             return (a1, x)
                            });
    a = tracei m show_state show_clock;
  } in extract_certificate_impl succsi a_0i fi lei emptyi keyi copyi a;

list_of_set :: forall a. (Eq a) => Set a -> [a];
list_of_set xs = remdups ((case xs of Set xs -> xs));

mk_renaming ::
  forall a. (Eq a) => (a -> String) -> [a] -> Result (a -> Nat, Nat -> a);
mk_renaming str xs =
  binda (fold_error
          (\ x m ->
            (if mem_assoc x m then Error ["Duplicate name: " ++ str x]
              else Result ((x, size_list m) : m)))
          xs [])
    (\ mapping -> Result (let {
                            m = map_of mapping;
                            f = (\ x -> (case m x of {
  Nothing -> error   "empty case";
  Just v -> v;
}));
                            ma = map_of (map swap mapping);
                            a = (\ x -> (case ma x of {
  Nothing -> error   "empty case";
  Just v -> v;
}));
                          } in (f, a)));

imp_map ::
  forall a b.
    (a -> Heap.ST Heap.RealWorld b) -> [a] -> Heap.ST Heap.RealWorld [b];
imp_map f (x : xs) = do { 
                       y <- f x;
                       ys <- imp_map f xs;
                       return (y : ys)
                      };
imp_map f [] = return [];

show_st ::
  forall a.
    (Showa a) => (Nat -> Nat -> Nat) ->
                   (Nat -> String) -> ([Nat], [a]) -> [Char];
show_st inv_renum_states inv_renum_vars =
  show_state inv_renum_states inv_renum_vars;

set2_sexp :: forall a b c d. (Eq b) => Sexp a b c d -> Set b;
set2_sexp Trueb = bot_set;
set2_sexp (Nota x2) = set2_sexp x2;
set2_sexp (Anda x31 x32) = sup_set (set2_sexp x31) (set2_sexp x32);
set2_sexp (Ora x41 x42) = sup_set (set2_sexp x41) (set2_sexp x42);
set2_sexp (Implya x51 x52) = sup_set (set2_sexp x51) (set2_sexp x52);
set2_sexp (Eqb x61 x62) = bot_set;
set2_sexp (Leb x71 x72) = bot_set;
set2_sexp (Ltb x81 x82) = bot_set;
set2_sexp (Gea x91 x92) = bot_set;
set2_sexp (Gta x101 x102) = bot_set;
set2_sexp (Loc x111 x112) = insert x112 bot_set;

set2_formula :: forall a b c d. (Eq b) => Formula a b c d -> Set b;
set2_formula (EX x1) = set2_sexp x1;
set2_formula (EG x2) = set2_sexp x2;
set2_formula (AX x3) = set2_sexp x3;
set2_formula (AG x4) = set2_sexp x4;
set2_formula (Leadsto x51 x52) = sup_set (set2_sexp x51) (set2_sexp x52);

clkp_set ::
  forall a b c d.
    (Eq c) => [([a], ([a], ([(a, (Bexp b Int,
                                   ([Acconstraint c Int],
                                     (Act d, ([(b, Exp b Int)], ([c], a))))))],
                             [(a, [Acconstraint c Int])])))] ->
                Set (c, Int);
clkp_set automata =
  sup_set
    (sup_seta
      (image
        (\ a ->
          sup_seta
            (image (\ g -> collect_clock_pairs (snd g))
              (Set (snd (snd (snd a))))))
        (Set automata)))
    (sup_seta
      (image
        (\ a ->
          sup_seta
            (image (\ (_, (_, (g, _))) -> collect_clock_pairs g)
              (Set (fst (snd (snd a))))))
        (Set automata)));

clk_set ::
  forall a b c d.
    (Eq c) => [([a], ([a], ([(a, (Bexp b Int,
                                   ([Acconstraint c Int],
                                     (Act d, ([(b, Exp b Int)], ([c], a))))))],
                             [(a, [Acconstraint c Int])])))] ->
                Set c;
clk_set automata =
  sup_set (image fst (clkp_set automata))
    (sup_seta
      (image
        (\ a ->
          sup_seta
            (image (\ (_, (_, (_, (_, (_, (r, _)))))) -> Set r)
              (Set (fst (snd (snd a))))))
        (Set automata)));

vars_of_sexp :: forall a b c d. (Eq c) => Sexp a b c d -> Set c;
vars_of_sexp (Nota e) = vars_of_sexp e;
vars_of_sexp (Anda e1 e2) = sup_set (vars_of_sexp e1) (vars_of_sexp e2);
vars_of_sexp (Ora e1 e2) = sup_set (vars_of_sexp e1) (vars_of_sexp e2);
vars_of_sexp (Implya e1 e2) = sup_set (vars_of_sexp e1) (vars_of_sexp e2);
vars_of_sexp (Eqb i x) = insert i bot_set;
vars_of_sexp (Ltb i x) = insert i bot_set;
vars_of_sexp (Leb i x) = insert i bot_set;
vars_of_sexp (Gea i x) = insert i bot_set;
vars_of_sexp (Gta i x) = insert i bot_set;
vars_of_sexp Trueb = bot_set;
vars_of_sexp (Loc v va) = bot_set;

vars_of_formula :: forall a b c d. (Eq c) => Formula a b c d -> Set c;
vars_of_formula (EX phi) = vars_of_sexp phi;
vars_of_formula (EG phi) = vars_of_sexp phi;
vars_of_formula (AX phi) = vars_of_sexp phi;
vars_of_formula (AG phi) = vars_of_sexp phi;
vars_of_formula (Leadsto phi psi) =
  sup_set (vars_of_sexp phi) (vars_of_sexp psi);

check_renaming ::
  forall a b.
    [String] ->
      [(String, (Int, Int))] ->
        (String -> Nat) ->
          (String -> Nat) ->
            (String -> Nat) ->
              (Nat -> Nat -> Nat) ->
                [([Nat],
                   ([Nat],
                     ([(Nat, (Bexp String Int,
                               ([Acconstraint String Int],
                                 (Act String,
                                   ([(String, Exp String Int)],
                                     ([String], Nat))))))],
                       [(Nat, [Acconstraint String Int])])))] ->
                  String ->
                    Formula Nat Nat String a ->
                      [Nat] -> [(String, b)] -> Result [()];
check_renaming broadcast bounds renum_acts renum_vars renum_clocks renum_states
  automata urge phi l_0 s_0 =
  combine
    [assert
       (all_interval_nat
         (\ i ->
           ball (sup_seta
                  (image
                    (\ (_, (_, (t, _))) ->
                      sup_seta
                        (image
                          (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                            insert l (insert la bot_set))
                          (Set t)))
                    (Set automata)))
             (\ x ->
               ball (sup_seta
                      (image
                        (\ (_, (_, (t, _))) ->
                          sup_seta
                            (image
                              (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                                insert l (insert la bot_set))
                              (Set t)))
                        (Set automata)))
                 (\ y ->
                   (if equal_nat (renum_states i x) (renum_states i y)
                     then equal_nat x y else True))))
         zero_nat (size_list automata))
       "Location renamings are injective",
      assert (inj_on renum_clocks (insert urge (clk_set automata)))
        "Clock renaming is injective",
      assert
        (inj_on renum_vars
          (sup_set
            (sup_seta
              (image (\ s -> sup_seta (image vars_of_bexp s))
                (image (\ t -> image (fst . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))
            (sup_seta
              (image
                (\ s ->
                  sup_seta
                    (image
                      (\ f ->
                        sup_seta
                          (image
                            (\ (x, e) ->
                              sup_set (insert x bot_set) (vars_of_exp e))
                            (Set f)))
                      s))
                (image
                  (\ t -> image ((((fst . snd) . snd) . snd) . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))))
        "Variable renaming is injective",
      assert
        (inj_on renum_acts
          (sup_set
            (sup_seta
              (image
                (\ (_, (_, (t, _))) ->
                  sup_seta
                    (image (\ (_, (_, (_, (a, _)))) -> set_act a) (Set t)))
                (Set automata)))
            (Set broadcast)))
        "Action renaming is injective",
      assert
        (equal_set (image fst (Set bounds))
          (sup_set
            (sup_seta
              (image (\ s -> sup_seta (image vars_of_bexp s))
                (image (\ t -> image (fst . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))
            (sup_seta
              (image
                (\ s ->
                  sup_seta
                    (image
                      (\ f ->
                        sup_seta
                          (image
                            (\ (x, e) ->
                              sup_set (insert x bot_set) (vars_of_exp e))
                            (Set f)))
                      s))
                (image
                  (\ t -> image ((((fst . snd) . snd) . snd) . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))))
        "Bound set is exactly the variable set",
      assert
        (less_eq_set
          (sup_seta
            (image (\ g -> image fst (Set g))
              (Set (map ((snd . snd) . snd) automata))))
          (sup_seta
            (image
              (\ (_, (_, (t, _))) ->
                sup_seta
                  (image
                    (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                      insert l (insert la bot_set))
                    (Set t)))
              (Set automata))))
        "Invariant locations are contained in the location set",
      assert
        (less_eq_set (sup_seta (image (Set . fst) (Set automata)))
          (sup_seta
            (image
              (\ (_, (_, (t, _))) ->
                sup_seta
                  (image
                    (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                      insert l (insert la bot_set))
                    (Set t)))
              (Set automata))))
        "Broadcast locations are containted in the location set",
      assert
        (less_eq_set
          (sup_seta (image (\ x -> Set (fst (snd x))) (Set automata)))
          (sup_seta
            (image
              (\ (_, (_, (t, _))) ->
                sup_seta
                  (image
                    (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                      insert l (insert la bot_set))
                    (Set t)))
              (Set automata))))
        "Urgent locations are containted in the location set",
      assert (not (member urge (clk_set automata))) "Urge not in clock set",
      assert
        (equal_nat (size_list l_0) (size_list automata) &&
          all_interval_nat
            (\ i ->
              bex (fst (snd (snd (nth (fst
(snd (Set broadcast, (map automaton_of automata, map_of bounds))))
                                   i))))
                (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                  equal_nat (nth l_0 i) l || equal_nat (nth l_0 i) la))
            zero_nat (size_list automata))
        "Initial location is in the state set",
      assert
        (equal_set (image fst (Set s_0))
          (sup_set
            (sup_seta
              (image (\ s -> sup_seta (image vars_of_bexp s))
                (image (\ t -> image (fst . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))
            (sup_seta
              (image
                (\ s ->
                  sup_seta
                    (image
                      (\ f ->
                        sup_seta
                          (image
                            (\ (x, e) ->
                              sup_set (insert x bot_set) (vars_of_exp e))
                            (Set f)))
                      s))
                (image
                  (\ t -> image ((((fst . snd) . snd) . snd) . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))))
        "Initial state has the correct domain",
      assert (distinct (map fst s_0)) "Initial state is unambiguous",
      assert
        (less_eq_set (set2_formula phi)
          (sup_seta
            (image
              (\ (_, (_, (t, _))) ->
                sup_seta
                  (image
                    (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                      insert l (insert la bot_set))
                    (Set t)))
              (Set automata))))
        "Formula locations are contained in the location set",
      assert
        (less_eq_set (locs_of_formula phi)
          (Set (upt zero_nat (size_list automata))))
        "Formula automata are contained in the automata set",
      assert
        (less_eq_set (vars_of_formula phi)
          (sup_set
            (sup_seta
              (image (\ s -> sup_seta (image vars_of_bexp s))
                (image (\ t -> image (fst . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))
            (sup_seta
              (image
                (\ s ->
                  sup_seta
                    (image
                      (\ f ->
                        sup_seta
                          (image
                            (\ (x, e) ->
                              sup_set (insert x bot_set) (vars_of_exp e))
                            (Set f)))
                      s))
                (image
                  (\ t -> image ((((fst . snd) . snd) . snd) . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))))
        "Variables of the formula are contained in the variable set"];

check_precond2 ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            [[[Nat]]] ->
              [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Result [()];
check_precond2 broadcast bounds automata m num_states k l_0 s_0 formula =
  combine
    [assert
       (all_interval_nat
         (\ i ->
           all (\ (l, g) ->
                 ball (collect_clock_pairs g)
                   (\ (x, ma) ->
                     less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
             (((snd . snd) . snd) (nth automata i)))
         zero_nat (size_list automata))
       "Ceiling invariants",
      assert
        (all_interval_nat
          (\ i ->
            all (\ (l, (_, (g, _))) ->
                  ball (collect_clock_pairs g)
                    (\ (x, ma) ->
                      less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
              (((fst . snd) . snd) (nth automata i)))
          zero_nat (size_list automata))
        "Ceiling transitions",
      assert
        (all_interval_nat
          (\ i ->
            all (\ (l, (_, (_, (_, (_, (r, la)))))) ->
                  ball (minus_set (Set (upt zero_nat (plus_nat m one_nat)))
                         (Set r))
                    (\ c ->
                      less_eq_nat (nth (nth (nth k i) la) c)
                        (nth (nth (nth k i) l) c)))
              (((fst . snd) . snd) (nth automata i)))
          zero_nat (size_list automata))
        "Ceiling resets",
      assert (equal_nat (size_list k) (size_list automata)) "Ceiling length",
      assert
        (all_interval_nat
          (\ i -> equal_nat (size_list (nth k i)) (num_states i)) zero_nat
          (size_list automata))
        "Ceiling length automata)",
      assert
        (all (all (\ xxs -> equal_nat (size_list xxs) (plus_nat m one_nat))) k)
        "Ceiling length clocks",
      assert
        (all_interval_nat
          (\ i ->
            all_interval_nat
              (\ l -> equal_nat (nth (nth (nth k i) l) zero_nat) zero_nat)
              zero_nat (num_states i))
          zero_nat (size_list automata))
        "Ceiling zero clock",
      assert (all (\ (_, (_, (_, inv))) -> distinct (map fst inv)) automata)
        "Unambiguous invariants",
      assert
        (equal_set (image fst (Set s_0)) (image fst (Set bounds)) &&
          ball (image fst (Set s_0))
            (\ x ->
              less_eq_int (fst (the (map_of bounds x))) (the (map_of s_0 x)) &&
                less_eq_int (the (map_of s_0 x)) (snd (the (map_of bounds x)))))
        "Initial state bounded",
      assert (equal_nat (size_list l_0) (size_list automata))
        "Length of initial state",
      assert
        (all_interval_nat
          (\ i ->
            member (nth l_0 i)
              (image fst (Set (((fst . snd) . snd) (nth automata i)))))
          zero_nat (size_list automata))
        "Initial state has outgoing transitions",
      assert
        (less_eq_set (vars_of_formula formula)
          (Set (upt zero_nat (n_vs bounds))))
        "Variable set of formula"];

check_precond1 ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat -> (Nat -> Nat) -> Nat -> Result [()];
check_precond1 broadcast bounds automata m num_states num_actions =
  combine
    [assert (less_nat zero_nat m) "At least one clock",
      assert (less_nat zero_nat (size_list automata)) "At least one automaton",
      assert
        (all_interval_nat
          (\ i ->
            (case nth automata i of {
              (_, (_, (trans, _))) ->
                all (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                      less_nat l (num_states i) && less_nat la (num_states i))
                  trans;
            }))
          zero_nat (size_list automata))
        "Number of states is correct (transitions)",
      assert
        (all_interval_nat
          (\ i ->
            (case nth automata i of {
              (_, (_, (_, a))) -> all (\ (x, _) -> less_nat x (num_states i)) a;
            }))
          zero_nat (size_list automata))
        "Number of states is correct (invariants)",
      assert
        (all (\ (_, (_, (trans, _))) ->
               all (\ (_, (_, (_, (_, (f, (_, _)))))) ->
                     all (\ (x, upd) ->
                           less_nat x (n_vs bounds) &&
                             ball (vars_of_exp upd)
                               (\ i -> less_nat i (n_vs bounds)))
                       f)
                 trans)
          automata)
        "Variable set bounded (updates)",
      assert
        (all (\ (_, (_, (trans, _))) ->
               all (\ (_, (b, (_, (_, (_, (_, _)))))) ->
                     ball (vars_of_bexp b) (\ i -> less_nat i (n_vs bounds)))
                 trans)
          automata)
        "Variable set bounded (guards)",
      assert
        (all_interval_nat (\ i -> equal_nat (fst (nth bounds i)) i) zero_nat
          (n_vs bounds))
        "Bounds first index",
      assert (all (\ a -> less_nat a num_actions) broadcast)
        "Broadcast actions bounded",
      assert
        (all (\ (_, (_, (trans, _))) ->
               all (\ (_, (_, (_, (a, (_, (_, _)))))) ->
                     pred_act (\ aa -> less_nat aa num_actions) a)
                 trans)
          automata)
        "Actions bounded (transitions)",
      assert
        (all (\ (_, (_, (trans, _))) ->
               all (\ (_, (_, (g, (_, (_, (r, _)))))) ->
                     all (\ c -> less_nat zero_nat c && less_eq_nat c m) r &&
                       ball (collect_clock_pairs g)
                         (\ (c, x) ->
                           less_nat zero_nat c &&
                             less_eq_nat c m && less_eq_int zero_int x))
                 trans)
          automata)
        "Clock set bounded (transitions)",
      assert
        (all (\ (_, (_, (_, a))) ->
               all (\ (_, g) ->
                     ball (collect_clock_pairs g)
                       (\ (c, x) ->
                         less_nat zero_nat c &&
                           less_eq_nat c m && less_eq_int zero_int x))
                 a)
          automata)
        "Clock set bounded (invariants)",
      assert
        (all (\ (_, (_, (trans, _))) ->
               all (\ a ->
                     (case a of {
                       (_, (_, (g, (In aa, (_, (_, _)))))) ->
                         (if membera broadcast aa then null g else True);
                       (_, (_, (_, (Out _, (_, (_, _)))))) -> True;
                       (_, (_, (_, (Sil _, (_, (_, _)))))) -> True;
                     }))
                 trans)
          automata)
        "Broadcast receivers are unguarded",
      assert (all (\ (_, (u, (_, _))) -> null u) automata)
        "Urgency was removed"];

check_precond ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [[[Nat]]] ->
                [Nat] ->
                  [(Nat, Int)] ->
                    Formula Nat Nat Nat Int -> Result ([()], [()]);
check_precond broadcast bounds automata m num_states num_actions k l_0 s_0
  formula =
  combine2 (check_precond1 broadcast bounds automata m num_states num_actions)
    (check_precond2 broadcast bounds automata m num_states k l_0 s_0 formula);

map_cconstraint ::
  forall a b c d.
    (a -> b) -> (c -> d) -> [Acconstraint a c] -> [Acconstraint b d];
map_cconstraint f g xs = map (map_acconstraint f g) xs;

renum_cconstraint ::
  forall a b.
    (Countable a) => (a -> Nat) -> [Acconstraint a b] -> [Acconstraint Nat b];
renum_cconstraint renum_clocks = map_cconstraint renum_clocks id;

renum_reset :: forall a. (Countable a) => (a -> Nat) -> [a] -> [Nat];
renum_reset renum_clocks = map renum_clocks;

renum_bexp :: forall a b. (Countable a) => (a -> Nat) -> Bexp a b -> Bexp Nat b;
renum_bexp renum_vars = map_bexp renum_vars;

renum_exp :: forall a b. (Countable a) => (a -> Nat) -> Exp a b -> Exp Nat b;
renum_exp renum_vars = map_exp renum_vars;

renum_upd ::
  forall a b. (Countable a) => (a -> Nat) -> (a, Exp a b) -> (Nat, Exp Nat b);
renum_upd renum_vars = (\ (x, upd) -> (renum_vars x, renum_exp renum_vars upd));

renum_act :: forall a. (Countable a) => (a -> Nat) -> Act a -> Act Nat;
renum_act renum_acts = map_act renum_acts;

renum_automaton ::
  forall a b c d e f g h.
    (Countable a, Countable b, Countable c,
      Countable d) => (a -> Nat) ->
                        (b -> Nat) ->
                          (c -> Nat) ->
                            (Nat -> d -> Nat) ->
                              Nat ->
                                ([d], ([d],
([(d, (Bexp b e, ([Acconstraint c f], (Act a, ([(b, Exp b g)], ([c], d))))))],
  [(d, [Acconstraint c h])]))) ->
                                  ([Nat],
                                    ([Nat],
                                      ([(Nat,
  (Bexp Nat e,
    ([Acconstraint Nat f], (Act Nat, ([(Nat, Exp Nat g)], ([Nat], Nat))))))],
[(Nat, [Acconstraint Nat h])])));
renum_automaton renum_acts renum_vars renum_clocks renum_states i =
  (\ (committed, (urgent, (trans, inv))) ->
    let {
      committeda = map (renum_states i) committed;
      urgenta = map (renum_states i) urgent;
      transa =
        map (\ (l, (b, (g, (a, (upd, (r, la)))))) ->
              (renum_states i l,
                (renum_bexp renum_vars b,
                  (renum_cconstraint renum_clocks g,
                    (renum_act renum_acts a,
                      (map (renum_upd renum_vars) upd,
                        (renum_reset renum_clocks r, renum_states i la)))))))
          trans;
      inva =
        map (\ (l, g) -> (renum_states i l, renum_cconstraint renum_clocks g))
          inv;
    } in (committeda, (urgenta, (transa, inva))));

rename_network ::
  forall a b c d e f g h i j.
    (Countable a, Countable b, Countable e,
      Countable g) => [a] ->
                        [(b, (c, d))] ->
                          [([e], ([e], ([(e,
   (Bexp b f, ([Acconstraint g h], (Act a, ([(b, Exp b i)], ([g], e))))))],
 [(e, [Acconstraint g j])])))] ->
                            (a -> Nat) ->
                              (b -> Nat) ->
                                (g -> Nat) ->
                                  (Nat -> e -> Nat) ->
                                    ([Nat],
                                      ([([Nat],
  ([Nat],
    ([(Nat, (Bexp Nat f,
              ([Acconstraint Nat h],
                (Act Nat, ([(Nat, Exp Nat i)], ([Nat], Nat))))))],
      [(Nat, [Acconstraint Nat j])])))],
[(Nat, (c, d))]));
rename_network broadcast bounds automata renum_acts renum_vars renum_clocks
  renum_states =
  let {
    automataa =
      map_index zero_nat
        (renum_automaton renum_acts renum_vars renum_clocks renum_states)
        automata;
    broadcasta = map renum_acts broadcast;
    boundsa = map (\ (a, (b, c)) -> (renum_vars a, (b, c))) bounds;
  } in (broadcasta, (automataa, boundsa));

do_rename_mc ::
  forall a b c d e f g.
    (Showa c, Showa e, Showa f,
      Showa g) => ((a -> [Char]) ->
                    (([b], [c]) -> [Char]) ->
                      [Nat] ->
                        [(Nat, (Int, Int))] ->
                          [([Nat],
                             ([Nat],
                               ([(Nat, (Bexp Nat Int,
 ([Acconstraint Nat Int], (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                                 [(Nat, [Acconstraint Nat Int])])))] ->
                            Nat ->
                              (Nat -> Nat) ->
                                Nat ->
                                  [[[Nat]]] ->
                                    [Nat] ->
                                      [(Nat, Int)] ->
Formula Nat Nat Nat Int -> d) ->
                    Bool ->
                      [String] ->
                        [(String, (Int, Int))] ->
                          [([Nat],
                             ([Nat],
                               ([(Nat, (Bexp String Int,
 ([Acconstraint String Int],
   (Act String, ([(String, Exp String Int)], ([String], Nat))))))],
                                 [(Nat, [Acconstraint String Int])])))] ->
                            [[[Nat]]] ->
                              String ->
                                [Nat] ->
                                  [(String, Int)] ->
                                    Formula Nat Nat String Int ->
                                      Nat ->
(Nat -> Nat) ->
  Nat ->
    (String -> Nat) ->
      (String -> Nat) ->
        (String -> Nat) ->
          (Nat -> Nat -> Nat) ->
            (Nat -> b -> e) -> (Nat -> f) -> (a -> g) -> Maybe d;
do_rename_mc f dc broadcast bounds automata k urge l_0 s_0 formula m num_states
  num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states
  inv_renum_vars inv_renum_clocks =
  let {
    _ = println "Checking renaming";
    formulaa = (if dc then EX (Nota Trueb) else formula);
    renaming_valid =
      check_renaming broadcast bounds renum_acts renum_vars renum_clocks
        renum_states automata urge formulaa l_0 s_0;
    _ = println "Renaming network";
  } in (case rename_network broadcast bounds (map (conv_urge urge) automata)
               renum_acts renum_vars renum_clocks renum_states
         of {
         (broadcasta, (automataa, boundsa)) ->
           let {
             _ = trace_level (Int_of_integer (4 :: Integer))
                   (\ _ -> return "Automata after renaming");
             _ = map (\ a ->
                       trace_level (Int_of_integer (4 :: Integer))
                         (\ _ ->
                           return (implode (shows_prec_prod zero_nat a []))))
                   automataa;
             _ = println "Renaming formula";
             formulab =
               (if dc then EX (Nota Trueb)
                 else map_formula renum_states renum_vars id formulaa);
             _ = println "Renaming state";
             l_0a = map_index zero_nat renum_states l_0;
             s_0a = map (\ (x, a) -> (renum_vars x, a)) s_0;
             show_clock = (\ x -> shows_prec zero_nat x []) . inv_renum_clocks;
             show_statea = show_state inv_renum_states inv_renum_vars;
           } in (if is_result renaming_valid
                  then let {
                         _ = println "Checking preconditions";
                         r = check_precond broadcasta boundsa automataa m
                               num_states num_actions k l_0a s_0a formulab;
                         _ = (case r of {
                               Result _ -> ();
                               Error es ->
                                 let {
                                   _ = println "";
                                   _ = println
 "The following pre-conditions were not satisified:";
                                   _ = map println es;
                                 } in println "";
                             });
                         _ = println "Running precond_mc";
                         a = f show_clock show_statea broadcasta boundsa
                               automataa
                               m
                               num_states
                               num_actions
                               k
                               l_0a
                               s_0a
                               formulab;
                       } in Just a
                  else let {
                         _ = println
                               "The following conditions on the renaming were not satisfied:";
                         _ = map println (the_errors renaming_valid);
                       } in Nothing);
       });

mk_renaminga :: forall a. (Eq a, Showa a) => [a] -> Result (a -> Nat, Nat -> a);
mk_renaminga xs = mk_renaming (implode . (\ x -> shows_prec zero_nat x [])) xs;

show_dbm :: Nat -> (Nat -> String) -> [DBMEntry Int] -> [Char];
show_dbm num_clocks inv_renum_clocks =
  dbm_list_to_string num_clocks (show_clock inv_renum_clocks)
    (\ x -> shows_prec_int zero_nat x []);

show_lit :: forall a. (Showa a) => a -> String;
show_lit = implode . (\ x -> shows_prec zero_nat x []);

show_str :: forall a. (Showa a) => a -> String;
show_str = implode . (\ x -> shows_prec zero_nat x []);

extend_domain ::
  forall a b. (Eq a, One b, Plus b) => (a -> b) -> [a] -> b -> a -> b;
extend_domain m d n =
  (case fold (\ x (i, xs) ->
               (if membera d x then (plus i one, (x, plus i one) : xs)
                 else (i, xs)))
          d (n, [])
    of {
    (_, xs) -> let {
                 ma = map_of xs;
               } in (\ x -> (if membera d x then the (ma x) else m x));
  });

action_set ::
  forall a b c d.
    (Eq d) => [([a], ([a], ([(a, (Bexp b Int,
                                   ([Acconstraint c Int],
                                     (Act d, ([(b, Exp b Int)], ([c], a))))))],
                             [(a, [Acconstraint c Int])])))] ->
                [d] -> Set d;
action_set automata broadcast =
  sup_set
    (sup_seta
      (image
        (\ (_, (_, (trans, _))) ->
          sup_seta
            (image (\ (_, (_, (_, (a, (_, (_, _)))))) -> set_act a)
              (Set trans)))
        (Set automata)))
    (Set broadcast);

loc_set ::
  forall a b c d.
    (Eq a) => [([a], ([a], ([(a, (Bexp b Int,
                                   ([Acconstraint c Int],
                                     (Act d, ([(b, Exp b Int)], ([c], a))))))],
                             [(a, [Acconstraint c Int])])))] ->
                Nat -> Set a;
loc_set automata p =
  sup_seta
    (image (\ (l, (_, (_, (_, (_, (_, la)))))) -> insert l (insert la bot_set))
      (Set (fst (snd (snd (nth automata p))))));

make_renaming ::
  forall a.
    (Eq a,
      Showa a) => [String] ->
                    [([a], ([a], ([(a, (Bexp String Int,
 ([Acconstraint String Int],
   (Act String, ([(String, Exp String Int)], ([String], a))))))],
                                   [(a, [Acconstraint String Int])])))] ->
                      [(String, (Int, Int))] ->
                        Result
                          (Nat, (Nat -> Nat,
                                  (Nat, (String -> Nat,
  (String -> Nat,
    (String -> Nat,
      (Nat -> a -> Nat,
        (Nat -> Nat -> a, (Nat -> String, Nat -> String)))))))));
make_renaming =
  (\ broadcast automata bounds ->
    let {
      action_seta = list_of_set (action_set automata broadcast);
      clk_seta = list_of_set (clk_set automata);
      clk_setb = clk_seta ++ ["_urge"];
      loc_seta = (\ i -> list_of_set (loc_set automata i));
      loc_setaa =
        sup_seta
          (image
            (\ (_, (_, (t, _))) ->
              sup_seta
                (image
                  (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                    insert l (insert la bot_set))
                  (Set t)))
            (Set automata));
      loc_set_diff =
        (\ i -> list_of_set (minus_set loc_setaa (loc_set automata i)));
      _ = list_of_set loc_setaa;
      var_set =
        list_of_set
          (sup_set
            (sup_seta
              (image (\ s -> sup_seta (image vars_of_bexp s))
                (image (\ t -> image (fst . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata)))))
            (sup_seta
              (image
                (\ s ->
                  sup_seta
                    (image
                      (\ f ->
                        sup_seta
                          (image
                            (\ (x, e) ->
                              sup_set (insert x bot_set) (vars_of_exp e))
                            (Set f)))
                      s))
                (image
                  (\ t -> image ((((fst . snd) . snd) . snd) . snd) (Set t))
                  (image (\ (_, (_, (t, _))) -> t) (Set automata))))));
      n_ps = size_list automata;
      num_actions = size_list action_seta;
      m = size_list (remdups clk_setb);
      num_states_list =
        map (\ i -> size_list (remdups (loc_seta i))) (upt zero_nat n_ps);
      num_states = nth num_states_list;
      mk_renamingb = mk_renaming (\ x -> x);
    } in binda (combine2 (mk_renamingb action_seta)
                 (combine2 (mk_renamingb clk_setb) (mk_renamingb var_set)))
           (\ (a, b) ->
             (case a of {
               (renum_acts, _) ->
                 (\ (aa, ba) ->
                   (case aa of {
                     (renum_clocks, inv_renum_clocks) ->
                       (\ (renum_vars, inv_renum_vars) ->
                         let {
                           renum_clocksa = suc . renum_clocks;
                           inv_renum_clocksa =
                             (\ c ->
                               (if equal_nat c zero_nat then "0"
                                 else inv_renum_clocks (minus_nat c one_nat)));
                         } in binda (combine_map
                                      (\ i -> mk_renaminga (loc_seta i))
                                      (upt zero_nat n_ps))
                                (\ renum_states_list ->
                                  let {
                                    renum_states_lista =
                                      map fst renum_states_list;
                                    renum_states_listaa =
                                      map_index zero_nat
(\ i ma -> extend_domain ma (loc_set_diff i) (size_list (loc_seta i)))
renum_states_lista;
                                    renum_states = nth renum_states_listaa;
                                    inv_renum_states =
                                      nth (map snd renum_states_list);
                                  } in binda
 (assert (less_eq_set (image fst (Set bounds)) (Set var_set))
   "State variables are declared but do not appear in model")
 (\ _ ->
   Result
     (m, (num_states,
           (num_actions,
             (renum_acts,
               (renum_vars,
                 (renum_clocksa,
                   (renum_states,
                     (inv_renum_states,
                       (inv_renum_vars, inv_renum_clocksa))))))))))));
                   })
                     ba);
             })
               b));

check_prop_fail_impl ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => ((a, b) -> Heap.ST Heap.RealWorld Bool) ->
                    (b -> Heap.ST Heap.RealWorld b) ->
                      (b -> Heap.ST Heap.RealWorld String) ->
                        (a -> Heap.ST Heap.RealWorld String) ->
                          [a] ->
                            Hashtable a [b] ->
                              Heap.ST Heap.RealWorld (Maybe (a, b));
check_prop_fail_impl pi copyi show_dbm_impl show_loc_impl =
  (\ ai bi ->
    do { 
      a <- imp_nfoldli ai (\ sigma -> return (is_None sigma))
             (\ xb _ ->
               do { 
                 x <- hms_lookup ht_lookup (heap_map copyi) xb bi;
                 x_c <-
                   (case x of {
                     Nothing -> return Nothing;
                     Just x_e ->
                       do { 
                         x_g <-
                           imp_nfoldli x_e (\ sigma -> return (is_None sigma))
                             (\ xh _ ->
                               do { 
                                 xa <- copyi xh;
                                 x_i <- pi (xb, xa);
                                 return (if x_i then Nothing else Just xh)
                                })
                             Nothing;
                         return (case x_g of {
                                  Nothing -> Nothing;
                                  Just x_h -> Just (xb, x_h);
                                })
                        };
                   });
                 return (case x_c of {
                          Nothing -> Nothing;
                          Just a -> Just a;
                        })
                })
             Nothing;
      (case a of {
        Nothing -> return Nothing;
        Just (a1, a2) -> do { 
                           x <- copyi a2;
                           x_c <- do { 
                                    xa <- show_loc_impl a1;
                                    x_a <- show_dbm_impl x;
                                    return (mk_st_string xa x_a)
                                   };
                           _ <- Printing.printM "Prop failed for: ";
                           _ <- Printing.printM x_c;
                           return (Just (a1, a2))
                          };
      })
     });

print_sep :: () -> ();
print_sep =
  (\ () ->
    println
      (implode
        (replicate (nat_of_integer (100 :: Integer))
          (Char True False True True False True False False))));

split_size :: forall a. (a -> Nat) -> Nat -> Nat -> [a] -> [a] -> [[a]];
split_size f width uu acc [] = [acc];
split_size f width n acc (x : xs) =
  let {
    k = f x;
  } in (if less_nat n width then split_size f width (plus_nat n k) (x : acc) xs
         else acc : split_size f width k [x] xs);

split_k :: forall a b. Nat -> [(a, [b])] -> [[(a, [b])]];
split_k k xs =
  let {
    width = divide_nat (sum_list (map (size_list . snd) xs)) k;
    widtha =
      (if equal_nat (modulo_nat (size_list xs) k) zero_nat then width
        else plus_nat width one_nat);
  } in split_size (size_list . snd) widtha zero_nat [] xs;

split_eq_width :: forall a. Nat -> [a] -> [[a]];
split_eq_width n = split_size (\ _ -> one_nat) n zero_nat [];

split_ka :: forall a. Nat -> [a] -> [[a]];
split_ka k xs =
  let {
    width = divide_nat (size_list xs) k;
    widtha =
      (if equal_nat (modulo_nat (size_list xs) k) zero_nat then width
        else plus_nat width one_nat);
  } in split_eq_width widtha xs;

insert_every_nth :: forall a. Nat -> a -> [a] -> [a];
insert_every_nth n a xs =
  reverse
    (snd (fold (\ x (i, xsa) ->
                 (if equal_nat i n then (one_nat, a : x : xsa)
                   else (plus_nat i one_nat, x : xsa)))
           xs (one_nat, [])));

fw_upd_impl_inta ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Nat ->
        Nat ->
          Nat ->
            Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
fw_upd_impl_inta =
  (\ n ai bib bia bi ->
    do { 
      x <- mtx_get (suc n) ai (bia, bib);
      xa <- mtx_get (suc n) ai (bib, bi);
      let { xb = dbm_add_int x xa };
      xaa <- mtx_get (suc n) ai (bia, bi);
      (if less_DBMEntry xb xaa then mtx_set (suc n) ai (bia, bi) xb
        else return ai)
     });

fw_impl_inta ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
fw_impl_inta =
  (\ n ->
    imp_for_inta zero_nat (plus_nat n one_nat)
      (\ xb ->
        imp_for_inta zero_nat (plus_nat n one_nat)
          (\ xd ->
            imp_for_inta zero_nat (plus_nat n one_nat)
              (\ xf sigma -> fw_upd_impl_inta n sigma xb xd xf))));

normalize_dbm :: Nat -> [DBMEntry Int] -> [DBMEntry Int];
normalize_dbm m xs = run_heap (do { 
                                 dbm <- Heap.newListArray xs;
                                 fw_impl_inta m dbm >>= freeze
                                });

convert_dbm :: Bool -> Nat -> [DBMEntry Int] -> [DBMEntry Int];
convert_dbm urge m dbm =
  normalize_dbm m
    (take m dbm ++
      Le zero_int :
        insert_every_nth m INF (drop m dbm) ++
          (if urge then Le zero_int else INF) :
            replicate (minus_nat m one_nat) INF ++ [Le zero_int]);

simple_Network_Impl_nat ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat -> (Nat -> Nat) -> Nat -> Bool;
simple_Network_Impl_nat broadcast bounds automata m num_states num_actions =
  ((less_nat zero_nat m &&
     less_nat zero_nat (size_list automata) &&
       all_interval_nat
         (\ i ->
           (case nth automata i of {
             (_, (_, (trans, _))) ->
               all (\ (l, (_, (_, (_, (_, (_, la)))))) ->
                     less_nat l (num_states i) && less_nat la (num_states i))
                 trans;
           }))
         zero_nat (size_list automata)) &&
    all_interval_nat
      (\ i ->
        (case nth automata i of {
          (_, (_, (_, a))) -> all (\ (x, _) -> less_nat x (num_states i)) a;
        }))
      zero_nat (size_list automata) &&
      all (\ (_, (_, (trans, _))) ->
            all (\ (_, (_, (_, (_, (f, (_, _)))))) ->
                  all (\ (x, upd) ->
                        less_nat x (n_vs bounds) &&
                          ball (vars_of_exp upd)
                            (\ i -> less_nat i (n_vs bounds)))
                    f)
              trans)
        automata &&
        all (\ (_, (_, (trans, _))) ->
              all (\ (_, (b, (_, (_, (_, (_, _)))))) ->
                    ball (vars_of_bexp b) (\ i -> less_nat i (n_vs bounds)))
                trans)
          automata) &&
    (all_interval_nat (\ i -> equal_nat (fst (nth bounds i)) i) zero_nat
       (n_vs bounds) &&
      all (\ a -> less_nat a num_actions) broadcast &&
        all (\ (_, (_, (trans, _))) ->
              all (\ (_, (_, (_, (a, (_, (_, _)))))) ->
                    pred_act (\ aa -> less_nat aa num_actions) a)
                trans)
          automata) &&
      all (\ (_, (_, (trans, _))) ->
            all (\ (_, (_, (g, (_, (_, (r, _)))))) ->
                  all (\ c -> less_nat zero_nat c && less_eq_nat c m) r &&
                    ball (collect_clock_pairs g)
                      (\ (c, x) ->
                        less_nat zero_nat c &&
                          less_eq_nat c m && less_eq_int zero_int x))
              trans)
        automata &&
        all (\ (_, (_, (_, a))) ->
              all (\ (_, g) ->
                    ball (collect_clock_pairs g)
                      (\ (c, x) ->
                        less_nat zero_nat c &&
                          less_eq_nat c m && less_eq_int zero_int x))
                a)
          automata &&
          all (\ (_, (_, (trans, _))) ->
                all (\ a ->
                      (case a of {
                        (_, (_, (g, (In aa, (_, (_, _)))))) ->
                          (if membera broadcast aa then null g else True);
                        (_, (_, (_, (Out _, (_, (_, _)))))) -> True;
                        (_, (_, (_, (Sil _, (_, (_, _)))))) -> True;
                      }))
                  trans)
            automata;

split_kb :: forall a b. Nat -> [(a, [b])] -> [[a]];
split_kb k xs =
  let {
    width = divide_nat (sum_list (map (size_list . snd) xs)) k;
    widtha =
      (if equal_nat (modulo_nat (size_list xs) k) zero_nat then width
        else plus_nat width one_nat);
  } in map (map fst) (split_size (size_list . snd) widtha zero_nat [] xs);

map_of_debug ::
  forall a b. (Eq a, Showa a) => String -> [(a, b)] -> a -> Maybe b;
map_of_debug prefix m =
  let {
    ma = map_of m;
  } in (\ x ->
         (case ma x of {
           Nothing ->
             let {
               _ = println ((("Key error(" ++ prefix) ++ "): ") ++ show_lit x);
             } in Nothing;
           Just a -> Just a;
         }));

print_errors :: [String] -> Heap.ST Heap.RealWorld ();
print_errors es = do { 
                    _ <- fold_map (\ a -> Printing.printM a) es;
                    return ()
                   };

abstr_repair_impl_int ::
  Nat ->
    [Acconstraint Nat Int] ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
abstr_repair_impl_int =
  (\ m ai ->
    imp_nfoldli ai (\ _ -> return True)
      (\ aia bi -> do { 
                     x <- abstra_upd_impl_int m aia bi;
                     repair_pair_impl_int m x zero_nat (constraint_clk aia)
                    }));

e_op_impl ::
  Nat ->
    [Acconstraint Nat Int] ->
      [Nat] ->
        [Acconstraint Nat Int] ->
          [Acconstraint Nat Int] ->
            Heap.STArray Heap.RealWorld (DBMEntry Int) ->
              Heap.ST Heap.RealWorld
                (Heap.STArray Heap.RealWorld (DBMEntry Int));
e_op_impl =
  (\ m l_inv r g l_inva ma ->
    do { 
      m1 <- up_canonical_upd_impl_int m ma m;
      m2 <- abstr_repair_impl_int m l_inv m1;
      is_empty1 <- check_diag_impl_int m m2;
      m3 <- (if is_empty1
              then mtx_set (suc m) m2 (zero_nat, zero_nat) (Lt zero_int)
              else abstr_repair_impl_int m g m2);
      is_empty3 <- check_diag_impl_int m m3;
      (if is_empty3 then mtx_set (suc m) m3 (zero_nat, zero_nat) (Lt zero_int)
        else imp_nfoldli r (\ _ -> return True)
               (\ xc sigma ->
                 reset_canonical_upd_impl_int m sigma m xc zero_int)
               m3 >>=
               abstr_repair_impl_int m l_inva)
     });

array_freeze ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Heap.ST Heap.RealWorld (IArray.IArray a);
array_freeze = array_freezea;

array_freezea ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Heap.ST Heap.RealWorld (IArray.IArray a);
array_freezea a = array_freeze a;

n :: (Nat -> Nat) -> Nat -> Nat;
n num_states q = num_states q;

clkp_inv ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Nat -> Set (Nat, Int);
clkp_inv automata i l =
  sup_seta
    (image (\ g -> collect_clock_pairs (snd g))
      (Set (filter (\ (a, _) -> equal_nat a l)
             (snd (snd (snd (nth automata i)))))));

bound_inv ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Nat -> Nat -> Int;
bound_inv automata q c l =
  maxa (sup_set (insert zero_int bot_set)
         (sup_seta
           (image
             (\ (x, d) -> (if equal_nat x c then insert d bot_set else bot_set))
             (clkp_inv automata q l))));

clkp_seta ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Nat -> Set (Nat, Int);
clkp_seta automata i l =
  sup_set (clkp_inv automata i l)
    (sup_seta
      (image
        (\ (la, (_, (g, _))) ->
          (if equal_nat la l then collect_clock_pairs g else bot_set))
        (Set (fst (snd (snd (nth automata i)))))));

bound_g ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Nat -> Nat -> Int;
bound_g automata q c l =
  maxa (sup_set (insert zero_int bot_set)
         (sup_seta
           (image
             (\ (x, d) -> (if equal_nat x c then insert d bot_set else bot_set))
             (clkp_seta automata q l))));

bound ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Nat -> Nat -> Int;
bound automata q c l = max (bound_g automata q c l) (bound_inv automata q c l);

w :: [([Nat],
        ([Nat],
          ([(Nat, (Bexp Nat Int,
                    ([Acconstraint Nat Int],
                      (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
            [(Nat, [Acconstraint Nat Int])])))] ->
       (Nat -> Nat) -> Nat -> Nat -> Nat -> Nat -> Int;
w automata num_states q c la l =
  (if equal_nat la (n num_states q) then uminus_int (bound automata q c l)
    else zero_int);

v :: (Nat -> Nat) -> Nat -> Nat -> Bool;
v num_states q = (\ v -> less_eq_nat v (n num_states q));

resets ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Nat -> Nat -> [Nat];
resets automata q c l =
  fold (\ (l1, (_, (_, (_, (_, (r, la)))))) xs ->
         (if not (equal_nat l1 l) || (membera xs la || membera r c) then xs
           else la : xs))
    (fst (snd (snd (nth automata q)))) [];

ea :: [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat -> Nat -> Nat -> [Nat];
ea automata q c l = resets automata q c l;

e :: [([Nat],
        ([Nat],
          ([(Nat, (Bexp Nat Int,
                    ([Acconstraint Nat Int],
                      (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
            [(Nat, [Acconstraint Nat Int])])))] ->
       (Nat -> Nat) -> Nat -> Nat -> Nat -> [Nat];
e automata num_states q c l =
  (if equal_nat l (n num_states q) then upt zero_nat (n num_states q)
    else filter (\ la -> membera (ea automata q c la) l)
           (upt zero_nat (n num_states q)));

g :: [([Nat],
        ([Nat],
          ([(Nat, (Bexp Nat Int,
                    ([Acconstraint Nat Int],
                      (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
            [(Nat, [Acconstraint Nat Int])])))] ->
       (Nat -> Nat) ->
         Nat ->
           Nat ->
             Gen_g_impl_ext (Nat -> Bool) (Nat -> [Nat]) [Nat]
               (Nat -> Nat -> Int);
g automata num_states q c =
  Gen_g_impl_ext (v num_states q) (e automata num_states q c) [n num_states q]
    (w automata num_states q c);

local_ceiling_single ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    (Nat -> Nat) -> Nat -> Nat -> [Nat];
local_ceiling_single automata num_states q c =
  let {
    a = calc_shortest_scc_paths (g automata num_states q c) (n num_states q);
  } in map (\ aa -> (case aa of {
                      Nothing -> zero_nat;
                      Just x -> nat (uminus_int x);
                    }))
         a;

local_ceiling ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat -> (Nat -> Nat) -> [[[Nat]]];
local_ceiling broadcast bounds automata m num_states =
  app reverse
    (fold (\ q xs ->
            app (\ x -> reverse x : xs)
              (fold (\ l xsa ->
                      app (\ x -> (zero_nat : reverse x) : xsa)
                        (fold (\ c ->
                                (\ a ->
                                  nth (local_ceiling_single automata num_states
q c)
                                    l :
                                    a))
                          (upt one_nat (suc m)) []))
                (upt zero_nat (n num_states q)) []))
      (upt zero_nat (size_list automata)) []);

list_of_json_object :: JSON -> Result [([Char], JSON)];
list_of_json_object obj = (case obj of {
                            Object a -> Result a;
                            Arraya _ -> Error ["Not an object"];
                            Stringa _ -> Error ["Not an object"];
                            Int _ -> Error ["Not an object"];
                            Nata _ -> Error ["Not an object"];
                            Rat _ -> Error ["Not an object"];
                            Boolean _ -> Error ["Not an object"];
                            Null -> Error ["Not an object"];
                          });

nat_renaming_of_json ::
  String -> Nat -> JSON -> Result (Nat -> Nat, Nat -> Nat);
nat_renaming_of_json prefix max_id json =
  binda (list_of_json_object json)
    (\ vars ->
      binda (combine_map
              (\ (a, b) ->
                binda (parse lx_nat (implode a))
                  (\ aa -> binda (of_nat b) (\ ba -> Result (aa, ba))))
              vars)
        (\ varsa ->
          let {
            ids = image fst (Set varsa);
            missing = filter (\ i -> not (member i ids)) (upt zero_nat max_id);
            m = the . map_of_debug prefix varsa;
            ma = extend_domain m missing (size_list varsa);
          } in Result (ma, the . map_of_debug prefix (map swap varsa))));

renaming_of_jsona ::
  Maybe String -> String -> JSON -> Result (String -> Nat, Nat -> String);
renaming_of_jsona opt prefix json =
  binda (list_of_json_object json)
    (\ vars ->
      binda (combine_map
              (\ (a, b) -> binda (of_nat b) (\ ba -> Result (implode a, ba)))
              vars)
        (\ varsa ->
          let {
            varsb =
              varsa ++
                (case opt of {
                  Nothing -> [];
                  Just x ->
                    [(x, plus_nat (fold (max . snd) varsa zero_nat) one_nat)];
                });
          } in Result
                 (the . map_of_debug prefix varsb,
                   the . map_of_debug prefix (map swap varsb))));

renaming_of_json :: String -> JSON -> Result (String -> Nat, Nat -> String);
renaming_of_json = renaming_of_jsona Nothing;

convert_renaming ::
  (Nat -> Nat -> String) ->
    (String -> Nat) ->
      JSON ->
        Result
          (String -> Nat,
            (String -> Nat,
              (Nat -> Nat -> Nat,
                (Nat -> String, (Nat -> String, Nat -> Nat -> Nat)))));
convert_renaming ids_to_names process_names_to_index json =
  binda (of_object json)
    (\ jsona ->
      binda (geta jsona
              [Char False True True False True True True False,
                Char True False False False False True True False,
                Char False True False False True True True False,
                Char True True False False True True True False])
        (\ vars ->
          binda (renaming_of_json "var renaming" vars)
            (\ (var_renaming, var_inv) ->
              binda (geta jsona
                      [Char True True False False False True True False,
                        Char False False True True False True True False,
                        Char True True True True False True True False,
                        Char True True False False False True True False,
                        Char True True False True False True True False,
                        Char True True False False True True True False])
                (\ clocks ->
                  binda (renaming_of_jsona (Just "_urge") "clock renaming"
                          clocks)
                    (\ (clock_renaming, clock_inv) ->
                      binda (geta jsona
                              [Char False False False False True True True
                                 False,
                                Char False True False False True True True
                                  False,
                                Char True True True True False True True False,
                                Char True True False False False True True
                                  False,
                                Char True False True False False True True
                                  False,
                                Char True True False False True True True False,
                                Char True True False False True True True False,
                                Char True False True False False True True
                                  False,
                                Char True True False False True True True
                                  False])
                        (\ processes ->
                          binda (renaming_of_json "process renaming" processes)
                            (\ (process_renaming, _) ->
                              binda (geta jsona
                                      [Char False False True True False True
 True False,
Char True True True True False True True False,
Char True True False False False True True False,
Char True False False False False True True False,
Char False False True False True True True False,
Char True False False True False True True False,
Char True True True True False True True False,
Char False True True True False True True False,
Char True True False False True True True False])
                                (\ locations ->
                                  binda (list_of_json_object locations)
                                    (\ locationsa ->
                                      binda
(combine_map
  (\ (name, renaming) ->
    let {
      p_num = process_names_to_index (implode name);
    } in binda (assert (equal_nat (process_renaming (implode name)) p_num)
                 ("Process renamings do not agree on " ++ implode name))
           (\ _ ->
             let {
               max_id = nat_of_integer (1000 :: Integer);
             } in binda (nat_renaming_of_json ("process" ++ show_str p_num)
                          max_id renaming)
                    (\ renaminga -> Result (p_num, renaminga))))
  locationsa)
(\ locationsb ->
  let {
    location_renaming =
      the . map_of_debug "location" (map (\ (i, (f, _)) -> (i, f)) locationsb);
    location_inv =
      the . map_of_debug "location inv"
              (map (\ (i, (_, a)) -> (i, a)) locationsb);
  } in Result
         (var_renaming,
           (clock_renaming,
             (location_renaming,
               (var_inv, (clock_inv, location_inv)))))))))))))));

parse_compute ::
  String ->
    String ->
      Result
        ([String],
          ([(String, (Int, Int))],
            ([([Nat],
                ([Nat],
                  ([(Nat, (Bexp String Int,
                            ([Acconstraint String Int],
                              (Act String,
                                ([(String, Exp String Int)],
                                  ([String], Nat))))))],
                    [(Nat, [Acconstraint String Int])])))],
              ([[Nat]],
                ([[[Nat]]],
                  ([Nat],
                    ([(String, Int)],
                      (Formula Nat Nat String Int,
                        (Nat, (Nat -> Nat,
                                (Nat, (String -> Nat,
(String -> Nat,
  (String -> Nat,
    (Nat -> Nat -> Nat,
      (Nat -> Nat -> Nat, (Nat -> String, Nat -> String)))))))))))))))));
parse_compute model renaming =
  binda (parse json model)
    (\ modela ->
      binda (convert modela)
        (\ (ids_to_names,
             (process_names_to_index,
               (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
          -> binda (parse json renaming)
               (\ renaminga ->
                 binda (convert_renaming ids_to_names process_names_to_index
                         renaminga)
                   (\ (var_renaming,
                        (clock_renaming,
                          (location_renaming,
                            (inv_renum_vars,
                              (inv_renum_clocks, inv_renum_states)))))
                     -> binda (make_renaming broadcast automata bounds)
                          (\ (m, (num_states,
                                   (num_actions,
                                     (renum_acts,
                                       (_, (renum_clocks, (_, (_, (_, _)))))))))
                            -> binda (assert
                                       (equal_nat (renum_clocks "_urge") m)
                                       "Computed renaming: _urge is not last clock!")
                                 (\ _ ->
                                   let {
                                     renum_vars = var_renaming;
                                     renum_clocksa = clock_renaming;
                                     renum_states = location_renaming;
                                   } in binda
  (assert (equal_nat (renum_clocksa "_urge") m)
    "Given renaming: _urge is not last clock!")
  (\ _ ->
    let {
      _ = println "Renaming";
    } in (case rename_network broadcast bounds automata renum_acts renum_vars
                 renum_clocksa renum_states
           of {
           (broadcasta, (automataa, boundsa)) ->
             let {
               _ = println "Calculating ceiling";
               k = local_ceiling broadcasta boundsa automataa m num_states;
               urgent_locations =
                 map (\ (_, (urgent, (_, _))) -> urgent) automataa;
             } in Result
                    (broadcast,
                      (bounds,
                        (automata,
                          (urgent_locations,
                            (k, (l_0, (s_0,
(formula,
  (m, (num_states,
        (num_actions,
          (renum_acts,
            (renum_vars,
              (renum_clocksa,
                (renum_states,
                  (inv_renum_states,
                    (inv_renum_vars, inv_renum_clocks)))))))))))))))));
         }))))))));

certify_unreachable_impl2 ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => ((a, b) -> Heap.ST Heap.RealWorld Bool) ->
                    ((a, b) -> Heap.ST Heap.RealWorld Bool) ->
                      (b -> Heap.ST Heap.RealWorld b) ->
                        (b -> b -> Heap.ST Heap.RealWorld Bool) ->
                          (a -> [b] -> Heap.ST Heap.RealWorld [(a, [b])]) ->
                            Heap.ST Heap.RealWorld a ->
                              Heap.ST Heap.RealWorld b ->
                                ([a] -> [[a]]) ->
                                  [a] ->
                                    Heap.ST Heap.RealWorld (Hashtable a [b]) ->
                                      Bool;
certify_unreachable_impl2 fi pi copyi lei succsi l_0i s_0i splitteri l_list
  m_table =
  let {
    _ = start_timer ();
    b1 = run_heap
           (do { 
              m <- m_table;
              x <- l_0i;
              xa <- imp_nfoldli l_list (\ sigma -> return (not sigma))
                      (\ xb _ -> return (xb == x)) False;
              xaa <- l_0i;
              xb <- s_0i;
              x_a <- pi (xaa, xb);
              xab <- l_0i;
              a <- hms_lookup ht_lookup (heap_map copyi) xab m;
              (case a of {
                Nothing -> return False;
                Just x_d ->
                  do { 
                    x_f <-
                      imp_nfoldli x_d (\ sigma -> return (not sigma))
                        (\ xg _ -> do { 
                                     x_h <- s_0i;
                                     lei x_h xg
                                    })
                        False;
                    x_g <-
                      imp_nfoldli l_list return
                        (\ xba _ ->
                          do { 
                            aa <- hms_lookup ht_lookup (heap_map copyi) xba m;
                            (case aa of {
                              Nothing -> return True;
                              Just x_e ->
                                imp_nfoldli x_e return (\ xh _ -> pi (xba, xh))
                                  True;
                            })
                           })
                        True;
                    _ <- print_check_impl "Start state is in state list" xa;
                    _ <- print_check_impl "Start state fulfills property" x_a;
                    _ <- print_check_impl "Start state is subsumed" x_f;
                    _ <- print_check_impl "Check property" x_g;
                    return (xa && x_a && x_f && x_g)
                   };
              })
             });
    _ = save_time "Time for checking basic preconditions";
    _ = start_timer ();
    xs = run_map_heap
           (\ li ->
             do { 
               m <- m_table;
               imp_nfoldli li return
                 (\ xa _ ->
                   do { 
                     a <- hms_lookup ht_lookup (heap_map copyi) xa m;
                     (case a of {
                       Nothing -> return True;
                       Just x_c ->
                         do { 
                           x_d <- succsi xa x_c;
                           imp_nfoldli x_d return
                             (\ xg _ ->
                               (case xg of {
                                 (a1, a2) ->
                                   (if op_list_is_empty a2 then return True
                                     else do { 
    aa <- hms_lookup ht_lookup (heap_map copyi) a1 m;
    (case aa of {
      Nothing -> return False;
      Just x_k ->
        imp_nfoldli a2 return
          (\ xn _ ->
            imp_nfoldli x_k (\ sigma -> return (not sigma))
              (\ xp _ -> lei xn xp) False)
          True;
    })
   });
                               }))
                             True
                          };
                     })
                    })
                 True
              })
           (splitteri l_list);
    b2 = all id xs;
    _ = save_time "Time for state space invariant check";
    _ = print_check "State set invariant check" b2;
    _ = start_timer ();
    b3 = run_heap (m_table >>= check_final_impl fi copyi l_list);
    _ = save_time "Time to check final state predicate";
    _ = print_check "All check: " (b1 && b2);
    _ = print_check "Target property check: " b3;
  } in b1 && b2 && b3;

check_invariant_fail_impl ::
  forall a b.
    (Heapa a, Eq b, Hashable b,
      Heapa b) => (a -> Heap.ST Heap.RealWorld a) ->
                    (a -> a -> Heap.ST Heap.RealWorld Bool) ->
                      (b -> [a] -> Heap.ST Heap.RealWorld [(b, [a])]) ->
                        [b] ->
                          Hashtable b [a] ->
                            Heap.ST Heap.RealWorld
                              (Maybe (Sum (Sum (b, (b, [a])) (b, (b, [a])))
                                       (b, ([a], (b, (a, [a]))))));
check_invariant_fail_impl copyi lei succsi =
  (\ ai bi ->
    imp_nfoldli ai (\ sigma -> return (is_None sigma))
      (\ xb _ ->
        do { 
          x <- hms_lookup ht_lookup (heap_map copyi) xb bi;
          x_c <-
            (case x of {
              Nothing -> return Nothing;
              Just x_d ->
                do { 
                  x_e <- succsi xb x_d;
                  imp_nfoldli x_e (\ sigma -> return (is_None sigma))
                    (\ xh _ ->
                      do { 
                        x_i <-
                          (case xh of {
                            (a1, a2) ->
                              (if op_list_is_empty a2 then return Nothing
                                else do { 
                                       x_k <-
 imp_nfoldli ai (\ sigma -> return (not sigma)) (\ xba _ -> return (xba == a1))
   False;
                                       (if x_k
 then do { 
        a <- hms_lookup ht_lookup (heap_map copyi) a1 bi;
        (case a of {
          Nothing -> return (Just (Inl (Inr (xb, (a1, a2)))));
          Just x_m ->
            do { 
              aa <- imp_nfoldli a2 (\ sigma -> return (is_None sigma))
                      (\ xp _ ->
                        do { 
                          x_q <-
                            imp_nfoldli x_m (\ sigma -> return (not sigma))
                              (\ xr _ -> do { 
   x_s <- copyi xp;
   lei x_s xr
  })
                              False;
                          return (if x_q then Nothing else Just xp)
                         })
                      Nothing;
              (case aa of {
                Nothing -> return Nothing;
                Just x_p ->
                  do { 
                    x_q <- hms_lookup ht_lookup (heap_map copyi) xb bi;
                    return
                      (case x_q of {
                        Nothing -> Just (Inl (Inr (xb, (a1, x_m))));
                        Just x_r -> Just (Inr (xb, (x_r, (a1, (x_p, x_m)))));
                      })
                   };
              })
             };
        })
       }
 else return (Just (Inl (Inl (xb, (a1, a2))))))
                                      });
                          });
                        return (case x_i of {
                                 Nothing -> Nothing;
                                 Just a -> Just a;
                               })
                       })
                    Nothing
                 };
            });
          return (case x_c of {
                   Nothing -> Nothing;
                   Just a -> Just a;
                 })
         })
      Nothing);

array_all2 ::
  forall a b.
    Nat -> (a -> b -> Bool) -> IArray.IArray a -> IArray.IArray b -> Bool;
array_all2 n p asa bs =
  all_interval_nat (\ i -> p (sub asa i) (sub bs i)) zero_nat n;

print_fail :: String -> Bool -> ();
print_fail s b =
  (if b then () else println (s ++ " precondition check failed!"));

succs_impl ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          Nat ->
            Nat ->
              IArray.IArray (IArray.IArray [Acconstraint Nat Int]) ->
                ([Nat], [Int]) ->
                  [Heap.STArray Heap.RealWorld (DBMEntry Int)] ->
                    Heap.ST Heap.RealWorld
                      [(([Nat], [Int]),
                         [Heap.STArray Heap.RealWorld (DBMEntry Int)])];
succs_impl broadcast bounds automata m num_actions =
  let {
    trans_impl =
      let {
        trans_mapa = trans_map automata;
        trans_i_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                }))
              (trans_mapa i j));
        int_trans_from_loc_impl =
          (\ p l la s ->
            let {
              a = trans_i_map p l;
            } in map_filter
                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                     let {
                       sa = mk_updsi s f;
                     } in (if bvali s b && check_boundedi bounds sa
                            then Just (g,
(Internal aa, (r, (list_update la p lb, sa))))
                            else Nothing))
                   a);
        int_trans_from_vec_impl =
          (\ pairs l s ->
            concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
        int_trans_from_all_impl =
          (\ l s ->
            concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nat (size_list automata)));
        trans_out_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_in_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_out_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        trans_in_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        broad_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                      (upt zero_nat (size_list automata));
              out = map (\ p -> trans_out_broad_grouped p (nth l p))
                      (upt zero_nat (size_list automata));
              inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
              outa = map (map (filter (\ (b, _) -> bvali s b))) out;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            concatMap
                              (\ p ->
                                let {
                                  outs = nth (nth outa p) a;
                                } in (if null outs then []
                                       else let {
      combs = make_combs broadcast bounds automata p a inb;
      outsa = map (\ aa -> (p, aa)) outs;
      combsa =
        (if null combs then map (\ x -> [x]) outsa
          else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
      init = ([], (Broad a, ([], (l, s))));
    } in compute_upds_impl bounds init combsa))
                              (upt zero_nat (size_list automata)))
                          (upt zero_nat num_actions)
                   else concatMap
                          (\ a ->
                            let {
                              ins_committed =
                                map_filter
                                  (\ (p, _) ->
                                    (if not (null (nth (nth inb p) a))
                                      then Just p else Nothing))
                                  pairs;
                              always_committed =
                                less_nat one_nat (size_list ins_committed);
                            } in concatMap
                                   (\ p ->
                                     let {
                                       outs = nth (nth outa p) a;
                                     } in (if null outs then []
    else (if not always_committed &&
               (ins_committed == [p] || null ins_committed) &&
                 not (any (\ (q, _) -> equal_nat q p) pairs)
           then []
           else let {
                  combs = make_combs broadcast bounds automata p a inb;
                  outsa = map (\ aa -> (p, aa)) outs;
                  combsa =
                    (if null combs then map (\ x -> [x]) outsa
                      else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                  init = ([], (Broad a, ([], (l, s))));
                } in compute_upds_impl bounds init combsa)))
                                   (upt zero_nat (size_list automata)))
                          (upt zero_nat num_actions)));
        bin_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
              out = all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let {
                          in2 = all_actions_from_vec num_actions trans_in_map
                                  pairs;
                          out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        } in concatMap
                               (\ a ->
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                               (bin_actions broadcast num_actions) ++
                               concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                                 (bin_actions broadcast num_actions)));
        int_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
            } in (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s));
      } in (\ st ->
             int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
  } in (\ n_ps invs ->
         let {
           inv_fun =
             (\ (l, _) ->
               concatMap (\ i -> sub (sub invs i) (nth l i))
                 (upt zero_nat n_ps));
           e_op_impla =
             (\ l r g la -> e_op_impl m (inv_fun l) r g (inv_fun la));
         } in (\ l_s ma ->
                (if null ma then return []
                  else imp_nfoldli (trans_impl l_s) (\ _ -> return True)
                         (\ c sigma ->
                           (case c of {
                             (g, (_, (r, l_sa))) ->
                               do { 
                                 maa <- heap_map amtx_copy ma;
                                 ms <- imp_nfoldli maa (\ _ -> return True)
 (\ xb sigmaa -> do { 
                   x_c <- e_op_impla l_s r g l_sa xb;
                   x_e <- check_diag_impl_int m x_c;
                   return (if x_e then sigmaa else op_list_prepend x_c sigmaa)
                  })
 [];
                                 return (op_list_prepend (l_sa, ms) sigma)
                                };
                           }))
                         [])));

check_subsumed ::
  forall a.
    (Linordered_cancel_ab_monoid_add a, Eq a,
      Heapa a) => Nat ->
                    [Heap.STArray Heap.RealWorld (DBMEntry a)] ->
                      Int ->
                        Heap.STArray Heap.RealWorld (DBMEntry a) ->
                          Heap.ST Heap.RealWorld Bool;
check_subsumed n xs i m =
  do { 
    (_, a) <-
      imp_nfoldli xs (\ (_, b) -> return (not b))
        (\ ma (j, b) ->
          (if equal_int i j then return (plus_int j one_int, b)
            else do { 
                   ba <- dbm_subset_impl n m ma;
                   (if ba then return (j, True)
                     else return (plus_int j one_int, False))
                  }))
        (zero_int, False);
    return a
   };

array_unfreeze ::
  forall a.
    (Heapa a) => IArray.IArray a ->
                   Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
array_unfreeze = array_unfreezea;

array_unfreezea ::
  forall a.
    (Heapa a) => IArray.IArray a ->
                   Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
array_unfreezea a = array_unfreeze a;

imp_filter_index ::
  forall a.
    (Nat -> a -> Heap.ST Heap.RealWorld Bool) ->
      [a] -> Heap.ST Heap.RealWorld [a];
imp_filter_index p xs =
  do { 
    (_, xsa) <-
      imp_nfoldli xs (\ _ -> return True)
        (\ x (i, xsa) ->
          do { 
            b <- p i x;
            return (plus_nat i one_nat, (if b then x : xsa else xsa))
           })
        (zero_nat, []);
    return (reverse xsa)
   };

filter_dbm_list ::
  forall a.
    (Linordered_cancel_ab_monoid_add a, Eq a,
      Heapa a) => Nat ->
                    [Heap.STArray Heap.RealWorld (DBMEntry a)] ->
                      Heap.ST Heap.RealWorld
                        [Heap.STArray Heap.RealWorld (DBMEntry a)];
filter_dbm_list n xs =
  imp_filter_index (\ x m -> do { 
                               b <- check_subsumed n xs (int_of_nat x) m;
                               return (not b)
                              })
    xs;

certify_no_buechi_run_pure ::
  forall a b.
    (a -> [b] -> [(a, [b])]) ->
      [a] ->
        (b -> b -> Bool) ->
          [[a]] ->
            ((a, b) -> Bool) ->
              ((a, b) -> Bool) -> (a -> Maybe [(b, Nat)]) -> [(a, b)] -> Bool;
certify_no_buechi_run_pure get_succs li lei li_split pi fi mi initsi =
  let {
    check_all_pre_impl =
      time_it "Time for state set preconditions check"
        (\ _ ->
          let {
            b = all (\ (l_0, s_0) ->
                      (case mi l_0 of {
                        Nothing -> False;
                        Just xs ->
                          not (is_none (mi l_0)) &&
                            pi (l_0, s_0) && any (\ (s, _) -> lei s_0 s) xs;
                      }))
                  initsi;
            _ = print_check "Initial state check" b;
          } in b &&
            let {
              b = all id
                    (mapa (\ l -> (case op_map_lookup l mi of {
                                    Nothing -> True;
                                    Just a -> all (\ (s, _) -> pi (l, s)) a;
                                  }))
                      li);
              _ = print_check "State set preconditions check" b;
            } in b);
    check_invariant =
      time_it "Time for state space invariant check"
        (\ _ ->
          all id
            (mapa (all (\ l ->
                         (case mi l of {
                           Nothing -> True;
                           Just a ->
                             all (\ (x, i) ->
                                   all (\ (la, xs) ->
 (if null xs then True
   else (case mi la of {
          Nothing -> False;
          Just ys ->
            all (\ y ->
                  any (\ (z, j) ->
                        lei y z &&
                          (if fi (l, x) then less_nat i else less_eq_nat i) j)
                    ys)
              xs;
        })))
                                     (get_succs l [x]))
                               a;
                         })))
              li_split));
  } in (if check_all_pre_impl
         then let {
                b = check_invariant;
                _ = print_check "State space invariant check" b;
              } in b
         else False);

check_nonneg ::
  forall a.
    (Zero a, Eq a, Heapa a,
      Linorder a) => Nat ->
                       Heap.STArray Heap.RealWorld (DBMEntry a) ->
                         Heap.ST Heap.RealWorld Bool;
check_nonneg n m =
  imp_for_int zero_nat (plus_nat n one_nat) return
    (\ xc _ -> do { 
                 x_e <- mtx_get (suc n) m (zero_nat, xc);
                 return (less_eq_DBMEntry x_e (Le zero))
                })
    True;

make_stringa ::
  forall a.
    (Linordered_ab_group_add a,
      Heapa a) => (Nat -> [Char]) ->
                    (a -> [Char]) -> DBMEntry a -> Nat -> Nat -> [Char];
make_stringa show_clock show_num e i j =
  let {
    ia = (if less_nat zero_nat i then show_clock i
           else [Char False False False False True True False False]);
    ja = (if less_nat zero_nat j then show_clock j
           else [Char False False False False True True False False]);
  } in (case e of {
         Le a ->
           ia ++ [Char False False False False False True False False,
                   Char True False True True False True False False,
                   Char False False False False False True False False] ++
                   ja ++ [Char False False False False False True False False,
                           Char False False True True True True False False,
                           Char True False True True True True False False,
                           Char False False False False False True False
                             False] ++
                           show_num a;
         Lt a ->
           ia ++ [Char False False False False False True False False,
                   Char True False True True False True False False,
                   Char False False False False False True False False] ++
                   ja ++ [Char False False False False False True False False,
                           Char False False True True True True False False,
                           Char False False False False False True False
                             False] ++
                           show_num a;
         INF ->
           ia ++ [Char False False False False False True False False,
                   Char True False True True False True False False,
                   Char False False False False False True False False] ++
                   ja ++ [Char False False False False False True False False,
                           Char False False True True True True False False,
                           Char False False False False False True False False,
                           Char True False False True False True True False,
                           Char False True True True False True True False,
                           Char False True True False False True True False];
       });

simple_Network_Impl_nat_ceiling_start_state_axioms ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            [[[Nat]]] ->
              [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
simple_Network_Impl_nat_ceiling_start_state_axioms broadcast bounds automata m
  num_states k l_0 s_0 formula =
  ((all_interval_nat
      (\ i ->
        all (\ (l, g) ->
              ball (collect_clock_pairs g)
                (\ (x, ma) ->
                  less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
          (((snd . snd) . snd) (nth automata i)))
      zero_nat (size_list automata) &&
     all_interval_nat
       (\ i ->
         all (\ (l, (_, (g, _))) ->
               ball (collect_clock_pairs g)
                 (\ (x, ma) ->
                   less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
           (((fst . snd) . snd) (nth automata i)))
       zero_nat (size_list automata) &&
       all_interval_nat
         (\ i ->
           all (\ (l, (_, (_, (_, (_, (r, la)))))) ->
                 ball (minus_set (Set (upt zero_nat (plus_nat m one_nat)))
                        (Set r))
                   (\ c ->
                     less_eq_nat (nth (nth (nth k i) la) c)
                       (nth (nth (nth k i) l) c)))
             (((fst . snd) . snd) (nth automata i)))
         zero_nat (size_list automata)) &&
    equal_nat (size_list k) (size_list automata) &&
      all_interval_nat (\ i -> equal_nat (size_list (nth k i)) (num_states i))
        zero_nat (size_list automata) &&
        all (all (\ xxs -> equal_nat (size_list xxs) (plus_nat m one_nat)))
          k) &&
    (all_interval_nat
       (\ i ->
         all_interval_nat
           (\ l -> equal_nat (nth (nth (nth k i) l) zero_nat) zero_nat) zero_nat
           (num_states i))
       zero_nat (size_list automata) &&
      all (\ (_, (_, (_, inv))) -> distinct (map fst inv)) automata &&
        equal_set (image fst (Set s_0)) (image fst (Set bounds)) &&
          ball (image fst (Set s_0))
            (\ x ->
              less_eq_int (fst (the (map_of bounds x))) (the (map_of s_0 x)) &&
                less_eq_int (the (map_of s_0 x))
                  (snd (the (map_of bounds x))))) &&
      equal_nat (size_list l_0) (size_list automata) &&
        all_interval_nat
          (\ i ->
            member (nth l_0 i)
              (image fst (Set (((fst . snd) . snd) (nth automata i)))))
          zero_nat (size_list automata) &&
          less_eq_set (vars_of_formula formula)
            (Set (upt zero_nat (n_vs bounds)));

simple_Network_Impl_nat_urge_axioms ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Bool;
simple_Network_Impl_nat_urge_axioms automata =
  all (\ (_, (u, (_, _))) -> null u) automata;

simple_Network_Impl_nat_urge ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat -> (Nat -> Nat) -> Nat -> Bool;
simple_Network_Impl_nat_urge broadcast bounds automata m num_states num_actions
  = simple_Network_Impl_nat broadcast bounds automata m num_states
      num_actions &&
      simple_Network_Impl_nat_urge_axioms automata;

simple_Network_Impl_nat_ceiling_start_state ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [[[Nat]]] ->
                [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  simple_Network_Impl_nat_urge broadcast bounds automata m num_states
    num_actions &&
    simple_Network_Impl_nat_ceiling_start_state_axioms broadcast bounds automata
      m num_states k l_0 s_0 formula;

states_i ::
  [([Nat],
     ([Nat],
       ([(Nat, (Bexp Nat Int,
                 ([Acconstraint Nat Int],
                   (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
         [(Nat, [Acconstraint Nat Int])])))] ->
    Nat -> Set Nat;
states_i automata i =
  sup_seta
    (image (\ (l, (_, (_, (_, (_, (_, la)))))) -> insert l (insert la bot_set))
      (Set (fst (snd (snd (nth automata i))))));

certificate_checker_pre ::
  forall a b.
    [([Nat], [Int])] ->
      [(a, [[b]])] ->
        [Nat] ->
          [(Nat, (Int, Int))] ->
            [([Nat],
               ([Nat],
                 ([(Nat, (Bexp Nat Int,
                           ([Acconstraint Nat Int],
                             (Act Nat,
                               ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                   [(Nat, [Acconstraint Nat Int])])))] ->
              Nat ->
                (Nat -> Nat) ->
                  Nat ->
                    [[[Nat]]] ->
                      [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
certificate_checker_pre l_list m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let {
    _ = start_timer ();
    check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    _ = save_time "Time to check ceiling";
    n_ps = size_list automata;
    n_vsa = n_vs bounds;
    states_ia = map (states_i automata) (upt zero_nat n_ps);
    _ = start_timer ();
    check2 =
      all (\ (l, s) ->
            equal_nat (size_list l) n_ps &&
              all_interval_nat (\ i -> member (nth l i) (nth states_ia i))
                zero_nat n_ps &&
                equal_nat (size_list s) n_vsa && check_boundedi bounds s)
        l_list;
    _ = save_time "Time to check states";
    _ = start_timer ();
    n_sq = times_nat (suc m) (suc m);
    check3 =
      all (\ (_, a) -> all (\ ma -> equal_nat (size_list ma) n_sq) a) m_list;
    _ = save_time "Time to check DBMs";
    check4 = (case formula of {
               EX _ -> True;
               EG _ -> False;
               AX _ -> False;
               AG _ -> False;
               Leadsto _ _ -> False;
             });
  } in check1 && check2 && check3 && check4;

dbm_subset_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) -> Heap.ST Heap.RealWorld Bool;
dbm_subset_impl_int =
  (\ n ai bi -> do { 
                  x <- check_diag_impl_inta n n ai;
                  (if x then return True else dbm_subset_impl_inta n ai bi)
                 });

certify_unreachable_impl_inner ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => ((a, b) -> Heap.ST Heap.RealWorld Bool) ->
                    ((a, b) -> Heap.ST Heap.RealWorld Bool) ->
                      (b -> Heap.ST Heap.RealWorld b) ->
                        (b -> b -> Heap.ST Heap.RealWorld Bool) ->
                          (a -> [b] -> Heap.ST Heap.RealWorld [(a, [b])]) ->
                            Heap.ST Heap.RealWorld a ->
                              Heap.ST Heap.RealWorld b ->
                                ([a] -> [[a]]) ->
                                  [a] ->
                                    Hashtable a [b] ->
                                      Heap.ST Heap.RealWorld Bool;
certify_unreachable_impl_inner fi pi copyi lei succsi l_0i s_0i splitteri =
  (\ ai bi ->
    do { 
      _ <- start_timer_impl ();
      x <- l_0i;
      xa <- imp_nfoldli ai (\ sigma -> return (not sigma))
              (\ xb _ -> return (xb == x)) False;
      xaa <- l_0i;
      xb <- s_0i;
      xab <- pi (xaa, xb);
      xba <- l_0i;
      xbb <- hms_lookup ht_lookup (heap_map copyi) xba bi;
      xc <- (case xbb of {
              Nothing -> return False;
              Just x_d ->
                do { 
                  x_f <-
                    imp_nfoldli x_d (\ sigma -> return (not sigma))
                      (\ xg _ -> do { 
                                   x_h <- s_0i;
                                   lei x_h xg
                                  })
                      False;
                  x_g <-
                    imp_nfoldli ai return
                      (\ xbc _ ->
                        do { 
                          a <- hms_lookup ht_lookup (heap_map copyi) xbc bi;
                          (case a of {
                            Nothing -> return True;
                            Just x_e ->
                              imp_nfoldli x_e return (\ xh _ -> pi (xbc, xh))
                                True;
                          })
                         })
                      True;
                  _ <- print_check_impl "Start state is in state list" xa;
                  _ <- print_check_impl "Start state fulfills property" xab;
                  _ <- print_check_impl "Start state is subsumed" x_f;
                  _ <- print_check_impl "Check property" x_g;
                  return (xa && xab && x_f && x_g)
                 };
            });
      x_a <-
        (if xc
          then do { 
                 x_b <-
                   do { 
                     bs <- parallel_fold_map
                             (\ l ->
                               imp_nfoldli l return
                                 (\ xac _ ->
                                   do { 
                                     a <- hms_lookup ht_lookup (heap_map copyi)
    xac bi;
                                     (case a of {
                                       Nothing -> return True;
                                       Just x_c ->
 do { 
   x_d <- succsi xac x_c;
   imp_nfoldli x_d return
     (\ xg _ ->
       (case xg of {
         (a1, a2) ->
           (if op_list_is_empty a2 then return True
             else do { 
                    aa <- hms_lookup ht_lookup (heap_map copyi) a1 bi;
                    (case aa of {
                      Nothing -> return False;
                      Just x_k ->
                        imp_nfoldli a2 return
                          (\ xn _ ->
                            imp_nfoldli x_k (\ sigma -> return (not sigma))
                              (\ xp _ -> lei xn xp) False)
                          True;
                    })
                   });
       }))
     True
  };
                                     })
                                    })
                                 True)
                             (splitteri ai);
                     return (all id bs)
                    };
                 _ <- print_check_impl "State set invariant check" x_b;
                 return x_b
                }
          else return False);
      _ <- save_time_impl "Time for state space invariant check";
      _ <- start_timer_impl ();
      x_d <-
        imp_nfoldli ai return
          (\ xbc _ ->
            do { 
              a <- hms_lookup ht_lookup (heap_map copyi) xbc bi;
              (case a of {
                Nothing -> return True;
                Just x_e ->
                  imp_nfoldli x_e return (\ xh _ -> do { 
              x_i <- fi (xbc, xh);
              return (not x_i)
             })
                    True;
              })
             })
          True;
      _ <- save_time_impl "Time to check final state predicate";
      _ <- print_check_impl "All check: " x_a;
      _ <- print_check_impl "Target property check: " x_d;
      return (x_a && x_d)
     });

unreachability_checker ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  Formula Nat Nat Nat Int ->
                    [([Nat], [Int])] ->
                      [(([Nat], [Int]), [[DBMEntry Int]])] ->
                        Nat -> Heap.ST Heap.RealWorld Bool;
unreachability_checker broadcast bounds automata m num_states num_actions l_0
  s_0 formula l_list m_list num_split =
  let {
    states_ia = map (states_i automata) (upt zero_nat (size_list automata));
    check_states =
      (\ (l, s) ->
        (equal_nat (size_list l) (size_list automata) &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            (size_list automata)) &&
          equal_nat (size_list s) (n_vs bounds) && check_boundedi bounds s);
    fi = (\ xi -> return (case xi of {
                           ((a, b), _) -> hd_of_formulai formula a b;
                         }));
    pi = (\ (a1, a2) ->
           do { 
             x <- imp_for_int zero_nat (plus_nat m one_nat) return
                    (\ xc _ ->
                      imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xf _ ->
                          imp_for_int zero_nat (plus_nat m one_nat) return
                            (\ xj _ ->
                              do { 
                                x_i <- mtx_get (suc m) a2 (xc, xj);
                                x <- mtx_get (suc m) a2 (xc, xf);
                                xa <- mtx_get (suc m) a2 (xf, xj);
                                return (dbm_le_int x_i (dbm_add_int x xa))
                               })
                            True)
                        True)
                    True;
             xa <- check_diag_impl_int m a2;
             xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_d <- mtx_get (suc m) a2 (xc, xc);
                                  return (dbm_le_int x_d (Le zero_int))
                                 })
                     True;
             xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                  return (dbm_le_int x_e (Le zero_int))
                                 })
                     True;
             return (check_states a1 && (x || xa) && xb && xc)
            });
    copyi = amtx_copy;
    lei = dbm_subset_impl_int m;
    l_0i = return (l_0, map (the . map_of s_0) (upt zero_nat (n_vs bounds)));
    s_0i = amtx_dflt (suc m) (suc m) (Le zero_int);
    succsi =
      let {
        n_ps = size_list automata;
        invs =
          IArray.of_list
            (map (\ i ->
                   let {
                     ma = default_map_of [] (snd (snd (snd (nth automata i))));
                     mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
                   } in mb)
              (upt zero_nat n_ps));
        inv_fun =
          (\ (l, _) ->
            concatMap (\ i -> sub (sub invs i) (nth l i)) (upt zero_nat n_ps));
        trans_mapa = trans_map automata;
        trans_i_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                }))
              (trans_mapa i j));
        int_trans_from_loc_impl =
          (\ p l la s ->
            let {
              a = trans_i_map p l;
            } in map_filter
                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                     let {
                       sa = mk_updsi s f;
                     } in (if bvali s b && check_boundedi bounds sa
                            then Just (g,
(Internal aa, (r, (list_update la p lb, sa))))
                            else Nothing))
                   a);
        int_trans_from_vec_impl =
          (\ pairs l s ->
            concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
        int_trans_from_all_impl =
          (\ l s ->
            concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nat n_ps));
        trans_out_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_in_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_out_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        trans_in_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        broad_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              out = map (\ p -> trans_out_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
              outa = map (map (filter (\ (b, _) -> bvali s b))) out;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            concatMap
                              (\ p ->
                                let {
                                  outs = nth (nth outa p) a;
                                } in (if null outs then []
                                       else let {
      combs = make_combs broadcast bounds automata p a inb;
      outsa = map (\ aa -> (p, aa)) outs;
      combsa =
        (if null combs then map (\ x -> [x]) outsa
          else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
      init = ([], (Broad a, ([], (l, s))));
    } in compute_upds_impl bounds init combsa))
                              (upt zero_nat n_ps))
                          (upt zero_nat num_actions)
                   else concatMap
                          (\ a ->
                            let {
                              ins_committed =
                                map_filter
                                  (\ (p, _) ->
                                    (if not (null (nth (nth inb p) a))
                                      then Just p else Nothing))
                                  pairs;
                              always_committed =
                                less_nat one_nat (size_list ins_committed);
                            } in concatMap
                                   (\ p ->
                                     let {
                                       outs = nth (nth outa p) a;
                                     } in (if null outs then []
    else (if not always_committed &&
               (ins_committed == [p] || null ins_committed) &&
                 not (any (\ (q, _) -> equal_nat q p) pairs)
           then []
           else let {
                  combs = make_combs broadcast bounds automata p a inb;
                  outsa = map (\ aa -> (p, aa)) outs;
                  combsa =
                    (if null combs then map (\ x -> [x]) outsa
                      else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                  init = ([], (Broad a, ([], (l, s))));
                } in compute_upds_impl bounds init combsa)))
                                   (upt zero_nat n_ps))
                          (upt zero_nat num_actions)));
        bin_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
              out = all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let {
                          in2 = all_actions_from_vec num_actions trans_in_map
                                  pairs;
                          out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        } in concatMap
                               (\ a ->
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                               (bin_actions broadcast num_actions) ++
                               concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                                 (bin_actions broadcast num_actions)));
        int_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
            } in (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s));
        trans_impl =
          (\ st ->
            int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
        e_op_impl =
          (\ ai bic bib bia bi ->
            do { 
              x <- up_canonical_upd_impl_int m bi m;
              xa <- imp_nfoldli (inv_fun ai) (\ _ -> return True)
                      (\ aia bid ->
                        do { 
                          xa <- abstra_upd_impl_int m aia bid;
                          repair_pair_impl_int m xa zero_nat
                            (constraint_clk aia)
                         })
                      x;
              xaa <- check_diag_impl_int m xa;
              x_a <-
                (if xaa
                  then mtx_set (suc m) xa (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bib (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            })
                         xa);
              x_b <- check_diag_impl_int m x_a;
              (if x_b
                then mtx_set (suc m) x_a (zero_nat, zero_nat) (Lt zero_int)
                else imp_nfoldli bic (\ _ -> return True)
                       (\ xc sigma ->
                         reset_canonical_upd_impl_int m sigma m xc zero_int)
                       x_a >>=
                       imp_nfoldli (inv_fun bia) (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            }))
             });
      } in (\ ai bi ->
             (if null bi then return []
               else imp_nfoldli (trans_impl ai) (\ _ -> return True)
                      (\ xc sigma ->
                        (case xc of {
                          (a1, (_, (a1b, a2b))) ->
                            do { 
                              x <- heap_map amtx_copy bi;
                              x_d <-
                                imp_nfoldli x (\ _ -> return True)
                                  (\ xb sigmaa ->
                                    do { 
                                      x_c <-
pR_CONST e_op_impl ai a1b a1 a2b xb;
                                      x_e <- check_diag_impl_int m x_c;
                                      return
(if x_e then sigmaa else op_list_prepend x_c sigmaa)
                                     })
                                  [];
                              return (op_list_prepend (a2b, x_d) sigma)
                             };
                        }))
                      []));
    _ = start_timer ();
  } in do { 
         m_table <-
           ht_new >>=
             imp_nfoldli m_list (\ _ -> return True)
               (\ xc sigma ->
                 do { 
                   x_e <-
                     imp_nfoldli (snd xc) (\ _ -> return True)
                       (\ xg sigmaa -> do { 
 x_g <- Heap.newListArray xg;
 return (x_g : sigmaa)
                                        })
                       [];
                   ht_update (fst xc) x_e sigma
                  });
         let { _ = save_time "Time for loading certificate" };
         certify_unreachable_impl_inner fi pi copyi lei succsi l_0i s_0i
           (split_ka num_split) l_list m_table >>=
           return
        };

abstr_upd_impl_int ::
  Nat ->
    [Acconstraint Nat Int] ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
abstr_upd_impl_int =
  (\ n ai -> imp_nfoldli ai (\ _ -> return True) (abstra_upd_impl_int n));

abstr_FW_impl_int ::
  Nat ->
    [Acconstraint Nat Int] ->
      Heap.STArray Heap.RealWorld (DBMEntry Int) ->
        Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
abstr_FW_impl_int =
  (\ n ai bi -> abstr_upd_impl_int n ai bi >>= fw_impl_inta n);

down_impl_int ::
  Nat ->
    Heap.STArray Heap.RealWorld (DBMEntry Int) ->
      Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld (DBMEntry Int));
down_impl_int =
  (\ n ->
    imp_for_inta one_nat (suc n)
      (\ xb sigma ->
        imp_for_inta one_nat (suc n)
          (\ xe sigmaa -> do { 
                            x_f <- mtx_get (suc n) sigma (xe, xb);
                            return (min_int_entry x_f sigmaa)
                           })
          (Le zero_int) >>=
          mtx_set (suc n) sigma (zero_nat, xb)));

no_deadlock_certifier ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  [([Nat], [Int])] ->
                    [(([Nat], [Int]), [[DBMEntry Int]])] ->
                      Nat -> Heap.ST Heap.RealWorld Bool;
no_deadlock_certifier broadcast bounds automata m num_states num_actions l_0 s_0
  l_list m_list num_split =
  let {
    states_ia = map (states_i automata) (upt zero_nat (size_list automata));
    check_states =
      (\ (l, s) ->
        (equal_nat (size_list l) (size_list automata) &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            (size_list automata)) &&
          equal_nat (size_list s) (n_vs bounds) && check_boundedi bounds s);
    fi = (\ (l, ma) ->
           do { 
             r <- let {
                    n_ps = size_list automata;
                    invs =
                      IArray.of_list
                        (map (\ i ->
                               let {
                                 mb = default_map_of []
(snd (snd (snd (nth automata i))));
                                 mc = IArray.of_list
(map mb (upt zero_nat (num_states i)));
                               } in mc)
                          (upt zero_nat n_ps));
                    inv_fun =
                      (\ (la, _) ->
                        concatMap (\ i -> sub (sub invs i) (nth la i))
                          (upt zero_nat n_ps));
                    trans_impl =
                      let {
                        trans_mapa = trans_map automata;
                        trans_i_map =
                          (\ i j ->
                            map_filter
                              (\ a ->
                                (case a of {
                                  (_, (_, (In _, (_, _)))) -> Nothing;
                                  (_, (_, (Out _, (_, _)))) -> Nothing;
                                  (b, (g, (Sil aa, (mb, la)))) ->
                                    Just (b, (g, (aa, (mb, la))));
                                }))
                              (trans_mapa i j));
                        int_trans_from_loc_impl =
                          (\ p la laa s ->
                            let {
                              a = trans_i_map p la;
                            } in map_filter
                                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                                     let {
                                       sa = mk_updsi s f;
                                     } in (if bvali s b &&
        check_boundedi bounds sa
    then Just (g, (Internal aa, (r, (list_update laa p lb, sa)))) else Nothing))
                                   a);
                        int_trans_from_vec_impl =
                          (\ pairs la s ->
                            concatMap
                              (\ (p, laa) -> int_trans_from_loc_impl p laa la s)
                              pairs);
                        int_trans_from_all_impl =
                          (\ la s ->
                            concatMap
                              (\ p -> int_trans_from_loc_impl p (nth la p) la s)
                              (upt zero_nat n_ps));
                        trans_out_map =
                          (\ i j ->
                            map_filter
                              (\ a ->
                                (case a of {
                                  (_, (_, (In _, (_, _)))) -> Nothing;
                                  (b, (g, (Out aa, (mb, la)))) ->
                                    Just (b, (g, (aa, (mb, la))));
                                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                                }))
                              (trans_mapa i j));
                        trans_in_map =
                          (\ i j ->
                            map_filter
                              (\ a ->
                                (case a of {
                                  (b, (g, (In aa, (mb, la)))) ->
                                    Just (b, (g, (aa, (mb, la))));
                                  (_, (_, (Out _, (_, _)))) -> Nothing;
                                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                                }))
                              (trans_mapa i j));
                        trans_out_broad_grouped =
                          (\ i j ->
                            actions_by_statea num_actions
                              (map_filter
                                (\ a ->
                                  (case a of {
                                    (_, (_, (In _, (_, _)))) -> Nothing;
                                    (b, (g, (Out aa, (mb, la)))) ->
                                      (if membera broadcast aa
then Just (b, (g, (aa, (mb, la)))) else Nothing);
                                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                                  }))
                                (trans_mapa i j)));
                        trans_in_broad_grouped =
                          (\ i j ->
                            actions_by_statea num_actions
                              (map_filter
                                (\ a ->
                                  (case a of {
                                    (b, (g, (In aa, (mb, la)))) ->
                                      (if membera broadcast aa
then Just (b, (g, (aa, (mb, la)))) else Nothing);
                                    (_, (_, (Out _, (_, _)))) -> Nothing;
                                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                                  }))
                                (trans_mapa i j)));
                        broad_trans_impl =
                          (\ (la, s) ->
                            let {
                              pairs =
                                get_committed broadcast bounds automata la;
                              ina = map (\ p ->
  trans_in_broad_grouped p (nth la p))
                                      (upt zero_nat n_ps);
                              out = map (\ p ->
  trans_out_broad_grouped p (nth la p))
                                      (upt zero_nat n_ps);
                              inb = map (map (filter (\ (b, _) -> bvali s b)))
                                      ina;
                              outa =
                                map (map (filter (\ (b, _) -> bvali s b))) out;
                            } in (if null pairs
                                   then concatMap
  (\ a ->
    concatMap
      (\ p ->
        let {
          outs = nth (nth outa p) a;
        } in (if null outs then []
               else let {
                      combs = make_combs broadcast bounds automata p a inb;
                      outsa = map (\ aa -> (p, aa)) outs;
                      combsa =
                        (if null combs then map (\ x -> [x]) outsa
                          else concatMap (\ x -> map (\ aa -> x : aa) combs)
                                 outsa);
                      init = ([], (Broad a, ([], (la, s))));
                    } in compute_upds_impl bounds init combsa))
      (upt zero_nat n_ps))
  (upt zero_nat num_actions)
                                   else concatMap
  (\ a ->
    let {
      ins_committed =
        map_filter
          (\ (p, _) ->
            (if not (null (nth (nth inb p) a)) then Just p else Nothing))
          pairs;
      always_committed = less_nat one_nat (size_list ins_committed);
    } in concatMap
           (\ p ->
             let {
               outs = nth (nth outa p) a;
             } in (if null outs then []
                    else (if not always_committed &&
                               (ins_committed == [p] || null ins_committed) &&
                                 not (any (\ (q, _) -> equal_nat q p) pairs)
                           then []
                           else let {
                                  combs =
                                    make_combs broadcast bounds automata p a
                                      inb;
                                  outsa = map (\ aa -> (p, aa)) outs;
                                  combsa =
                                    (if null combs then map (\ x -> [x]) outsa
                                      else concatMap
     (\ x -> map (\ aa -> x : aa) combs) outsa);
                                  init = ([], (Broad a, ([], (la, s))));
                                } in compute_upds_impl bounds init combsa)))
           (upt zero_nat n_ps))
  (upt zero_nat num_actions)));
                        bin_trans_impl =
                          (\ (la, s) ->
                            let {
                              pairs =
                                get_committed broadcast bounds automata la;
                              ina = all_actions_by_state broadcast bounds
                                      automata num_actions trans_in_map la;
                              out = all_actions_by_state broadcast bounds
                                      automata num_actions trans_out_map la;
                            } in (if null pairs
                                   then concatMap
  (\ a -> pairs_by_action_impl bounds la s (nth out a) (nth ina a))
  (bin_actions broadcast num_actions)
                                   else let {
  in2 = all_actions_from_vec num_actions trans_in_map pairs;
  out2 = all_actions_from_vec num_actions trans_out_map pairs;
} in concatMap (\ a -> pairs_by_action_impl bounds la s (nth out a) (nth in2 a))
       (bin_actions broadcast num_actions) ++
       concatMap
         (\ a -> pairs_by_action_impl bounds la s (nth out2 a) (nth ina a))
         (bin_actions broadcast num_actions)));
                        int_trans_impl =
                          (\ (la, s) ->
                            let {
                              pairs =
                                get_committed broadcast bounds automata la;
                            } in (if null pairs
                                   then int_trans_from_all_impl la s
                                   else int_trans_from_vec_impl pairs la s));
                      } in (\ st ->
                             int_trans_impl st ++
                               bin_trans_impl st ++ broad_trans_impl st);
                  } in (\ ai bi ->
                         do { 
                           x <- imp_nfoldli (trans_impl ai) (\ _ -> return True)
                                  (\ xb sigma ->
                                    do { 
                                      x <- v_dbm_impl m;
                                      xa <-
abstr_FW_impl_int m (inv_fun (snd (snd (snd xb)))) x;
                                      xc <-
pre_reset_list_impl m xa (fst (snd (snd xb)));
                                      xd <- abstr_FW_impl_int m (fst xb) xc;
                                      xe <- abstr_FW_impl_int m (inv_fun ai) xd;
                                      x_c <- down_impl_int m xe;
                                      return (x_c : sigma)
                                     })
                                  [];
                           dbm_subset_fed_impl m bi (op_list_rev x)
                          })
                    l
                    ma;
             return (not r)
            });
    pi = (\ (a1, a2) ->
           do { 
             x <- imp_for_int zero_nat (plus_nat m one_nat) return
                    (\ xc _ ->
                      imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xf _ ->
                          imp_for_int zero_nat (plus_nat m one_nat) return
                            (\ xj _ ->
                              do { 
                                x_i <- mtx_get (suc m) a2 (xc, xj);
                                x <- mtx_get (suc m) a2 (xc, xf);
                                xa <- mtx_get (suc m) a2 (xf, xj);
                                return (dbm_le_int x_i (dbm_add_int x xa))
                               })
                            True)
                        True)
                    True;
             xa <- check_diag_impl_int m a2;
             xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_d <- mtx_get (suc m) a2 (xc, xc);
                                  return (dbm_le_int x_d (Le zero_int))
                                 })
                     True;
             xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                  return (dbm_le_int x_e (Le zero_int))
                                 })
                     True;
             return (check_states a1 && (x || xa) && xb && xc)
            });
    copyi = amtx_copy;
    lei = dbm_subset_impl_int m;
    l_0i = return (l_0, map (the . map_of s_0) (upt zero_nat (n_vs bounds)));
    s_0i = amtx_dflt (suc m) (suc m) (Le zero_int);
    succsi =
      let {
        n_ps = size_list automata;
        invs =
          IArray.of_list
            (map (\ i ->
                   let {
                     ma = default_map_of [] (snd (snd (snd (nth automata i))));
                     mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
                   } in mb)
              (upt zero_nat n_ps));
        inv_fun =
          (\ (l, _) ->
            concatMap (\ i -> sub (sub invs i) (nth l i)) (upt zero_nat n_ps));
        trans_mapa = trans_map automata;
        trans_i_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                }))
              (trans_mapa i j));
        int_trans_from_loc_impl =
          (\ p l la s ->
            let {
              a = trans_i_map p l;
            } in map_filter
                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                     let {
                       sa = mk_updsi s f;
                     } in (if bvali s b && check_boundedi bounds sa
                            then Just (g,
(Internal aa, (r, (list_update la p lb, sa))))
                            else Nothing))
                   a);
        int_trans_from_vec_impl =
          (\ pairs l s ->
            concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
        int_trans_from_all_impl =
          (\ l s ->
            concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nat n_ps));
        trans_out_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_in_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_out_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        trans_in_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        broad_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              out = map (\ p -> trans_out_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
              outa = map (map (filter (\ (b, _) -> bvali s b))) out;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            concatMap
                              (\ p ->
                                let {
                                  outs = nth (nth outa p) a;
                                } in (if null outs then []
                                       else let {
      combs = make_combs broadcast bounds automata p a inb;
      outsa = map (\ aa -> (p, aa)) outs;
      combsa =
        (if null combs then map (\ x -> [x]) outsa
          else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
      init = ([], (Broad a, ([], (l, s))));
    } in compute_upds_impl bounds init combsa))
                              (upt zero_nat n_ps))
                          (upt zero_nat num_actions)
                   else concatMap
                          (\ a ->
                            let {
                              ins_committed =
                                map_filter
                                  (\ (p, _) ->
                                    (if not (null (nth (nth inb p) a))
                                      then Just p else Nothing))
                                  pairs;
                              always_committed =
                                less_nat one_nat (size_list ins_committed);
                            } in concatMap
                                   (\ p ->
                                     let {
                                       outs = nth (nth outa p) a;
                                     } in (if null outs then []
    else (if not always_committed &&
               (ins_committed == [p] || null ins_committed) &&
                 not (any (\ (q, _) -> equal_nat q p) pairs)
           then []
           else let {
                  combs = make_combs broadcast bounds automata p a inb;
                  outsa = map (\ aa -> (p, aa)) outs;
                  combsa =
                    (if null combs then map (\ x -> [x]) outsa
                      else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                  init = ([], (Broad a, ([], (l, s))));
                } in compute_upds_impl bounds init combsa)))
                                   (upt zero_nat n_ps))
                          (upt zero_nat num_actions)));
        bin_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
              out = all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let {
                          in2 = all_actions_from_vec num_actions trans_in_map
                                  pairs;
                          out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        } in concatMap
                               (\ a ->
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                               (bin_actions broadcast num_actions) ++
                               concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                                 (bin_actions broadcast num_actions)));
        int_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
            } in (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s));
        trans_impl =
          (\ st ->
            int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
        e_op_impl =
          (\ ai bic bib bia bi ->
            do { 
              x <- up_canonical_upd_impl_int m bi m;
              xa <- imp_nfoldli (inv_fun ai) (\ _ -> return True)
                      (\ aia bid ->
                        do { 
                          xa <- abstra_upd_impl_int m aia bid;
                          repair_pair_impl_int m xa zero_nat
                            (constraint_clk aia)
                         })
                      x;
              xaa <- check_diag_impl_int m xa;
              x_a <-
                (if xaa
                  then mtx_set (suc m) xa (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bib (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            })
                         xa);
              x_b <- check_diag_impl_int m x_a;
              (if x_b
                then mtx_set (suc m) x_a (zero_nat, zero_nat) (Lt zero_int)
                else imp_nfoldli bic (\ _ -> return True)
                       (\ xc sigma ->
                         reset_canonical_upd_impl_int m sigma m xc zero_int)
                       x_a >>=
                       imp_nfoldli (inv_fun bia) (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            }))
             });
      } in (\ ai bi ->
             (if null bi then return []
               else imp_nfoldli (trans_impl ai) (\ _ -> return True)
                      (\ xc sigma ->
                        (case xc of {
                          (a1, (_, (a1b, a2b))) ->
                            do { 
                              x <- heap_map amtx_copy bi;
                              x_d <-
                                imp_nfoldli x (\ _ -> return True)
                                  (\ xb sigmaa ->
                                    do { 
                                      x_c <-
pR_CONST e_op_impl ai a1b a1 a2b xb;
                                      x_e <- check_diag_impl_int m x_c;
                                      return
(if x_e then sigmaa else op_list_prepend x_c sigmaa)
                                     })
                                  [];
                              return (op_list_prepend (a2b, x_d) sigma)
                             };
                        }))
                      []));
    _ = start_timer ();
  } in do { 
         m_table <-
           ht_new >>=
             imp_nfoldli m_list (\ _ -> return True)
               (\ xc sigma ->
                 do { 
                   x_e <-
                     imp_nfoldli (snd xc) (\ _ -> return True)
                       (\ xg sigmaa -> do { 
 x_g <- Heap.newListArray xg;
 return (x_g : sigmaa)
                                        })
                       [];
                   ht_update (fst xc) x_e sigma
                  });
         let { _ = save_time "Time for loading certificate" };
         certify_unreachable_impl_inner fi pi copyi lei succsi l_0i s_0i
           (split_ka num_split) l_list m_table >>=
           return
        };

certificate_checker ::
  Nat ->
    Bool ->
      [(([Nat], [Int]), [[DBMEntry Int]])] ->
        [Nat] ->
          [(Nat, (Int, Int))] ->
            [([Nat],
               ([Nat],
                 ([(Nat, (Bexp Nat Int,
                           ([Acconstraint Nat Int],
                             (Act Nat,
                               ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                   [(Nat, [Acconstraint Nat Int])])))] ->
              Nat ->
                (Nat -> Nat) ->
                  Nat ->
                    [[[Nat]]] ->
                      [Nat] ->
                        [(Nat, Int)] ->
                          Formula Nat Nat Nat Int ->
                            Heap.ST Heap.RealWorld (Maybe Bool);
certificate_checker num_split dc m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let {
    l_list = map fst m_list;
  } in (case certificate_checker_pre l_list m_list broadcast bounds automata m
               num_states num_actions k l_0 s_0 formula
         of {
         True ->
           do { 
             r <- (if dc
                    then no_deadlock_certifier broadcast bounds automata m
                           num_states num_actions l_0 s_0 l_list m_list
                           num_split
                    else unreachability_checker broadcast bounds automata m
                           num_states num_actions l_0 s_0 formula l_list m_list
                           num_split);
             return (Just r)
            };
         False -> return Nothing;
       });

rename_check ::
  Nat ->
    Bool ->
      [String] ->
        [(String, (Int, Int))] ->
          [([Nat],
             ([Nat],
               ([(Nat, (Bexp String Int,
                         ([Acconstraint String Int],
                           (Act String,
                             ([(String, Exp String Int)], ([String], Nat))))))],
                 [(Nat, [Acconstraint String Int])])))] ->
            [[[Nat]]] ->
              [Nat] ->
                [(String, Int)] ->
                  Formula Nat Nat String Int ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          (String -> Nat) ->
                            (String -> Nat) ->
                              (String -> Nat) ->
                                (Nat -> Nat -> Nat) ->
                                  [(([Nat], [Int]), [[DBMEntry Int]])] ->
                                    Heap.ST Heap.RealWorld Resulta;
rename_check num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case (do_rename_mc ::
          ((Nat -> [Char]) ->
            (([Nat], [Int]) -> [Char]) ->
              [Nat] ->
                [(Nat, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp Nat Int,
                                 ([Acconstraint Nat Int],
                                   (Act Nat,
                                     ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                         [(Nat, [Acconstraint Nat Int])])))] ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          [[[Nat]]] ->
                            [Nat] ->
                              [(Nat, Int)] ->
                                Formula Nat Nat Nat Int ->
                                  Heap.ST Heap.RealWorld (Maybe Bool)) ->
            Bool ->
              [String] ->
                [(String, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp String Int,
                                 ([Acconstraint String Int],
                                   (Act String,
                                     ([(String, Exp String Int)],
                                       ([String], Nat))))))],
                         [(Nat, [Acconstraint String Int])])))] ->
                    [[[Nat]]] ->
                      String ->
                        [Nat] ->
                          [(String, Int)] ->
                            Formula Nat Nat String Int ->
                              Nat ->
                                (Nat -> Nat) ->
                                  Nat ->
                                    (String -> Nat) ->
                                      (String -> Nat) ->
(String -> Nat) ->
  (Nat -> Nat -> Nat) ->
    (Nat -> Nat -> [Char]) ->
      (Nat -> [Char]) ->
        (Nat -> [Char]) -> Maybe (Heap.ST Heap.RealWorld (Maybe Bool)))
          (\ _ _ -> certificate_checker num_split dc state_space) dc broadcast
          bounds automata k "_urge" l_0 s_0 formula m num_states num_actions
          renum_acts renum_vars renum_clocks renum_states
          (\ _ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
    of {
    Nothing -> return Renaming_Failed;
    Just r -> do { 
                a <- r;
                (case a of {
                  Nothing -> return Preconds_Unsat;
                  Just True -> return Sat;
                  Just False -> return Unsat;
                })
               };
  });

show_state_space ::
  Nat ->
    (Nat -> Nat -> Nat) ->
      (Nat -> String) -> (Nat -> String) -> State_space Nat -> [[()]];
show_state_space num_clocks inv_renum_states inv_renum_vars inv_renum_clocks
  (Reachable_Set xs) =
  map (\ (l, a) ->
        map (\ x ->
              println
                (implode
                  ([Char False False False True False True False False] ++
                    show_st inv_renum_states inv_renum_vars l ++
                      [Char False False True True False True False False,
                        Char False False False False False True False False,
                        Char False False True True True True False False] ++
                        show_dbm num_clocks inv_renum_clocks x ++
                          [Char False True True True True True False False,
                            Char True False False True False True False
                              False])))
          a)
    xs;
show_state_space num_clocks inv_renum_states inv_renum_vars inv_renum_clocks
  (Buechi_Set xs) =
  map (\ (l, a) ->
        map (\ (x, i) ->
              println
                (implode
                  (shows_prec_nat zero_nat i [] ++
                    [Char False True False True True True False False,
                      Char False False False False False True False False,
                      Char False False False True False True False False] ++
                      show_st inv_renum_states inv_renum_vars l ++
                        [Char False False True True False True False False,
                          Char False False False False False True False False,
                          Char False False True True True True False False] ++
                          show_dbm num_clocks inv_renum_clocks x ++
                            [Char False True True True True True False False,
                              Char True False False True False True False
                                False])))
          a)
    xs;

unreachability_checker2 ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  Formula Nat Nat Nat Int ->
                    [([Nat], [Int])] ->
                      [(([Nat], [Int]), [[DBMEntry Int]])] -> Nat -> Bool;
unreachability_checker2 broadcast bounds automata m num_states num_actions l_0
  s_0 formula l_list m_list num_split =
  let {
    states_ia = map (states_i automata) (upt zero_nat (size_list automata));
    check_states =
      (\ (l, s) ->
        (equal_nat (size_list l) (size_list automata) &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            (size_list automata)) &&
          equal_nat (size_list s) (n_vs bounds) && check_boundedi bounds s);
    fi = (\ xi -> return (case xi of {
                           ((a, b), _) -> hd_of_formulai formula a b;
                         }));
    pi = (\ (a1, a2) ->
           do { 
             x <- imp_for_int zero_nat (plus_nat m one_nat) return
                    (\ xc _ ->
                      imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xf _ ->
                          imp_for_int zero_nat (plus_nat m one_nat) return
                            (\ xj _ ->
                              do { 
                                x_i <- mtx_get (suc m) a2 (xc, xj);
                                x <- mtx_get (suc m) a2 (xc, xf);
                                xa <- mtx_get (suc m) a2 (xf, xj);
                                return (dbm_le_int x_i (dbm_add_int x xa))
                               })
                            True)
                        True)
                    True;
             xa <- check_diag_impl_int m a2;
             xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_d <- mtx_get (suc m) a2 (xc, xc);
                                  return (dbm_le_int x_d (Le zero_int))
                                 })
                     True;
             xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                  return (dbm_le_int x_e (Le zero_int))
                                 })
                     True;
             return (check_states a1 && (x || xa) && xb && xc)
            });
    copyi = amtx_copy;
    lei = dbm_subset_impl_int m;
    l_0i = return (l_0, map (the . map_of s_0) (upt zero_nat (n_vs bounds)));
    s_0i = amtx_dflt (suc m) (suc m) (Le zero_int);
    succsi =
      let {
        n_ps = size_list automata;
        invs =
          IArray.of_list
            (map (\ i ->
                   let {
                     ma = default_map_of [] (snd (snd (snd (nth automata i))));
                     mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
                   } in mb)
              (upt zero_nat n_ps));
        inv_fun =
          (\ (l, _) ->
            concatMap (\ i -> sub (sub invs i) (nth l i)) (upt zero_nat n_ps));
        trans_mapa = trans_map automata;
        trans_i_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                }))
              (trans_mapa i j));
        int_trans_from_loc_impl =
          (\ p l la s ->
            let {
              a = trans_i_map p l;
            } in map_filter
                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                     let {
                       sa = mk_updsi s f;
                     } in (if bvali s b && check_boundedi bounds sa
                            then Just (g,
(Internal aa, (r, (list_update la p lb, sa))))
                            else Nothing))
                   a);
        int_trans_from_vec_impl =
          (\ pairs l s ->
            concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
        int_trans_from_all_impl =
          (\ l s ->
            concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nat n_ps));
        trans_out_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_in_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_out_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        trans_in_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        broad_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              out = map (\ p -> trans_out_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
              outa = map (map (filter (\ (b, _) -> bvali s b))) out;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            concatMap
                              (\ p ->
                                let {
                                  outs = nth (nth outa p) a;
                                } in (if null outs then []
                                       else let {
      combs = make_combs broadcast bounds automata p a inb;
      outsa = map (\ aa -> (p, aa)) outs;
      combsa =
        (if null combs then map (\ x -> [x]) outsa
          else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
      init = ([], (Broad a, ([], (l, s))));
    } in compute_upds_impl bounds init combsa))
                              (upt zero_nat n_ps))
                          (upt zero_nat num_actions)
                   else concatMap
                          (\ a ->
                            let {
                              ins_committed =
                                map_filter
                                  (\ (p, _) ->
                                    (if not (null (nth (nth inb p) a))
                                      then Just p else Nothing))
                                  pairs;
                              always_committed =
                                less_nat one_nat (size_list ins_committed);
                            } in concatMap
                                   (\ p ->
                                     let {
                                       outs = nth (nth outa p) a;
                                     } in (if null outs then []
    else (if not always_committed &&
               (ins_committed == [p] || null ins_committed) &&
                 not (any (\ (q, _) -> equal_nat q p) pairs)
           then []
           else let {
                  combs = make_combs broadcast bounds automata p a inb;
                  outsa = map (\ aa -> (p, aa)) outs;
                  combsa =
                    (if null combs then map (\ x -> [x]) outsa
                      else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                  init = ([], (Broad a, ([], (l, s))));
                } in compute_upds_impl bounds init combsa)))
                                   (upt zero_nat n_ps))
                          (upt zero_nat num_actions)));
        bin_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
              out = all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let {
                          in2 = all_actions_from_vec num_actions trans_in_map
                                  pairs;
                          out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        } in concatMap
                               (\ a ->
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                               (bin_actions broadcast num_actions) ++
                               concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                                 (bin_actions broadcast num_actions)));
        int_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
            } in (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s));
        trans_impl =
          (\ st ->
            int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
        e_op_impl =
          (\ ai bic bib bia bi ->
            do { 
              x <- up_canonical_upd_impl_int m bi m;
              xa <- imp_nfoldli (inv_fun ai) (\ _ -> return True)
                      (\ aia bid ->
                        do { 
                          xa <- abstra_upd_impl_int m aia bid;
                          repair_pair_impl_int m xa zero_nat
                            (constraint_clk aia)
                         })
                      x;
              xaa <- check_diag_impl_int m xa;
              x_a <-
                (if xaa
                  then mtx_set (suc m) xa (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bib (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            })
                         xa);
              x_b <- check_diag_impl_int m x_a;
              (if x_b
                then mtx_set (suc m) x_a (zero_nat, zero_nat) (Lt zero_int)
                else imp_nfoldli bic (\ _ -> return True)
                       (\ xc sigma ->
                         reset_canonical_upd_impl_int m sigma m xc zero_int)
                       x_a >>=
                       imp_nfoldli (inv_fun bia) (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            }))
             });
      } in (\ ai bi ->
             (if null bi then return []
               else imp_nfoldli (trans_impl ai) (\ _ -> return True)
                      (\ xc sigma ->
                        (case xc of {
                          (a1, (_, (a1b, a2b))) ->
                            do { 
                              x <- heap_map amtx_copy bi;
                              x_d <-
                                imp_nfoldli x (\ _ -> return True)
                                  (\ xb sigmaa ->
                                    do { 
                                      x_c <-
pR_CONST e_op_impl ai a1b a1 a2b xb;
                                      x_e <- check_diag_impl_int m x_c;
                                      return
(if x_e then sigmaa else op_list_prepend x_c sigmaa)
                                     })
                                  [];
                              return (op_list_prepend (a2b, x_d) sigma)
                             };
                        }))
                      []));
    a = ht_new >>=
          imp_nfoldli m_list (\ _ -> return True)
            (\ xc sigma ->
              do { 
                x_e <-
                  imp_nfoldli (snd xc) (\ _ -> return True)
                    (\ xg sigmaa -> do { 
                                      x_g <- Heap.newListArray xg;
                                      return (x_g : sigmaa)
                                     })
                    [];
                ht_update (fst xc) x_e sigma
               });
  } in certify_unreachable_impl2 fi pi copyi lei succsi l_0i s_0i
         (split_ka num_split) l_list a;

no_deadlock_certifier2 ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  [([Nat], [Int])] ->
                    [(([Nat], [Int]), [[DBMEntry Int]])] -> Nat -> Bool;
no_deadlock_certifier2 broadcast bounds automata m num_states num_actions l_0
  s_0 l_list m_list num_split =
  let {
    states_ia = map (states_i automata) (upt zero_nat (size_list automata));
    check_states =
      (\ (l, s) ->
        (equal_nat (size_list l) (size_list automata) &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            (size_list automata)) &&
          equal_nat (size_list s) (n_vs bounds) && check_boundedi bounds s);
    fi = (\ (l, ma) ->
           do { 
             r <- let {
                    n_ps = size_list automata;
                    invs =
                      IArray.of_list
                        (map (\ i ->
                               let {
                                 mb = default_map_of []
(snd (snd (snd (nth automata i))));
                                 mc = IArray.of_list
(map mb (upt zero_nat (num_states i)));
                               } in mc)
                          (upt zero_nat n_ps));
                    inv_fun =
                      (\ (la, _) ->
                        concatMap (\ i -> sub (sub invs i) (nth la i))
                          (upt zero_nat n_ps));
                    trans_impl =
                      let {
                        trans_mapa = trans_map automata;
                        trans_i_map =
                          (\ i j ->
                            map_filter
                              (\ a ->
                                (case a of {
                                  (_, (_, (In _, (_, _)))) -> Nothing;
                                  (_, (_, (Out _, (_, _)))) -> Nothing;
                                  (b, (g, (Sil aa, (mb, la)))) ->
                                    Just (b, (g, (aa, (mb, la))));
                                }))
                              (trans_mapa i j));
                        int_trans_from_loc_impl =
                          (\ p la laa s ->
                            let {
                              a = trans_i_map p la;
                            } in map_filter
                                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                                     let {
                                       sa = mk_updsi s f;
                                     } in (if bvali s b &&
        check_boundedi bounds sa
    then Just (g, (Internal aa, (r, (list_update laa p lb, sa)))) else Nothing))
                                   a);
                        int_trans_from_vec_impl =
                          (\ pairs la s ->
                            concatMap
                              (\ (p, laa) -> int_trans_from_loc_impl p laa la s)
                              pairs);
                        int_trans_from_all_impl =
                          (\ la s ->
                            concatMap
                              (\ p -> int_trans_from_loc_impl p (nth la p) la s)
                              (upt zero_nat n_ps));
                        trans_out_map =
                          (\ i j ->
                            map_filter
                              (\ a ->
                                (case a of {
                                  (_, (_, (In _, (_, _)))) -> Nothing;
                                  (b, (g, (Out aa, (mb, la)))) ->
                                    Just (b, (g, (aa, (mb, la))));
                                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                                }))
                              (trans_mapa i j));
                        trans_in_map =
                          (\ i j ->
                            map_filter
                              (\ a ->
                                (case a of {
                                  (b, (g, (In aa, (mb, la)))) ->
                                    Just (b, (g, (aa, (mb, la))));
                                  (_, (_, (Out _, (_, _)))) -> Nothing;
                                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                                }))
                              (trans_mapa i j));
                        trans_out_broad_grouped =
                          (\ i j ->
                            actions_by_statea num_actions
                              (map_filter
                                (\ a ->
                                  (case a of {
                                    (_, (_, (In _, (_, _)))) -> Nothing;
                                    (b, (g, (Out aa, (mb, la)))) ->
                                      (if membera broadcast aa
then Just (b, (g, (aa, (mb, la)))) else Nothing);
                                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                                  }))
                                (trans_mapa i j)));
                        trans_in_broad_grouped =
                          (\ i j ->
                            actions_by_statea num_actions
                              (map_filter
                                (\ a ->
                                  (case a of {
                                    (b, (g, (In aa, (mb, la)))) ->
                                      (if membera broadcast aa
then Just (b, (g, (aa, (mb, la)))) else Nothing);
                                    (_, (_, (Out _, (_, _)))) -> Nothing;
                                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                                  }))
                                (trans_mapa i j)));
                        broad_trans_impl =
                          (\ (la, s) ->
                            let {
                              pairs =
                                get_committed broadcast bounds automata la;
                              ina = map (\ p ->
  trans_in_broad_grouped p (nth la p))
                                      (upt zero_nat n_ps);
                              out = map (\ p ->
  trans_out_broad_grouped p (nth la p))
                                      (upt zero_nat n_ps);
                              inb = map (map (filter (\ (b, _) -> bvali s b)))
                                      ina;
                              outa =
                                map (map (filter (\ (b, _) -> bvali s b))) out;
                            } in (if null pairs
                                   then concatMap
  (\ a ->
    concatMap
      (\ p ->
        let {
          outs = nth (nth outa p) a;
        } in (if null outs then []
               else let {
                      combs = make_combs broadcast bounds automata p a inb;
                      outsa = map (\ aa -> (p, aa)) outs;
                      combsa =
                        (if null combs then map (\ x -> [x]) outsa
                          else concatMap (\ x -> map (\ aa -> x : aa) combs)
                                 outsa);
                      init = ([], (Broad a, ([], (la, s))));
                    } in compute_upds_impl bounds init combsa))
      (upt zero_nat n_ps))
  (upt zero_nat num_actions)
                                   else concatMap
  (\ a ->
    let {
      ins_committed =
        map_filter
          (\ (p, _) ->
            (if not (null (nth (nth inb p) a)) then Just p else Nothing))
          pairs;
      always_committed = less_nat one_nat (size_list ins_committed);
    } in concatMap
           (\ p ->
             let {
               outs = nth (nth outa p) a;
             } in (if null outs then []
                    else (if not always_committed &&
                               (ins_committed == [p] || null ins_committed) &&
                                 not (any (\ (q, _) -> equal_nat q p) pairs)
                           then []
                           else let {
                                  combs =
                                    make_combs broadcast bounds automata p a
                                      inb;
                                  outsa = map (\ aa -> (p, aa)) outs;
                                  combsa =
                                    (if null combs then map (\ x -> [x]) outsa
                                      else concatMap
     (\ x -> map (\ aa -> x : aa) combs) outsa);
                                  init = ([], (Broad a, ([], (la, s))));
                                } in compute_upds_impl bounds init combsa)))
           (upt zero_nat n_ps))
  (upt zero_nat num_actions)));
                        bin_trans_impl =
                          (\ (la, s) ->
                            let {
                              pairs =
                                get_committed broadcast bounds automata la;
                              ina = all_actions_by_state broadcast bounds
                                      automata num_actions trans_in_map la;
                              out = all_actions_by_state broadcast bounds
                                      automata num_actions trans_out_map la;
                            } in (if null pairs
                                   then concatMap
  (\ a -> pairs_by_action_impl bounds la s (nth out a) (nth ina a))
  (bin_actions broadcast num_actions)
                                   else let {
  in2 = all_actions_from_vec num_actions trans_in_map pairs;
  out2 = all_actions_from_vec num_actions trans_out_map pairs;
} in concatMap (\ a -> pairs_by_action_impl bounds la s (nth out a) (nth in2 a))
       (bin_actions broadcast num_actions) ++
       concatMap
         (\ a -> pairs_by_action_impl bounds la s (nth out2 a) (nth ina a))
         (bin_actions broadcast num_actions)));
                        int_trans_impl =
                          (\ (la, s) ->
                            let {
                              pairs =
                                get_committed broadcast bounds automata la;
                            } in (if null pairs
                                   then int_trans_from_all_impl la s
                                   else int_trans_from_vec_impl pairs la s));
                      } in (\ st ->
                             int_trans_impl st ++
                               bin_trans_impl st ++ broad_trans_impl st);
                  } in (\ ai bi ->
                         do { 
                           x <- imp_nfoldli (trans_impl ai) (\ _ -> return True)
                                  (\ xb sigma ->
                                    do { 
                                      x <- v_dbm_impl m;
                                      xa <-
abstr_FW_impl_int m (inv_fun (snd (snd (snd xb)))) x;
                                      xc <-
pre_reset_list_impl m xa (fst (snd (snd xb)));
                                      xd <- abstr_FW_impl_int m (fst xb) xc;
                                      xe <- abstr_FW_impl_int m (inv_fun ai) xd;
                                      x_c <- down_impl_int m xe;
                                      return (x_c : sigma)
                                     })
                                  [];
                           dbm_subset_fed_impl m bi (op_list_rev x)
                          })
                    l
                    ma;
             return (not r)
            });
    pi = (\ (a1, a2) ->
           do { 
             x <- imp_for_int zero_nat (plus_nat m one_nat) return
                    (\ xc _ ->
                      imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xf _ ->
                          imp_for_int zero_nat (plus_nat m one_nat) return
                            (\ xj _ ->
                              do { 
                                x_i <- mtx_get (suc m) a2 (xc, xj);
                                x <- mtx_get (suc m) a2 (xc, xf);
                                xa <- mtx_get (suc m) a2 (xf, xj);
                                return (dbm_le_int x_i (dbm_add_int x xa))
                               })
                            True)
                        True)
                    True;
             xa <- check_diag_impl_int m a2;
             xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_d <- mtx_get (suc m) a2 (xc, xc);
                                  return (dbm_le_int x_d (Le zero_int))
                                 })
                     True;
             xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xc _ -> do { 
                                  x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                  return (dbm_le_int x_e (Le zero_int))
                                 })
                     True;
             return (check_states a1 && (x || xa) && xb && xc)
            });
    copyi = amtx_copy;
    lei = dbm_subset_impl_int m;
    l_0i = return (l_0, map (the . map_of s_0) (upt zero_nat (n_vs bounds)));
    s_0i = amtx_dflt (suc m) (suc m) (Le zero_int);
    succsi =
      let {
        n_ps = size_list automata;
        invs =
          IArray.of_list
            (map (\ i ->
                   let {
                     ma = default_map_of [] (snd (snd (snd (nth automata i))));
                     mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
                   } in mb)
              (upt zero_nat n_ps));
        inv_fun =
          (\ (l, _) ->
            concatMap (\ i -> sub (sub invs i) (nth l i)) (upt zero_nat n_ps));
        trans_mapa = trans_map automata;
        trans_i_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                }))
              (trans_mapa i j));
        int_trans_from_loc_impl =
          (\ p l la s ->
            let {
              a = trans_i_map p l;
            } in map_filter
                   (\ (b, (g, (aa, (f, (r, lb))))) ->
                     let {
                       sa = mk_updsi s f;
                     } in (if bvali s b && check_boundedi bounds sa
                            then Just (g,
(Internal aa, (r, (list_update la p lb, sa))))
                            else Nothing))
                   a);
        int_trans_from_vec_impl =
          (\ pairs l s ->
            concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
        int_trans_from_all_impl =
          (\ l s ->
            concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nat n_ps));
        trans_out_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (_, (_, (In _, (_, _)))) -> Nothing;
                  (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_in_map =
          (\ i j ->
            map_filter
              (\ a ->
                (case a of {
                  (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  (_, (_, (Out _, (_, _)))) -> Nothing;
                  (_, (_, (Sil _, (_, _)))) -> Nothing;
                }))
              (trans_mapa i j));
        trans_out_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        trans_in_broad_grouped =
          (\ i j ->
            actions_by_statea num_actions
              (map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) ->
                      (if membera broadcast aa then Just (b, (g, (aa, (ma, l))))
                        else Nothing);
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j)));
        broad_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              out = map (\ p -> trans_out_broad_grouped p (nth l p))
                      (upt zero_nat n_ps);
              inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
              outa = map (map (filter (\ (b, _) -> bvali s b))) out;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            concatMap
                              (\ p ->
                                let {
                                  outs = nth (nth outa p) a;
                                } in (if null outs then []
                                       else let {
      combs = make_combs broadcast bounds automata p a inb;
      outsa = map (\ aa -> (p, aa)) outs;
      combsa =
        (if null combs then map (\ x -> [x]) outsa
          else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
      init = ([], (Broad a, ([], (l, s))));
    } in compute_upds_impl bounds init combsa))
                              (upt zero_nat n_ps))
                          (upt zero_nat num_actions)
                   else concatMap
                          (\ a ->
                            let {
                              ins_committed =
                                map_filter
                                  (\ (p, _) ->
                                    (if not (null (nth (nth inb p) a))
                                      then Just p else Nothing))
                                  pairs;
                              always_committed =
                                less_nat one_nat (size_list ins_committed);
                            } in concatMap
                                   (\ p ->
                                     let {
                                       outs = nth (nth outa p) a;
                                     } in (if null outs then []
    else (if not always_committed &&
               (ins_committed == [p] || null ins_committed) &&
                 not (any (\ (q, _) -> equal_nat q p) pairs)
           then []
           else let {
                  combs = make_combs broadcast bounds automata p a inb;
                  outsa = map (\ aa -> (p, aa)) outs;
                  combsa =
                    (if null combs then map (\ x -> [x]) outsa
                      else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                  init = ([], (Broad a, ([], (l, s))));
                } in compute_upds_impl bounds init combsa)))
                                   (upt zero_nat n_ps))
                          (upt zero_nat num_actions)));
        bin_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
              ina = all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
              out = all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
            } in (if null pairs
                   then concatMap
                          (\ a ->
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let {
                          in2 = all_actions_from_vec num_actions trans_in_map
                                  pairs;
                          out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        } in concatMap
                               (\ a ->
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                               (bin_actions broadcast num_actions) ++
                               concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                                 (bin_actions broadcast num_actions)));
        int_trans_impl =
          (\ (l, s) ->
            let {
              pairs = get_committed broadcast bounds automata l;
            } in (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s));
        trans_impl =
          (\ st ->
            int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
        e_op_impl =
          (\ ai bic bib bia bi ->
            do { 
              x <- up_canonical_upd_impl_int m bi m;
              xa <- imp_nfoldli (inv_fun ai) (\ _ -> return True)
                      (\ aia bid ->
                        do { 
                          xa <- abstra_upd_impl_int m aia bid;
                          repair_pair_impl_int m xa zero_nat
                            (constraint_clk aia)
                         })
                      x;
              xaa <- check_diag_impl_int m xa;
              x_a <-
                (if xaa
                  then mtx_set (suc m) xa (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bib (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            })
                         xa);
              x_b <- check_diag_impl_int m x_a;
              (if x_b
                then mtx_set (suc m) x_a (zero_nat, zero_nat) (Lt zero_int)
                else imp_nfoldli bic (\ _ -> return True)
                       (\ xc sigma ->
                         reset_canonical_upd_impl_int m sigma m xc zero_int)
                       x_a >>=
                       imp_nfoldli (inv_fun bia) (\ _ -> return True)
                         (\ aia bid ->
                           do { 
                             xb <- abstra_upd_impl_int m aia bid;
                             repair_pair_impl_int m xb zero_nat
                               (constraint_clk aia)
                            }))
             });
      } in (\ ai bi ->
             (if null bi then return []
               else imp_nfoldli (trans_impl ai) (\ _ -> return True)
                      (\ xc sigma ->
                        (case xc of {
                          (a1, (_, (a1b, a2b))) ->
                            do { 
                              x <- heap_map amtx_copy bi;
                              x_d <-
                                imp_nfoldli x (\ _ -> return True)
                                  (\ xb sigmaa ->
                                    do { 
                                      x_c <-
pR_CONST e_op_impl ai a1b a1 a2b xb;
                                      x_e <- check_diag_impl_int m x_c;
                                      return
(if x_e then sigmaa else op_list_prepend x_c sigmaa)
                                     })
                                  [];
                              return (op_list_prepend (a2b, x_d) sigma)
                             };
                        }))
                      []));
    a = ht_new >>=
          imp_nfoldli m_list (\ _ -> return True)
            (\ xc sigma ->
              do { 
                x_e <-
                  imp_nfoldli (snd xc) (\ _ -> return True)
                    (\ xg sigmaa -> do { 
                                      x_g <- Heap.newListArray xg;
                                      return (x_g : sigmaa)
                                     })
                    [];
                ht_update (fst xc) x_e sigma
               });
  } in certify_unreachable_impl2 fi pi copyi lei succsi l_0i s_0i
         (split_ka num_split) l_list a;

certificate_checker2 ::
  Nat ->
    Bool ->
      [(([Nat], [Int]), [[DBMEntry Int]])] ->
        [Nat] ->
          [(Nat, (Int, Int))] ->
            [([Nat],
               ([Nat],
                 ([(Nat, (Bexp Nat Int,
                           ([Acconstraint Nat Int],
                             (Act Nat,
                               ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                   [(Nat, [Acconstraint Nat Int])])))] ->
              Nat ->
                (Nat -> Nat) ->
                  Nat ->
                    [[[Nat]]] ->
                      [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
certificate_checker2 num_split dc m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let {
    l_list = map fst m_list;
  } in (case certificate_checker_pre l_list m_list broadcast bounds automata m
               num_states num_actions k l_0 s_0 formula
         of {
         True ->
           (if dc
             then no_deadlock_certifier2 broadcast bounds automata m num_states
                    num_actions l_0 s_0 l_list m_list num_split
             else unreachability_checker2 broadcast bounds automata m num_states
                    num_actions l_0 s_0 formula l_list m_list num_split);
         False -> False;
       });

rename_check2 ::
  Nat ->
    Bool ->
      [String] ->
        [(String, (Int, Int))] ->
          [([Nat],
             ([Nat],
               ([(Nat, (Bexp String Int,
                         ([Acconstraint String Int],
                           (Act String,
                             ([(String, Exp String Int)], ([String], Nat))))))],
                 [(Nat, [Acconstraint String Int])])))] ->
            [[[Nat]]] ->
              [Nat] ->
                [(String, Int)] ->
                  Formula Nat Nat String Int ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          (String -> Nat) ->
                            (String -> Nat) ->
                              (String -> Nat) ->
                                (Nat -> Nat -> Nat) ->
                                  [(([Nat], [Int]), [[DBMEntry Int]])] ->
                                    Resulta;
rename_check2 num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case (do_rename_mc ::
          ((Nat -> [Char]) ->
            (([Nat], [Int]) -> [Char]) ->
              [Nat] ->
                [(Nat, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp Nat Int,
                                 ([Acconstraint Nat Int],
                                   (Act Nat,
                                     ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                         [(Nat, [Acconstraint Nat Int])])))] ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          [[[Nat]]] ->
                            [Nat] ->
                              [(Nat, Int)] ->
                                Formula Nat Nat Nat Int -> Bool) ->
            Bool ->
              [String] ->
                [(String, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp String Int,
                                 ([Acconstraint String Int],
                                   (Act String,
                                     ([(String, Exp String Int)],
                                       ([String], Nat))))))],
                         [(Nat, [Acconstraint String Int])])))] ->
                    [[[Nat]]] ->
                      String ->
                        [Nat] ->
                          [(String, Int)] ->
                            Formula Nat Nat String Int ->
                              Nat ->
                                (Nat -> Nat) ->
                                  Nat ->
                                    (String -> Nat) ->
                                      (String -> Nat) ->
(String -> Nat) ->
  (Nat -> Nat -> Nat) ->
    (Nat -> Nat -> [Char]) -> (Nat -> [Char]) -> (Nat -> [Char]) -> Maybe Bool)
          (\ _ _ -> certificate_checker2 num_split dc state_space) dc broadcast
          bounds automata k "_urge" l_0 s_0 formula m num_states num_actions
          renum_acts renum_vars renum_clocks renum_states
          (\ _ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
    of {
    Nothing -> Renaming_Failed;
    Just True -> Sat;
    Just False -> Unsat;
  });

hashmap_of_list :: forall a b. (Eq a, Hashable a) => [(a, b)] -> Hashmap a b;
hashmap_of_list m =
  fold (\ (a, b) -> ahm_update (\ aa ba -> aa == ba) bounded_hashcode_nat a b) m
    (ahm_empty ((def_hashmap_size :: Itself a -> Nat) Type));

certify_unreachable_impl_pure ::
  forall a b.
    (a -> [b] -> [(a, [b])]) ->
      [a] ->
        (b -> b -> Bool) ->
          [[a]] ->
            ((a, b) -> Bool) ->
              ((a, b) -> Bool) -> (a -> Maybe [b]) -> a -> b -> Bool;
certify_unreachable_impl_pure get_succs li lei li_split pi fi mi l_0i s_0i =
  let {
    check_all_pre_impl =
      time_it "Time for state set preconditions check"
        (\ _ ->
          (case mi l_0i of {
            Nothing -> False;
            Just xs ->
              not (is_none (mi l_0i)) &&
                pi (l_0i, s_0i) &&
                  any (lei s_0i) xs &&
                    all id
                      (mapa (\ l -> (case op_map_lookup l mi of {
                                      Nothing -> True;
                                      Just a -> all (\ s -> pi (l, s)) a;
                                    }))
                        li);
          }));
    check_final =
      time_it "Time to check final state predicate"
        (\ _ ->
          all id
            (mapa (all (\ l -> (case op_map_lookup l mi of {
                                 Nothing -> True;
                                 Just a -> all (\ s -> not (fi (l, s))) a;
                               })))
              li_split));
    check_invariant =
      time_it "Time for state space invariant check"
        (\ _ ->
          all id
            (mapa (all (\ l ->
                         (case mi l of {
                           Nothing -> True;
                           Just asa ->
                             all (\ (la, xs) ->
                                   (if null xs then True
                                     else (case mi la of {
    Nothing -> False;
    Just ys -> all (\ x -> any (lei x) ys) xs;
  })))
                               (get_succs l asa);
                         })))
              li_split));
  } in (if (if check_all_pre_impl then check_invariant else False)
         then check_final else False);

unreachability_checker3 ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  Formula Nat Nat Nat Int ->
                    [([Nat], [Int])] ->
                      [(([Nat], [Int]), [[DBMEntry Int]])] -> Nat -> Bool;
unreachability_checker3 broadcast bounds automata m num_states num_actions l_0
  s_0 formula l_list m_list num_split =
  let {
    n_vsa = n_vs bounds;
    n_ps = size_list automata;
    invs =
      IArray.of_list
        (map (\ i ->
               let {
                 ma = default_map_of [] (snd (snd (snd (nth automata i))));
                 mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
               } in mb)
          (upt zero_nat n_ps));
    succsi = succs_impl broadcast bounds automata m num_actions n_ps invs;
    states_ia = map (states_i automata) (upt zero_nat n_ps);
    check_state =
      (\ (l, s) ->
        (equal_nat (size_list l) n_ps &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            n_ps) &&
          equal_nat (size_list s) n_vsa && check_boundedi bounds s);
    mi = hashmap_of_list
           (map (\ (k, dbms) -> (k, map IArray.of_list dbms)) m_list);
    init_dbm = amtx_dflt (suc m) (suc m) (Le zero_int);
  } in certify_unreachable_impl_pure
         (\ x ->
           run_heap .
             (\ xs ->
               let {
                 li = id x;
               } in do { 
                      xsi <- fold_map array_unfreezea xs;
                      succsi li xsi >>=
                        fold_map
                          (\ (lia, xsia) ->
                            do { 
                              xsa <- fold_map array_freezea xsia;
                              return (id lia, xsa)
                             })
                     }))
         l_list
         (\ asa bs ->
           not (all_interval_nat
                 (not .
                   (\ i ->
                     dbm_lt_0
                       (sub asa (plus_nat (plus_nat i (times_nat i m)) i))))
                 zero_nat (suc m)) ||
             array_all2 (times_nat (suc m) (suc m)) dbm_le_int asa bs)
         (split_kb num_split m_list)
         (\ a ->
           run_heap
             (do { 
                (a1, a2) <- (case a of {
                              (l, s) -> do { 
  sa <- array_unfreezea s;
  return (id l, sa)
 };
                            });
                x <- imp_for_int zero_nat (plus_nat m one_nat) return
                       (\ xc _ ->
                         imp_for_int zero_nat (plus_nat m one_nat) return
                           (\ xf _ ->
                             imp_for_int zero_nat (plus_nat m one_nat) return
                               (\ xj _ ->
                                 do { 
                                   x_i <- mtx_get (suc m) a2 (xc, xj);
                                   x <- mtx_get (suc m) a2 (xc, xf);
                                   xa <- mtx_get (suc m) a2 (xf, xj);
                                   return (dbm_le_int x_i (dbm_add_int x xa))
                                  })
                               True)
                           True)
                       True;
                xa <- check_diag_impl_int m a2;
                xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xc _ -> do { 
                                     x_d <- mtx_get (suc m) a2 (xc, xc);
                                     return (dbm_le_int x_d (Le zero_int))
                                    })
                        True;
                xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xc _ -> do { 
                                     x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                     return (dbm_le_int x_e (Le zero_int))
                                    })
                        True;
                return (check_state a1 && (x || xa) && xb && xc)
               }))
         (\ a ->
           run_heap (do { 
                       xi <- (case a of {
                               (l, s) -> do { 
   sa <- array_unfreezea s;
   return (id l, sa)
  };
                             });
                       return (case xi of {
                                ((aa, b), _) -> hd_of_formulai formula aa b;
                              })
                      }))
         (\ k -> ahm_lookup (\ a b -> a == b) bounded_hashcode_nat k mi)
         (id (run_heap
               (return (l_0, map (the . map_of s_0) (upt zero_nat n_vsa)))))
         (run_heap (init_dbm >>= array_freezea));

no_deadlock_certifier3 ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  [([Nat], [Int])] ->
                    [(([Nat], [Int]), [[DBMEntry Int]])] -> Nat -> Bool;
no_deadlock_certifier3 broadcast bounds automata m num_states num_actions l_0
  s_0 l_list m_list num_split =
  let {
    n_vsa = n_vs bounds;
    n_ps = size_list automata;
    invs =
      IArray.of_list
        (map (\ i ->
               let {
                 ma = default_map_of [] (snd (snd (snd (nth automata i))));
                 mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
               } in mb)
          (upt zero_nat n_ps));
    succsi = succs_impl broadcast bounds automata m num_actions n_ps invs;
    states_ia = map (states_i automata) (upt zero_nat n_ps);
    check_states =
      (\ (l, s) ->
        (equal_nat (size_list l) n_ps &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            n_ps) &&
          equal_nat (size_list s) n_vsa && check_boundedi bounds s);
    subsumption =
      (\ asa bs ->
        not (all_interval_nat
              (not .
                (\ i ->
                  dbm_lt_0 (sub asa (plus_nat (plus_nat i (times_nat i m)) i))))
              zero_nat (suc m)) ||
          array_all2 (times_nat (suc m) (suc m)) dbm_le_int asa bs);
    p_impl =
      (\ (a1, a2) ->
        do { 
          x <- imp_for_int zero_nat (plus_nat m one_nat) return
                 (\ xc _ ->
                   imp_for_int zero_nat (plus_nat m one_nat) return
                     (\ xf _ ->
                       imp_for_int zero_nat (plus_nat m one_nat) return
                         (\ xj _ ->
                           do { 
                             x_i <- mtx_get (suc m) a2 (xc, xj);
                             x <- mtx_get (suc m) a2 (xc, xf);
                             xa <- mtx_get (suc m) a2 (xf, xj);
                             return (dbm_le_int x_i (dbm_add_int x xa))
                            })
                         True)
                     True)
                 True;
          xa <- check_diag_impl_int m a2;
          xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                  (\ xc _ -> do { 
                               x_d <- mtx_get (suc m) a2 (xc, xc);
                               return (dbm_le_int x_d (Le zero_int))
                              })
                  True;
          xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                  (\ xc _ -> do { 
                               x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                               return (dbm_le_int x_e (Le zero_int))
                              })
                  True;
          return (check_states a1 && (x || xa) && xb && xc)
         });
    p = (\ a -> run_heap ((case a of {
                            (l, s) -> do { 
sa <- array_unfreezea s;
return (id l, sa)
                                       };
                          }) >>=
                           p_impl));
    mi = hashmap_of_list
           (map (\ (k, dbms) -> (k, map IArray.of_list dbms)) m_list);
    init_dbm = amtx_dflt (suc m) (suc m) (Le zero_int);
    check_deadlock =
      let {
        n_psa = n_ps;
        invsa =
          IArray.of_list
            (map (\ i ->
                   let {
                     ma = default_map_of [] (snd (snd (snd (nth automata i))));
                     mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
                   } in mb)
              (upt zero_nat n_psa));
        inv_fun =
          (\ (l, _) ->
            concatMap (\ i -> sub (sub invsa i) (nth l i))
              (upt zero_nat n_psa));
        trans_impl =
          let {
            trans_mapa = trans_map automata;
            trans_i_map =
              (\ i j ->
                map_filter
                  (\ a ->
                    (case a of {
                      (_, (_, (In _, (_, _)))) -> Nothing;
                      (_, (_, (Out _, (_, _)))) -> Nothing;
                      (b, (g, (Sil aa, (ma, l)))) ->
                        Just (b, (g, (aa, (ma, l))));
                    }))
                  (trans_mapa i j));
            int_trans_from_loc_impl =
              (\ pa l la s ->
                let {
                  a = trans_i_map pa l;
                } in map_filter
                       (\ (b, (g, (aa, (f, (r, lb))))) ->
                         let {
                           sa = mk_updsi s f;
                         } in (if bvali s b && check_boundedi bounds sa
                                then Just (g,
    (Internal aa, (r, (list_update la pa lb, sa))))
                                else Nothing))
                       a);
            int_trans_from_vec_impl =
              (\ pairs l s ->
                concatMap (\ (pa, la) -> int_trans_from_loc_impl pa la l s)
                  pairs);
            int_trans_from_all_impl =
              (\ l s ->
                concatMap (\ pa -> int_trans_from_loc_impl pa (nth l pa) l s)
                  (upt zero_nat n_psa));
            trans_out_map =
              (\ i j ->
                map_filter
                  (\ a ->
                    (case a of {
                      (_, (_, (In _, (_, _)))) -> Nothing;
                      (b, (g, (Out aa, (ma, l)))) ->
                        Just (b, (g, (aa, (ma, l))));
                      (_, (_, (Sil _, (_, _)))) -> Nothing;
                    }))
                  (trans_mapa i j));
            trans_in_map =
              (\ i j ->
                map_filter
                  (\ a ->
                    (case a of {
                      (b, (g, (In aa, (ma, l)))) ->
                        Just (b, (g, (aa, (ma, l))));
                      (_, (_, (Out _, (_, _)))) -> Nothing;
                      (_, (_, (Sil _, (_, _)))) -> Nothing;
                    }))
                  (trans_mapa i j));
            trans_out_broad_grouped =
              (\ i j ->
                actions_by_statea num_actions
                  (map_filter
                    (\ a ->
                      (case a of {
                        (_, (_, (In _, (_, _)))) -> Nothing;
                        (b, (g, (Out aa, (ma, l)))) ->
                          (if membera broadcast aa
                            then Just (b, (g, (aa, (ma, l)))) else Nothing);
                        (_, (_, (Sil _, (_, _)))) -> Nothing;
                      }))
                    (trans_mapa i j)));
            trans_in_broad_grouped =
              (\ i j ->
                actions_by_statea num_actions
                  (map_filter
                    (\ a ->
                      (case a of {
                        (b, (g, (In aa, (ma, l)))) ->
                          (if membera broadcast aa
                            then Just (b, (g, (aa, (ma, l)))) else Nothing);
                        (_, (_, (Out _, (_, _)))) -> Nothing;
                        (_, (_, (Sil _, (_, _)))) -> Nothing;
                      }))
                    (trans_mapa i j)));
            broad_trans_impl =
              (\ (l, s) ->
                let {
                  pairs = get_committed broadcast bounds automata l;
                  ina = map (\ pa -> trans_in_broad_grouped pa (nth l pa))
                          (upt zero_nat n_psa);
                  out = map (\ pa -> trans_out_broad_grouped pa (nth l pa))
                          (upt zero_nat n_psa);
                  inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
                  outa = map (map (filter (\ (b, _) -> bvali s b))) out;
                } in (if null pairs
                       then concatMap
                              (\ a ->
                                concatMap
                                  (\ pa ->
                                    let {
                                      outs = nth (nth outa pa) a;
                                    } in (if null outs then []
   else let {
          combs = make_combs broadcast bounds automata pa a inb;
          outsa = map (\ aa -> (pa, aa)) outs;
          combsa =
            (if null combs then map (\ x -> [x]) outsa
              else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
          init = ([], (Broad a, ([], (l, s))));
        } in compute_upds_impl bounds init combsa))
                                  (upt zero_nat n_psa))
                              (upt zero_nat num_actions)
                       else concatMap
                              (\ a ->
                                let {
                                  ins_committed =
                                    map_filter
                                      (\ (pa, _) ->
(if not (null (nth (nth inb pa) a)) then Just pa else Nothing))
                                      pairs;
                                  always_committed =
                                    less_nat one_nat (size_list ins_committed);
                                } in concatMap
                                       (\ pa ->
 let {
   outs = nth (nth outa pa) a;
 } in (if null outs then []
        else (if not always_committed &&
                   (ins_committed == [pa] || null ins_committed) &&
                     not (any (\ (q, _) -> equal_nat q pa) pairs)
               then []
               else let {
                      combs = make_combs broadcast bounds automata pa a inb;
                      outsa = map (\ aa -> (pa, aa)) outs;
                      combsa =
                        (if null combs then map (\ x -> [x]) outsa
                          else concatMap (\ x -> map (\ aa -> x : aa) combs)
                                 outsa);
                      init = ([], (Broad a, ([], (l, s))));
                    } in compute_upds_impl bounds init combsa)))
                                       (upt zero_nat n_psa))
                              (upt zero_nat num_actions)));
            bin_trans_impl =
              (\ (l, s) ->
                let {
                  pairs = get_committed broadcast bounds automata l;
                  ina = all_actions_by_state broadcast bounds automata
                          num_actions trans_in_map l;
                  out = all_actions_by_state broadcast bounds automata
                          num_actions trans_out_map l;
                } in (if null pairs
                       then concatMap
                              (\ a ->
                                pairs_by_action_impl bounds l s (nth out a)
                                  (nth ina a))
                              (bin_actions broadcast num_actions)
                       else let {
                              in2 = all_actions_from_vec num_actions
                                      trans_in_map pairs;
                              out2 =
                                all_actions_from_vec num_actions trans_out_map
                                  pairs;
                            } in concatMap
                                   (\ a ->
                                     pairs_by_action_impl bounds l s (nth out a)
                                       (nth in2 a))
                                   (bin_actions broadcast num_actions) ++
                                   concatMap
                                     (\ a ->
                                       pairs_by_action_impl bounds l s
 (nth out2 a) (nth ina a))
                                     (bin_actions broadcast num_actions)));
            int_trans_impl =
              (\ (l, s) ->
                let {
                  pairs = get_committed broadcast bounds automata l;
                } in (if null pairs then int_trans_from_all_impl l s
                       else int_trans_from_vec_impl pairs l s));
          } in (\ st ->
                 int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
      } in (\ ai bi ->
             do { 
               x <- imp_nfoldli (trans_impl ai) (\ _ -> return True)
                      (\ xb sigma ->
                        do { 
                          x <- v_dbm_impl m;
                          xa <- abstr_FW_impl_int m
                                  (inv_fun (snd (snd (snd xb)))) x;
                          xc <- pre_reset_list_impl m xa (fst (snd (snd xb)));
                          xd <- abstr_FW_impl_int m (fst xb) xc;
                          xe <- abstr_FW_impl_int m (inv_fun ai) xd;
                          x_c <- down_impl_int m xe;
                          return (x_c : sigma)
                         })
                      [];
               dbm_subset_fed_impl m bi (op_list_rev x)
              });
    check_deadlock1 =
      (\ a -> run_heap (do { 
                          (l, ma) <- (case a of {
                                       (l, s) -> do { 
           sa <- array_unfreezea s;
           return (id l, sa)
          };
                                     });
                          r <- check_deadlock l ma;
                          return (not r)
                         }));
  } in certify_unreachable_impl_pure
         (\ x ->
           run_heap .
             (\ xs ->
               let {
                 li = id x;
               } in do { 
                      xsi <- fold_map array_unfreezea xs;
                      succsi li xsi >>=
                        fold_map
                          (\ (lia, xsia) ->
                            do { 
                              xsa <- fold_map array_freezea xsia;
                              return (id lia, xsa)
                             })
                     }))
         l_list subsumption (split_kb num_split m_list) p check_deadlock1
         (\ k -> ahm_lookup (\ a b -> a == b) bounded_hashcode_nat k mi)
         (id (run_heap
               (return (l_0, map (the . map_of s_0) (upt zero_nat n_vsa)))))
         (run_heap (init_dbm >>= array_freezea));

certificate_checker3 ::
  Nat ->
    Bool ->
      [(([Nat], [Int]), [[DBMEntry Int]])] ->
        [Nat] ->
          [(Nat, (Int, Int))] ->
            [([Nat],
               ([Nat],
                 ([(Nat, (Bexp Nat Int,
                           ([Acconstraint Nat Int],
                             (Act Nat,
                               ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                   [(Nat, [Acconstraint Nat Int])])))] ->
              Nat ->
                (Nat -> Nat) ->
                  Nat ->
                    [[[Nat]]] ->
                      [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
certificate_checker3 num_split dc m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let {
    l_list = map fst m_list;
  } in (case certificate_checker_pre l_list m_list broadcast bounds automata m
               num_states num_actions k l_0 s_0 formula
         of {
         True ->
           (if dc
             then no_deadlock_certifier3 broadcast bounds automata m num_states
                    num_actions l_0 s_0 l_list m_list num_split
             else unreachability_checker3 broadcast bounds automata m num_states
                    num_actions l_0 s_0 formula l_list m_list num_split);
         False -> False;
       });

rename_check3 ::
  Nat ->
    Bool ->
      [String] ->
        [(String, (Int, Int))] ->
          [([Nat],
             ([Nat],
               ([(Nat, (Bexp String Int,
                         ([Acconstraint String Int],
                           (Act String,
                             ([(String, Exp String Int)], ([String], Nat))))))],
                 [(Nat, [Acconstraint String Int])])))] ->
            [[[Nat]]] ->
              [Nat] ->
                [(String, Int)] ->
                  Formula Nat Nat String Int ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          (String -> Nat) ->
                            (String -> Nat) ->
                              (String -> Nat) ->
                                (Nat -> Nat -> Nat) ->
                                  [(([Nat], [Int]), [[DBMEntry Int]])] ->
                                    Resulta;
rename_check3 num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case (do_rename_mc ::
          ((Nat -> [Char]) ->
            (([Nat], [Int]) -> [Char]) ->
              [Nat] ->
                [(Nat, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp Nat Int,
                                 ([Acconstraint Nat Int],
                                   (Act Nat,
                                     ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                         [(Nat, [Acconstraint Nat Int])])))] ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          [[[Nat]]] ->
                            [Nat] ->
                              [(Nat, Int)] ->
                                Formula Nat Nat Nat Int -> Bool) ->
            Bool ->
              [String] ->
                [(String, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp String Int,
                                 ([Acconstraint String Int],
                                   (Act String,
                                     ([(String, Exp String Int)],
                                       ([String], Nat))))))],
                         [(Nat, [Acconstraint String Int])])))] ->
                    [[[Nat]]] ->
                      String ->
                        [Nat] ->
                          [(String, Int)] ->
                            Formula Nat Nat String Int ->
                              Nat ->
                                (Nat -> Nat) ->
                                  Nat ->
                                    (String -> Nat) ->
                                      (String -> Nat) ->
(String -> Nat) ->
  (Nat -> Nat -> Nat) ->
    (Nat -> Nat -> [Char]) -> (Nat -> [Char]) -> (Nat -> [Char]) -> Maybe Bool)
          (\ _ _ -> certificate_checker3 num_split dc state_space) dc broadcast
          bounds automata k "_urge" l_0 s_0 formula m num_states num_actions
          renum_acts renum_vars renum_clocks renum_states
          (\ _ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
    of {
    Nothing -> Renaming_Failed;
    Just True -> Sat;
    Just False -> Unsat;
  });

len_of_state_space :: forall a. State_space a -> Nat;
len_of_state_space (Reachable_Set xs) = size_list xs;
len_of_state_space (Buechi_Set xs) = size_list xs;

rename_state_space ::
  forall a.
    (Showa a) => Bool ->
                   (Nat -> Nat -> a) ->
                     ([String],
                       ([([Nat],
                           ([Nat],
                             ([(Nat, (Bexp String Int,
                                       ([Acconstraint String Int],
 (Act String, ([(String, Exp String Int)], ([String], Nat))))))],
                               [(Nat, [Acconstraint String Int])])))],
                         [(String, (Int, Int))])) ->
                       [Nat] ->
                         [(String, Int)] ->
                           Formula Nat Nat String Int ->
                             Result
                               (Maybe (Heap.ST Heap.RealWorld
[(([Nat], [Int]),
   [(([Nat], [Int]), Heap.STArray Heap.RealWorld (DBMEntry Int))])]),
                                 (Nat -> [Char],
                                   (([Nat], [Int]) -> [Char],
                                     ((Nat,
(Nat -> Nat,
  (Nat, (String -> Nat,
          (String -> Nat,
            (String -> Nat,
              (Nat -> Nat -> Nat,
                (Nat -> Nat -> Nat, (Nat -> String, Nat -> String))))))))),
                                       [[[Nat]]]))));
rename_state_space =
  (\ dc ids_to_names (broadcast, (automata, bounds)) l_0 s_0 formula ->
    let {
      _ = println "Make renaming";
    } in binda (make_renaming broadcast automata bounds)
           (\ (m, (num_states,
                    (num_actions,
                      (renum_acts,
                        (renum_vars,
                          (renum_clocks,
                            (renum_states,
                              (inv_renum_states,
                                (inv_renum_vars, inv_renum_clocks)))))))))
             -> let {
                  _ = println "Renaming";
                } in (case rename_network broadcast bounds automata renum_acts
                             renum_vars renum_clocks renum_states
                       of {
                       (broadcasta, (automataa, boundsa)) ->
                         let {
                           _ = println "Calculating ceiling";
                           k = local_ceiling broadcasta boundsa automataa m
                                 num_states;
                           _ = println "Running model checker";
                           inv_renum_statesa =
                             (\ i -> ids_to_names i . inv_renum_states i);
                           f = (\ show_clock show_statea broadcastb boundsb
                                 automatab ma num_statesa num_actionsa ka l_0a
                                 s_0a formulaa ->
                                 state_space broadcastb boundsb automatab ma
                                   num_statesa num_actionsa ka l_0a s_0a
                                   formulaa show_clock show_statea ());
                           r = do_rename_mc f dc broadcast bounds automata k
                                 "_urge" l_0 s_0 formula m num_states
                                 num_actions renum_acts renum_vars renum_clocks
                                 renum_states inv_renum_statesa inv_renum_vars
                                 inv_renum_clocks;
                           show_clock =
                             (\ x -> shows_prec_literal zero_nat x []) .
                               inv_renum_clocks;
                           show_statea =
                             show_state inv_renum_states inv_renum_vars;
                           renamings =
                             (m, (num_states,
                                   (num_actions,
                                     (renum_acts,
                                       (renum_vars,
 (renum_clocks,
   (renum_states, (inv_renum_states, (inv_renum_vars, inv_renum_clocks)))))))));
                         } in Result
                                (r, (show_clock,
                                      (show_statea, (renamings, k))));
                     })));

dbm_list_to_stringa ::
  forall a.
    (Linordered_ab_group_add a,
      Heapa a) => Nat ->
                    (Nat -> [Char]) -> (a -> [Char]) -> [DBMEntry a] -> [Char];
dbm_list_to_stringa n show_clock show_num xs =
  app ((((concat .
           intersperse
             [Char False False True True False True False False,
               Char False False False False False True False False]) .
          reverse) .
         snd) .
        snd)
    (fold (\ e (i, (j, acc)) ->
            let {
              s = make_stringa show_clock show_num e i j;
              ja = modulo_nat (plus_nat j one_nat) (plus_nat n one_nat);
              ia = (if equal_nat ja zero_nat then plus_nat i one_nat else i);
            } in (ia, (ja, s : acc)))
      xs (zero_nat, (zero_nat, [])));

show_dbm_impl_all ::
  forall a.
    (Linordered_ab_group_add a, Eq a,
      Heapa a) => Nat ->
                    (Nat -> [Char]) ->
                      (a -> [Char]) ->
                        Heap.STArray Heap.RealWorld (DBMEntry a) ->
                          Heap.ST Heap.RealWorld [Char];
show_dbm_impl_all n show_clock show_num =
  (\ xi -> do { 
             x <- dbm_to_list_impl n xi;
             return (dbm_list_to_stringa n show_clock show_num x)
            });

check_diag_nonpos ::
  forall a.
    (Zero a, Eq a, Heapa a,
      Linorder a) => Nat ->
                       Heap.STArray Heap.RealWorld (DBMEntry a) ->
                         Heap.ST Heap.RealWorld Bool;
check_diag_nonpos n m =
  imp_for_int zero_nat (plus_nat n one_nat) return
    (\ xc _ -> do { 
                 x_d <- mtx_get (suc n) m (xc, xc);
                 return (less_eq_DBMEntry x_d (Le zero))
                })
    True;

check_prop_fail ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> [Char]) ->
            (([Nat], [Int]) -> [Char]) ->
              [([Nat], [Int])] ->
                [(([Nat], [Int]), [[DBMEntry Int]])] ->
                  Heap.ST Heap.RealWorld ();
check_prop_fail broadcast bounds automata m show_clock show_state =
  let {
    states_ia = map (states_i automata) (upt zero_nat (size_list automata));
    check_states =
      (\ (l, s) ->
        (equal_nat (size_list l) (size_list automata) &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            (size_list automata)) &&
          equal_nat (size_list s) (n_vs bounds) && check_boundedi bounds s);
  } in (\ l_list m_list ->
         let {
           p_impl =
             (\ (a1, a2) ->
               do { 
                 x <- imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xc _ ->
                          imp_for_int zero_nat (plus_nat m one_nat) return
                            (\ xf _ ->
                              imp_for_int zero_nat (plus_nat m one_nat) return
                                (\ xj _ ->
                                  do { 
                                    x_i <- mtx_get (suc m) a2 (xc, xj);
                                    x <- mtx_get (suc m) a2 (xc, xf);
                                    xa <- mtx_get (suc m) a2 (xf, xj);
                                    return (dbm_le_int x_i (dbm_add_int x xa))
                                   })
                                True)
                            True)
                        True;
                 xa <- check_diag_impl_int m a2;
                 xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                         (\ xc _ -> do { 
                                      x_d <- mtx_get (suc m) a2 (xc, xc);
                                      return (dbm_le_int x_d (Le zero_int))
                                     })
                         True;
                 xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                         (\ xc _ -> do { 
                                      x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                      return (dbm_le_int x_e (Le zero_int))
                                     })
                         True;
                 return (check_states a1 && (x || xa) && xb && xc)
                });
           copy = amtx_copy;
           show_dbm =
             (\ ma ->
               do { 
                 s <- show_dbm_impl m show_clock
                        (\ x -> shows_prec_int zero_nat x []) ma;
                 return (implode s)
                });
           show_statea = (\ l -> let {
                                   s = show_state l;
                                   a = implode s;
                                 } in return a);
         } in do { 
                m_table <-
                  ht_new >>=
                    imp_nfoldli m_list (\ _ -> return True)
                      (\ xc sigma ->
                        do { 
                          x_e <-
                            imp_nfoldli (snd xc) (\ _ -> return True)
                              (\ xg sigmaa -> do { 
        x_g <- Heap.newListArray xg;
        return (x_g : sigmaa)
       })
                              [];
                          ht_update (fst xc) x_e sigma
                         });
                a <- check_prop_fail_impl p_impl copy show_dbm show_statea
                       l_list m_table;
                (case a of {
                  Nothing -> return ();
                  Just (l, ma) ->
                    let {
                      b = check_states l;
                      _ = println
                            (if b then "State passed" else "State failed");
                    } in do { 
                           ba <- check_diag_impl_int m ma;
                           let { _ =
                             println
                               (if ba then "DBM passed diag"
                                 else "DBM failed diag")
                             };
                           bb <- check_diag_nonpos m ma;
                           let { _ =
                             println
                               (if bb then "DBM passed diag nonpos"
                                 else "DBM failed diag nonpos")
                             };
                           bc <- check_nonneg m ma;
                           let { _ =
                             println
                               (if bc then "DBM passed nonneg"
                                 else "DBM failed nonneg")
                             };
                           s <- show_dbm_impl_all m show_clock
                                  (\ x -> shows_prec_int zero_nat x []) ma;
                           let { _ = println ("DBM: " ++ implode s) };
                           return ()
                          };
                })
               });

convert_state_space ::
  Nat -> (([Int], [Int]) -> Bool) -> State_space Int -> State_space Nat;
convert_state_space m is_urgent (Reachable_Set xs) =
  Reachable_Set
    (map (\ (a, b) ->
           (case a of {
             (locs, vars) ->
               (\ dbms ->
                 ((map nat locs, vars),
                   map (convert_dbm (is_urgent (locs, vars)) m) dbms));
           })
             b)
      xs);
convert_state_space m is_urgent (Buechi_Set xs) =
  Buechi_Set
    (map (\ (a, b) ->
           (case a of {
             (locs, vars) ->
               (\ dbms ->
                 ((map nat locs, vars),
                   map (\ (dbm, aa) ->
                         (convert_dbm (is_urgent (locs, vars)) m dbm, aa))
                     dbms));
           })
             b)
      xs);

certificate_checker_pre1 ::
  forall a b c.
    [([Nat], [Int])] ->
      [(a, [([b], c)])] ->
        [Nat] ->
          [(Nat, (Int, Int))] ->
            [([Nat],
               ([Nat],
                 ([(Nat, (Bexp Nat Int,
                           ([Acconstraint Nat Int],
                             (Act Nat,
                               ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                   [(Nat, [Acconstraint Nat Int])])))] ->
              Nat ->
                (Nat -> Nat) ->
                  Nat ->
                    [[[Nat]]] ->
                      [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
certificate_checker_pre1 l_list m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let {
    _ = start_timer ();
    check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    _ = save_time "Time to check ceiling";
    n_ps = size_list automata;
    n_vsa = n_vs bounds;
    states_ia = map (states_i automata) (upt zero_nat n_ps);
    _ = start_timer ();
    check2 =
      all (\ (l, s) ->
            equal_nat (size_list l) n_ps &&
              all_interval_nat (\ i -> member (nth l i) (nth states_ia i))
                zero_nat n_ps &&
                equal_nat (size_list s) n_vsa && check_boundedi bounds s)
        l_list;
    _ = save_time "Time to check states";
    _ = start_timer ();
    n_sq = times_nat (suc m) (suc m);
    check3 =
      all (\ (_, a) -> all (\ (ma, _) -> equal_nat (size_list ma) n_sq) a)
        m_list;
    _ = save_time "Time to check DBMs";
    check4 = (case formula of {
               EX _ -> True;
               EG _ -> False;
               AX _ -> False;
               AG _ -> False;
               Leadsto _ _ -> False;
             });
    _ = map (\ (a, b) -> print_fail a b)
          [("Ceiling", check1), ("States", check2), ("DBM", check3),
            ("Formula", check4)];
  } in check1 && check2 && check3 && check4;

no_buechi_run_checker ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              [Nat] ->
                [(Nat, Int)] ->
                  Formula Nat Nat Nat Int ->
                    [([Nat], [Int])] ->
                      [(([Nat], [Int]), [([DBMEntry Int], Nat)])] ->
                        Nat -> Bool;
no_buechi_run_checker broadcast bounds automata m num_states num_actions l_0 s_0
  formula l_list m_list num_split =
  let {
    n_vsa = n_vs bounds;
    n_ps = size_list automata;
    invs =
      IArray.of_list
        (map (\ i ->
               let {
                 ma = default_map_of [] (snd (snd (snd (nth automata i))));
                 mb = IArray.of_list (map ma (upt zero_nat (num_states i)));
               } in mb)
          (upt zero_nat n_ps));
    succsi = succs_impl broadcast bounds automata m num_actions n_ps invs;
    states_ia = map (states_i automata) (upt zero_nat n_ps);
    check_state =
      (\ (l, s) ->
        (equal_nat (size_list l) n_ps &&
          all_interval_nat (\ i -> member (nth l i) (nth states_ia i)) zero_nat
            n_ps) &&
          equal_nat (size_list s) n_vsa && check_boundedi bounds s);
    mi = hashmap_of_list
           (map (\ (k, dbms) ->
                  (k, map (\ (ma, a) -> (IArray.of_list ma, a)) dbms))
             m_list);
    init_dbm = amtx_dflt (suc m) (suc m) (Le zero_int);
  } in certify_no_buechi_run_pure
         (\ x ->
           run_heap .
             (\ xs ->
               let {
                 li = id x;
               } in do { 
                      xsi <- fold_map array_unfreezea xs;
                      succsi li xsi >>=
                        fold_map
                          (\ (lia, xsia) ->
                            do { 
                              xsa <- fold_map array_freezea xsia;
                              return (id lia, xsa)
                             })
                     }))
         l_list
         (\ asa bs ->
           not (all_interval_nat
                 (not .
                   (\ i ->
                     dbm_lt_0
                       (sub asa (plus_nat (plus_nat i (times_nat i m)) i))))
                 zero_nat (suc m)) ||
             array_all2 (times_nat (suc m) (suc m)) dbm_le_int asa bs)
         (split_kb num_split m_list)
         (\ a ->
           run_heap
             (do { 
                (a1, a2) <- (case a of {
                              (l, s) -> do { 
  sa <- array_unfreezea s;
  return (id l, sa)
 };
                            });
                x <- imp_for_int zero_nat (plus_nat m one_nat) return
                       (\ xc _ ->
                         imp_for_int zero_nat (plus_nat m one_nat) return
                           (\ xf _ ->
                             imp_for_int zero_nat (plus_nat m one_nat) return
                               (\ xj _ ->
                                 do { 
                                   x_i <- mtx_get (suc m) a2 (xc, xj);
                                   x <- mtx_get (suc m) a2 (xc, xf);
                                   xa <- mtx_get (suc m) a2 (xf, xj);
                                   return (dbm_le_int x_i (dbm_add_int x xa))
                                  })
                               True)
                           True)
                       True;
                xa <- check_diag_impl_int m a2;
                xb <- imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xc _ -> do { 
                                     x_d <- mtx_get (suc m) a2 (xc, xc);
                                     return (dbm_le_int x_d (Le zero_int))
                                    })
                        True;
                xc <- imp_for_int zero_nat (plus_nat m one_nat) return
                        (\ xc _ -> do { 
                                     x_e <- mtx_get (suc m) a2 (zero_nat, xc);
                                     return (dbm_le_int x_e (Le zero_int))
                                    })
                        True;
                return (check_state a1 && (x || xa) && xb && xc)
               }))
         (\ a ->
           run_heap (do { 
                       xi <- (case a of {
                               (l, s) -> do { 
   sa <- array_unfreezea s;
   return (id l, sa)
  };
                             });
                       return (case xi of {
                                ((aa, b), _) -> hd_of_formulai formula aa b;
                              })
                      }))
         (\ k -> ahm_lookup (\ a b -> a == b) bounded_hashcode_nat k mi)
         (run_heap
           (imp_nfoldli [(l_0, map (the . map_of s_0) (upt zero_nat n_vsa))]
              (\ _ -> return True)
              (\ xc sigma ->
                do { 
                  x <- init_dbm;
                  return (op_list_concat sigma (op_list_prepend (xc, x) []))
                 })
              [] >>=
             fold_map (\ (l, s) -> do { 
                                     sa <- array_freezea s;
                                     return (id l, sa)
                                    })));

buechi_certificate_checker ::
  Nat ->
    [(([Nat], [Int]), [([DBMEntry Int], Nat)])] ->
      [Nat] ->
        [(Nat, (Int, Int))] ->
          [([Nat],
             ([Nat],
               ([(Nat, (Bexp Nat Int,
                         ([Acconstraint Nat Int],
                           (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                 [(Nat, [Acconstraint Nat Int])])))] ->
            Nat ->
              (Nat -> Nat) ->
                Nat ->
                  [[[Nat]]] ->
                    [Nat] -> [(Nat, Int)] -> Formula Nat Nat Nat Int -> Bool;
buechi_certificate_checker num_split m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let {
    l_list = map fst m_list;
  } in (case certificate_checker_pre1 l_list m_list broadcast bounds automata m
               num_states num_actions k l_0 s_0 formula
         of {
         True ->
           no_buechi_run_checker broadcast bounds automata m num_states
             num_actions l_0 s_0 formula l_list m_list num_split;
         False -> let {
                    _ = println "Checking Buechi preconditions failed";
                  } in False;
       });

rename_check_buechi ::
  Nat ->
    [String] ->
      [(String, (Int, Int))] ->
        [([Nat],
           ([Nat],
             ([(Nat, (Bexp String Int,
                       ([Acconstraint String Int],
                         (Act String,
                           ([(String, Exp String Int)], ([String], Nat))))))],
               [(Nat, [Acconstraint String Int])])))] ->
          [[[Nat]]] ->
            [Nat] ->
              [(String, Int)] ->
                Formula Nat Nat String Int ->
                  Nat ->
                    (Nat -> Nat) ->
                      Nat ->
                        (String -> Nat) ->
                          (String -> Nat) ->
                            (String -> Nat) ->
                              (Nat -> Nat -> Nat) ->
                                [(([Nat], [Int]), [([DBMEntry Int], Nat)])] ->
                                  Resulta;
rename_check_buechi num_split broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case (do_rename_mc ::
          ((Nat -> [Char]) ->
            (([Nat], [Int]) -> [Char]) ->
              [Nat] ->
                [(Nat, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp Nat Int,
                                 ([Acconstraint Nat Int],
                                   (Act Nat,
                                     ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                         [(Nat, [Acconstraint Nat Int])])))] ->
                    Nat ->
                      (Nat -> Nat) ->
                        Nat ->
                          [[[Nat]]] ->
                            [Nat] ->
                              [(Nat, Int)] ->
                                Formula Nat Nat Nat Int -> Bool) ->
            Bool ->
              [String] ->
                [(String, (Int, Int))] ->
                  [([Nat],
                     ([Nat],
                       ([(Nat, (Bexp String Int,
                                 ([Acconstraint String Int],
                                   (Act String,
                                     ([(String, Exp String Int)],
                                       ([String], Nat))))))],
                         [(Nat, [Acconstraint String Int])])))] ->
                    [[[Nat]]] ->
                      String ->
                        [Nat] ->
                          [(String, Int)] ->
                            Formula Nat Nat String Int ->
                              Nat ->
                                (Nat -> Nat) ->
                                  Nat ->
                                    (String -> Nat) ->
                                      (String -> Nat) ->
(String -> Nat) ->
  (Nat -> Nat -> Nat) ->
    (Nat -> Nat -> [Char]) -> (Nat -> [Char]) -> (Nat -> [Char]) -> Maybe Bool)
          (\ _ _ -> buechi_certificate_checker num_split state_space) False
          broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          (\ _ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
          (\ _ -> [Char False False False False False True False False])
    of {
    Nothing -> Renaming_Failed;
    Just True -> Sat;
    Just False -> Unsat;
  });

buechi_of ::
  forall a. State_space a -> [(([a], [Int]), [([DBMEntry Int], Nat)])];
buechi_of (Buechi_Set x2) = x2;

reach_of :: forall a. State_space a -> [(([a], [Int]), [[DBMEntry Int]])];
reach_of (Reachable_Set x1) = x1;

check_invariant_fail ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              (Nat -> [Char]) ->
                (([Nat], [Int]) -> [Char]) ->
                  [([Nat], [Int])] ->
                    [(([Nat], [Int]), [[DBMEntry Int]])] ->
                      Heap.ST Heap.RealWorld ();
check_invariant_fail broadcast bounds automata m num_states num_actions
  show_clock show_state =
  (\ l_list m_list ->
    let {
      copy = amtx_copy;
      succs =
        let {
          n_ps = size_list automata;
          invs =
            IArray.of_list
              (map (\ i ->
                     let {
                       ma = default_map_of []
                              (snd (snd (snd (nth automata i))));
                       mb = IArray.of_list
                              (map ma (upt zero_nat (num_states i)));
                     } in mb)
                (upt zero_nat n_ps));
          inv_fun =
            (\ (l, _) ->
              concatMap (\ i -> sub (sub invs i) (nth l i))
                (upt zero_nat n_ps));
          trans_mapa = trans_map automata;
          trans_i_map =
            (\ i j ->
              map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (b, (g, (Sil aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                  }))
                (trans_mapa i j));
          int_trans_from_loc_impl =
            (\ p l la s ->
              let {
                a = trans_i_map p l;
              } in map_filter
                     (\ (b, (g, (aa, (f, (r, lb))))) ->
                       let {
                         sa = mk_updsi s f;
                       } in (if bvali s b && check_boundedi bounds sa
                              then Just (g,
  (Internal aa, (r, (list_update la p lb, sa))))
                              else Nothing))
                     a);
          int_trans_from_vec_impl =
            (\ pairs l s ->
              concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s) pairs);
          int_trans_from_all_impl =
            (\ l s ->
              concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
                (upt zero_nat n_ps));
          trans_out_map =
            (\ i j ->
              map_filter
                (\ a ->
                  (case a of {
                    (_, (_, (In _, (_, _)))) -> Nothing;
                    (b, (g, (Out aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j));
          trans_in_map =
            (\ i j ->
              map_filter
                (\ a ->
                  (case a of {
                    (b, (g, (In aa, (ma, l)))) -> Just (b, (g, (aa, (ma, l))));
                    (_, (_, (Out _, (_, _)))) -> Nothing;
                    (_, (_, (Sil _, (_, _)))) -> Nothing;
                  }))
                (trans_mapa i j));
          trans_out_broad_grouped =
            (\ i j ->
              actions_by_statea num_actions
                (map_filter
                  (\ a ->
                    (case a of {
                      (_, (_, (In _, (_, _)))) -> Nothing;
                      (b, (g, (Out aa, (ma, l)))) ->
                        (if membera broadcast aa
                          then Just (b, (g, (aa, (ma, l)))) else Nothing);
                      (_, (_, (Sil _, (_, _)))) -> Nothing;
                    }))
                  (trans_mapa i j)));
          trans_in_broad_grouped =
            (\ i j ->
              actions_by_statea num_actions
                (map_filter
                  (\ a ->
                    (case a of {
                      (b, (g, (In aa, (ma, l)))) ->
                        (if membera broadcast aa
                          then Just (b, (g, (aa, (ma, l)))) else Nothing);
                      (_, (_, (Out _, (_, _)))) -> Nothing;
                      (_, (_, (Sil _, (_, _)))) -> Nothing;
                    }))
                  (trans_mapa i j)));
          broad_trans_impl =
            (\ (l, s) ->
              let {
                pairs = get_committed broadcast bounds automata l;
                ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                        (upt zero_nat n_ps);
                out = map (\ p -> trans_out_broad_grouped p (nth l p))
                        (upt zero_nat n_ps);
                inb = map (map (filter (\ (b, _) -> bvali s b))) ina;
                outa = map (map (filter (\ (b, _) -> bvali s b))) out;
              } in (if null pairs
                     then concatMap
                            (\ a ->
                              concatMap
                                (\ p ->
                                  let {
                                    outs = nth (nth outa p) a;
                                  } in (if null outs then []
 else let {
        combs = make_combs broadcast bounds automata p a inb;
        outsa = map (\ aa -> (p, aa)) outs;
        combsa =
          (if null combs then map (\ x -> [x]) outsa
            else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
        init = ([], (Broad a, ([], (l, s))));
      } in compute_upds_impl bounds init combsa))
                                (upt zero_nat n_ps))
                            (upt zero_nat num_actions)
                     else concatMap
                            (\ a ->
                              let {
                                ins_committed =
                                  map_filter
                                    (\ (p, _) ->
                                      (if not (null (nth (nth inb p) a))
then Just p else Nothing))
                                    pairs;
                                always_committed =
                                  less_nat one_nat (size_list ins_committed);
                              } in concatMap
                                     (\ p ->
                                       let {
 outs = nth (nth outa p) a;
                                       } in
 (if null outs then []
   else (if not always_committed &&
              (ins_committed == [p] || null ins_committed) &&
                not (any (\ (q, _) -> equal_nat q p) pairs)
          then []
          else let {
                 combs = make_combs broadcast bounds automata p a inb;
                 outsa = map (\ aa -> (p, aa)) outs;
                 combsa =
                   (if null combs then map (\ x -> [x]) outsa
                     else concatMap (\ x -> map (\ aa -> x : aa) combs) outsa);
                 init = ([], (Broad a, ([], (l, s))));
               } in compute_upds_impl bounds init combsa)))
                                     (upt zero_nat n_ps))
                            (upt zero_nat num_actions)));
          bin_trans_impl =
            (\ (l, s) ->
              let {
                pairs = get_committed broadcast bounds automata l;
                ina = all_actions_by_state broadcast bounds automata num_actions
                        trans_in_map l;
                out = all_actions_by_state broadcast bounds automata num_actions
                        trans_out_map l;
              } in (if null pairs
                     then concatMap
                            (\ a ->
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth ina a))
                            (bin_actions broadcast num_actions)
                     else let {
                            in2 = all_actions_from_vec num_actions trans_in_map
                                    pairs;
                            out2 =
                              all_actions_from_vec num_actions trans_out_map
                                pairs;
                          } in concatMap
                                 (\ a ->
                                   pairs_by_action_impl bounds l s (nth out a)
                                     (nth in2 a))
                                 (bin_actions broadcast num_actions) ++
                                 concatMap
                                   (\ a ->
                                     pairs_by_action_impl bounds l s
                                       (nth out2 a) (nth ina a))
                                   (bin_actions broadcast num_actions)));
          int_trans_impl =
            (\ (l, s) ->
              let {
                pairs = get_committed broadcast bounds automata l;
              } in (if null pairs then int_trans_from_all_impl l s
                     else int_trans_from_vec_impl pairs l s));
          trans_impl =
            (\ st ->
              int_trans_impl st ++ bin_trans_impl st ++ broad_trans_impl st);
          e_op_impl =
            (\ ai bic bib bia bi ->
              do { 
                x <- up_canonical_upd_impl_int m bi m;
                xa <- imp_nfoldli (inv_fun ai) (\ _ -> return True)
                        (\ aia bid ->
                          do { 
                            xa <- abstra_upd_impl_int m aia bid;
                            repair_pair_impl_int m xa zero_nat
                              (constraint_clk aia)
                           })
                        x;
                xaa <- check_diag_impl_int m xa;
                x_a <-
                  (if xaa
                    then mtx_set (suc m) xa (zero_nat, zero_nat) (Lt zero_int)
                    else imp_nfoldli bib (\ _ -> return True)
                           (\ aia bid ->
                             do { 
                               xb <- abstra_upd_impl_int m aia bid;
                               repair_pair_impl_int m xb zero_nat
                                 (constraint_clk aia)
                              })
                           xa);
                x_b <- check_diag_impl_int m x_a;
                (if x_b
                  then mtx_set (suc m) x_a (zero_nat, zero_nat) (Lt zero_int)
                  else imp_nfoldli bic (\ _ -> return True)
                         (\ xc sigma ->
                           reset_canonical_upd_impl_int m sigma m xc zero_int)
                         x_a >>=
                         imp_nfoldli (inv_fun bia) (\ _ -> return True)
                           (\ aia bid ->
                             do { 
                               xb <- abstra_upd_impl_int m aia bid;
                               repair_pair_impl_int m xb zero_nat
                                 (constraint_clk aia)
                              }))
               });
        } in (\ ai bi ->
               (if null bi then return []
                 else imp_nfoldli (trans_impl ai) (\ _ -> return True)
                        (\ xc sigma ->
                          (case xc of {
                            (a1, (_, (a1b, a2b))) ->
                              do { 
                                x <- heap_map amtx_copy bi;
                                x_d <-
                                  imp_nfoldli x (\ _ -> return True)
                                    (\ xb sigmaa ->
                                      do { 
x_c <- pR_CONST e_op_impl ai a1b a1 a2b xb;
x_e <- check_diag_impl_int m x_c;
return (if x_e then sigmaa else op_list_prepend x_c sigmaa)
                                       })
                                    [];
                                return (op_list_prepend (a2b, x_d) sigma)
                               };
                          }))
                        []));
      lei = dbm_subset_impl_int m;
      show_statea = (\ l -> let {
                              s = show_state l;
                              a = implode s;
                            } in return a);
      show_dbm =
        show_dbm_impl_all m show_clock (\ x -> shows_prec_int zero_nat x []);
    } in do { 
           m_table <-
             ht_new >>=
               imp_nfoldli m_list (\ _ -> return True)
                 (\ xc sigma ->
                   do { 
                     x_e <-
                       imp_nfoldli (snd xc) (\ _ -> return True)
                         (\ xg sigmaa -> do { 
   x_g <- Heap.newListArray xg;
   return (x_g : sigmaa)
  })
                         [];
                     ht_update (fst xc) x_e sigma
                    });
           a <- check_invariant_fail_impl copy lei succs l_list m_table;
           (case a of {
             Nothing -> return ();
             Just (Inl (Inl (l, (la, xs)))) ->
               let {
                 _ = println "The successor is not contained in L:";
               } in do { 
                      s <- show_statea l;
                      let { _ = println ("  " ++ s) };
                      sa <- show_statea la;
                      let { _ = println ("  " ++ sa) };
                      _ <- fold_map
                             (\ ma ->
                               do { 
                                 sb <- show_dbm ma;
                                 let { _ = println (" " ++ implode sb) };
                                 return ()
                                })
                             xs;
                      return ()
                     };
             Just (Inl (Inr (l, (la, xs)))) ->
               let {
                 _ = println "The successor is not empty:";
               } in do { 
                      s <- show_statea l;
                      let { _ = println ("  " ++ s) };
                      sa <- show_statea la;
                      let { _ = println ("  " ++ sa) };
                      _ <- fold_map
                             (\ ma ->
                               do { 
                                 sb <- show_dbm ma;
                                 let { _ = println (" " ++ implode sb) };
                                 return ()
                                })
                             xs;
                      return ()
                     };
             Just (Inr (l, (asa, (la, (ma, xs))))) ->
               do { 
                 s1 <- show_statea l;
                 s2 <- show_statea la;
                 s3 <- show_dbm ma;
                 let { _ = println ("\nA successor of the zones for:\n  " ++ s1)
                   };
                 _ <- fold_map
                        (\ mb -> do { 
                                   s <- show_dbm mb;
                                   let { _ = println ("\n" ++ implode s) };
                                   return ()
                                  })
                        asa;
                 let { _ = println (("\nis not subsumed:\n  " ++ s2) ++ "\n") };
                 let { _ = println (implode s3 ++ "\n") };
                 let { _ = println "These are the candidate dbms:" };
                 _ <- fold_map
                        (\ mb -> do { 
                                   s <- show_dbm mb;
                                   let { _ = println ("\n" ++ implode s) };
                                   return ()
                                  })
                        xs;
                 let { _ = println "" };
                 return ()
                };
           })
          });

check_deadlock_fail ::
  [Nat] ->
    [(Nat, (Int, Int))] ->
      [([Nat],
         ([Nat],
           ([(Nat, (Bexp Nat Int,
                     ([Acconstraint Nat Int],
                       (Act Nat, ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
             [(Nat, [Acconstraint Nat Int])])))] ->
        Nat ->
          (Nat -> Nat) ->
            Nat ->
              (Nat -> [Char]) ->
                (([Nat], [Int]) -> [Char]) ->
                  [([Nat], [Int])] ->
                    [(([Nat], [Int]), [[DBMEntry Int]])] ->
                      Heap.ST Heap.RealWorld ();
check_deadlock_fail broadcast bounds automata m num_states num_actions
  show_clock show_state =
  (\ l_list m_list ->
    let {
      p_impl =
        (\ (a, b) ->
          let {
            n_ps = size_list automata;
            invs =
              IArray.of_list
                (map (\ i ->
                       let {
                         ma = default_map_of []
                                (snd (snd (snd (nth automata i))));
                         mb = IArray.of_list
                                (map ma (upt zero_nat (num_states i)));
                       } in mb)
                  (upt zero_nat n_ps));
            inv_fun =
              (\ (l, _) ->
                concatMap (\ i -> sub (sub invs i) (nth l i))
                  (upt zero_nat n_ps));
            trans_impl =
              let {
                trans_mapa = trans_map automata;
                trans_i_map =
                  (\ i j ->
                    map_filter
                      (\ aa ->
                        (case aa of {
                          (_, (_, (In _, (_, _)))) -> Nothing;
                          (_, (_, (Out _, (_, _)))) -> Nothing;
                          (ba, (g, (Sil ab, (ma, l)))) ->
                            Just (ba, (g, (ab, (ma, l))));
                        }))
                      (trans_mapa i j));
                int_trans_from_loc_impl =
                  (\ p l la s ->
                    let {
                      aa = trans_i_map p l;
                    } in map_filter
                           (\ (ba, (g, (ab, (f, (r, lb))))) ->
                             let {
                               sa = mk_updsi s f;
                             } in (if bvali s ba && check_boundedi bounds sa
                                    then Just
   (g, (Internal ab, (r, (list_update la p lb, sa))))
                                    else Nothing))
                           aa);
                int_trans_from_vec_impl =
                  (\ pairs l s ->
                    concatMap (\ (p, la) -> int_trans_from_loc_impl p la l s)
                      pairs);
                int_trans_from_all_impl =
                  (\ l s ->
                    concatMap (\ p -> int_trans_from_loc_impl p (nth l p) l s)
                      (upt zero_nat n_ps));
                trans_out_map =
                  (\ i j ->
                    map_filter
                      (\ aa ->
                        (case aa of {
                          (_, (_, (In _, (_, _)))) -> Nothing;
                          (ba, (g, (Out ab, (ma, l)))) ->
                            Just (ba, (g, (ab, (ma, l))));
                          (_, (_, (Sil _, (_, _)))) -> Nothing;
                        }))
                      (trans_mapa i j));
                trans_in_map =
                  (\ i j ->
                    map_filter
                      (\ aa ->
                        (case aa of {
                          (ba, (g, (In ab, (ma, l)))) ->
                            Just (ba, (g, (ab, (ma, l))));
                          (_, (_, (Out _, (_, _)))) -> Nothing;
                          (_, (_, (Sil _, (_, _)))) -> Nothing;
                        }))
                      (trans_mapa i j));
                trans_out_broad_grouped =
                  (\ i j ->
                    actions_by_statea num_actions
                      (map_filter
                        (\ aa ->
                          (case aa of {
                            (_, (_, (In _, (_, _)))) -> Nothing;
                            (ba, (g, (Out ab, (ma, l)))) ->
                              (if membera broadcast ab
                                then Just (ba, (g, (ab, (ma, l))))
                                else Nothing);
                            (_, (_, (Sil _, (_, _)))) -> Nothing;
                          }))
                        (trans_mapa i j)));
                trans_in_broad_grouped =
                  (\ i j ->
                    actions_by_statea num_actions
                      (map_filter
                        (\ aa ->
                          (case aa of {
                            (ba, (g, (In ab, (ma, l)))) ->
                              (if membera broadcast ab
                                then Just (ba, (g, (ab, (ma, l))))
                                else Nothing);
                            (_, (_, (Out _, (_, _)))) -> Nothing;
                            (_, (_, (Sil _, (_, _)))) -> Nothing;
                          }))
                        (trans_mapa i j)));
                broad_trans_impl =
                  (\ (l, s) ->
                    let {
                      pairs = get_committed broadcast bounds automata l;
                      ina = map (\ p -> trans_in_broad_grouped p (nth l p))
                              (upt zero_nat n_ps);
                      out = map (\ p -> trans_out_broad_grouped p (nth l p))
                              (upt zero_nat n_ps);
                      inb = map (map (filter (\ (ba, _) -> bvali s ba))) ina;
                      outa = map (map (filter (\ (ba, _) -> bvali s ba))) out;
                    } in (if null pairs
                           then concatMap
                                  (\ aa ->
                                    concatMap
                                      (\ p ->
let {
  outs = nth (nth outa p) aa;
} in (if null outs then []
       else let {
              combs = make_combs broadcast bounds automata p aa inb;
              outsa = map (\ ab -> (p, ab)) outs;
              combsa =
                (if null combs then map (\ x -> [x]) outsa
                  else concatMap (\ x -> map (\ ab -> x : ab) combs) outsa);
              init = ([], (Broad aa, ([], (l, s))));
            } in compute_upds_impl bounds init combsa))
                                      (upt zero_nat n_ps))
                                  (upt zero_nat num_actions)
                           else concatMap
                                  (\ aa ->
                                    let {
                                      ins_committed =
map_filter
  (\ (p, _) -> (if not (null (nth (nth inb p) aa)) then Just p else Nothing))
  pairs;
                                      always_committed =
less_nat one_nat (size_list ins_committed);
                                    } in concatMap
   (\ p ->
     let {
       outs = nth (nth outa p) aa;
     } in (if null outs then []
            else (if not always_committed &&
                       (ins_committed == [p] || null ins_committed) &&
                         not (any (\ (q, _) -> equal_nat q p) pairs)
                   then []
                   else let {
                          combs = make_combs broadcast bounds automata p aa inb;
                          outsa = map (\ ab -> (p, ab)) outs;
                          combsa =
                            (if null combs then map (\ x -> [x]) outsa
                              else concatMap (\ x -> map (\ ab -> x : ab) combs)
                                     outsa);
                          init = ([], (Broad aa, ([], (l, s))));
                        } in compute_upds_impl bounds init combsa)))
   (upt zero_nat n_ps))
                                  (upt zero_nat num_actions)));
                bin_trans_impl =
                  (\ (l, s) ->
                    let {
                      pairs = get_committed broadcast bounds automata l;
                      ina = all_actions_by_state broadcast bounds automata
                              num_actions trans_in_map l;
                      out = all_actions_by_state broadcast bounds automata
                              num_actions trans_out_map l;
                    } in (if null pairs
                           then concatMap
                                  (\ aa ->
                                    pairs_by_action_impl bounds l s (nth out aa)
                                      (nth ina aa))
                                  (bin_actions broadcast num_actions)
                           else let {
                                  in2 = all_actions_from_vec num_actions
  trans_in_map pairs;
                                  out2 =
                                    all_actions_from_vec num_actions
                                      trans_out_map pairs;
                                } in concatMap
                                       (\ aa ->
 pairs_by_action_impl bounds l s (nth out aa) (nth in2 aa))
                                       (bin_actions broadcast num_actions) ++
                                       concatMap
 (\ aa -> pairs_by_action_impl bounds l s (nth out2 aa) (nth ina aa))
 (bin_actions broadcast num_actions)));
                int_trans_impl =
                  (\ (l, s) ->
                    let {
                      pairs = get_committed broadcast bounds automata l;
                    } in (if null pairs then int_trans_from_all_impl l s
                           else int_trans_from_vec_impl pairs l s));
              } in (\ st ->
                     int_trans_impl st ++
                       bin_trans_impl st ++ broad_trans_impl st);
          } in (\ ai bi ->
                 do { 
                   x <- imp_nfoldli (trans_impl ai) (\ _ -> return True)
                          (\ xb sigma ->
                            do { 
                              x <- v_dbm_impl m;
                              xa <- abstr_FW_impl_int m
                                      (inv_fun (snd (snd (snd xb)))) x;
                              xc <- pre_reset_list_impl m xa
                                      (fst (snd (snd xb)));
                              xd <- abstr_FW_impl_int m (fst xb) xc;
                              xe <- abstr_FW_impl_int m (inv_fun ai) xd;
                              x_c <- down_impl_int m xe;
                              return (x_c : sigma)
                             })
                          [];
                   dbm_subset_fed_impl m bi (op_list_rev x)
                  })
            a
            b);
      copy = amtx_copy;
      show_dbm =
        (\ ma ->
          do { 
            s <- show_dbm_impl m show_clock
                   (\ x -> shows_prec_int zero_nat x []) ma;
            return (implode s)
           });
      show_statea = (\ l -> let {
                              s = show_state l;
                              a = implode s;
                            } in return a);
    } in do { 
           m_table <-
             ht_new >>=
               imp_nfoldli m_list (\ _ -> return True)
                 (\ xc sigma ->
                   do { 
                     x_e <-
                       imp_nfoldli (snd xc) (\ _ -> return True)
                         (\ xg sigmaa -> do { 
   x_g <- Heap.newListArray xg;
   return (x_g : sigmaa)
  })
                         [];
                     ht_update (fst xc) x_e sigma
                    });
           a <- check_prop_fail_impl p_impl copy show_dbm show_statea l_list
                  m_table;
           (case a of {
             Nothing -> return ();
             Just (l, ma) ->
               let {
                 _ = println "\nThe following state is deadlocked";
               } in do { 
                      s <- show_statea l;
                      let { _ = println s };
                      sa <- show_dbm_impl_all m show_clock
                              (\ x -> shows_prec_int zero_nat x []) ma;
                      let { _ = println (implode sa) };
                      return ()
                     };
           })
          });

certificate_checker_dbg ::
  Nat ->
    Bool ->
      (Nat -> [Char]) ->
        (([Nat], [Int]) -> [Char]) ->
          [(([Nat], [Int]), [[DBMEntry Int]])] ->
            [Nat] ->
              [(Nat, (Int, Int))] ->
                [([Nat],
                   ([Nat],
                     ([(Nat, (Bexp Nat Int,
                               ([Acconstraint Nat Int],
                                 (Act Nat,
                                   ([(Nat, Exp Nat Int)], ([Nat], Nat))))))],
                       [(Nat, [Acconstraint Nat Int])])))] ->
                  Nat ->
                    (Nat -> Nat) ->
                      Nat ->
                        [[[Nat]]] ->
                          [Nat] ->
                            [(Nat, Int)] ->
                              Formula Nat Nat Nat Int ->
                                Heap.ST Heap.RealWorld (Maybe Bool);
certificate_checker_dbg num_split dc show_clock show_state m_list broadcast
  bounds automata m num_states num_actions k l_0 s_0 formula =
  let {
    _ = start_timer ();
    check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    _ = save_time "Time to check ceiling";
    l_list = map fst m_list;
    n_ps = size_list automata;
    n_vsa = n_vs bounds;
    states_ia = map (states_i automata) (upt zero_nat n_ps);
    _ = start_timer ();
    check2 =
      all (\ (l, s) ->
            equal_nat (size_list l) n_ps &&
              all_interval_nat (\ i -> member (nth l i) (nth states_ia i))
                zero_nat n_ps &&
                equal_nat (size_list s) n_vsa && check_boundedi bounds s)
        l_list;
    _ = save_time "Time to check states";
    check3 = (case formula of {
               EX _ -> True;
               EG _ -> False;
               AX _ -> False;
               AG _ -> False;
               Leadsto _ _ -> False;
             });
  } in (if check1 && check2 && check3
         then do { 
                _ <- check_prop_fail broadcast bounds automata m show_clock
                       show_state l_list m_list;
                _ <- check_invariant_fail broadcast bounds automata m num_states
                       num_actions show_clock show_state l_list m_list;
                _ <- (if dc
                       then check_deadlock_fail broadcast bounds automata m
                              num_states num_actions show_clock show_state
                              l_list m_list
                       else return ());
                r <- unreachability_checker broadcast bounds automata m
                       num_states num_actions l_0 s_0 formula l_list m_list
                       num_split;
                return (Just r)
               }
         else return Nothing);

rename_check_dbg ::
  forall a b c.
    (Showa a, Showa b,
      Showa c) => Nat ->
                    Bool ->
                      [String] ->
                        [(String, (Int, Int))] ->
                          [([Nat],
                             ([Nat],
                               ([(Nat, (Bexp String Int,
 ([Acconstraint String Int],
   (Act String, ([(String, Exp String Int)], ([String], Nat))))))],
                                 [(Nat, [Acconstraint String Int])])))] ->
                            [[[Nat]]] ->
                              [Nat] ->
                                [(String, Int)] ->
                                  Formula Nat Nat String Int ->
                                    Nat ->
                                      (Nat -> Nat) ->
Nat ->
  (String -> Nat) ->
    (String -> Nat) ->
      (String -> Nat) ->
        (Nat -> Nat -> Nat) ->
          (Nat -> Nat -> a) ->
            (Nat -> b) ->
              (Nat -> c) ->
                [(([Nat], [Int]), [[DBMEntry Int]])] ->
                  Heap.ST Heap.RealWorld Resulta;
rename_check_dbg num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  inv_renum_states inv_renum_vars inv_renum_clocks state_space =
  (case do_rename_mc
          (\ show_clock show_state ->
            certificate_checker_dbg num_split dc show_clock show_state
              state_space)
          dc broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          inv_renum_states inv_renum_vars inv_renum_clocks
    of {
    Nothing -> return Renaming_Failed;
    Just r -> do { 
                a <- r;
                (case a of {
                  Nothing -> return Preconds_Unsat;
                  Just True -> return Sat;
                  Just False -> return Unsat;
                })
               };
  });

parse_convert_check ::
  Mode ->
    Nat ->
      Bool ->
        String ->
          String -> State_space Int -> Bool -> Heap.ST Heap.RealWorld ();
parse_convert_check mode num_split dc model renaming state_space show_cert =
  (case parse_compute model renaming of {
    Result
      (broadcast,
        (bounds,
          (automata,
            (urgent_locations,
              (k, (l_0, (s_0, (formula,
                                (m, (num_states,
                                      (num_actions,
(renum_acts,
  (renum_vars,
    (renum_clocks,
      (renum_states,
        (inv_renum_states, (inv_renum_vars, inv_renum_clocks)))))))))))))))))
      -> let {
           is_urgent =
             (\ (l, _) ->
               any (\ (la, urgent) -> membera (map int_of_nat urgent) la)
                 (zip l urgent_locations));
           inv_renum_clocksa =
             (\ i -> (if equal_nat i m then "_urge" else inv_renum_clocks i));
           t = Prelude.const 0 ();
           state_spacea = convert_state_space m is_urgent state_space;
           ta = (-) (Prelude.const 0 ()) t;
           _ = println ("Time for converting state space: " ++ Prelude.show ta);
           _ = start_timer ();
           _ = save_time "Time for converting DBMs in certificate";
           _ = println
                 ("Number of discrete states: " ++
                   show_lit (len_of_state_space state_spacea));
           _ = (if show_cert
                 then let {
                        _ = print_sep ();
                        _ = println "Certificate";
                        _ = print_sep ();
                        _ = show_state_space m inv_renum_states inv_renum_vars
                              inv_renum_clocksa state_spacea;
                        _ = print_sep ();
                      } in return ()
                 else return ());
           tb = Prelude.const 0 ();
         } in do { 
                check <-
                  (case mode of {
                    Impl1 ->
                      rename_check num_split dc broadcast bounds automata k l_0
                        s_0 formula m num_states num_actions renum_acts
                        renum_vars renum_clocks renum_states
                        (reach_of state_spacea);
                    Impl2 ->
                      return
                        (rename_check2 num_split dc broadcast bounds automata k
                          l_0 s_0 formula m num_states num_actions renum_acts
                          renum_vars renum_clocks renum_states
                          (reach_of state_spacea));
                    Impl3 ->
                      return
                        (rename_check3 num_split dc broadcast bounds automata k
                          l_0 s_0 formula m num_states num_actions renum_acts
                          renum_vars renum_clocks renum_states
                          (reach_of state_spacea));
                    Buechi ->
                      return
                        (rename_check_buechi num_split broadcast bounds automata
                          k l_0 s_0 formula m num_states num_actions renum_acts
                          renum_vars renum_clocks renum_states
                          (buechi_of state_spacea));
                    Debug ->
                      rename_check_dbg num_split dc broadcast bounds automata k
                        l_0 s_0 formula m num_states num_actions renum_acts
                        renum_vars renum_clocks renum_states inv_renum_states
                        inv_renum_vars inv_renum_clocksa
                        (reach_of state_spacea);
                  });
                let { tc = (-) (Prelude.const 0 ()) tb };
                let { _ =
                  println ("Time for certificate checking: " ++ Prelude.show tc)
                  };
                (case check of {
                  Renaming_Failed -> let {
                                       _ = println "Renaming failed";
                                     } in return ();
                  Preconds_Unsat -> let {
                                      _ = println "Preconditions were not met";
                                    } in return ();
                  Sat -> let {
                           _ = println "Certificate was accepted";
                         } in return ();
                  Unsat -> let {
                             _ = println "Certificate was rejected";
                           } in return ();
                })
               };
    Error es -> let {
                  _ = map println es;
                } in return ();
  });

equal_mode :: Mode -> Mode -> Bool;
equal_mode Buechi Debug = False;
equal_mode Debug Buechi = False;
equal_mode Impl3 Debug = False;
equal_mode Debug Impl3 = False;
equal_mode Impl3 Buechi = False;
equal_mode Buechi Impl3 = False;
equal_mode Impl2 Debug = False;
equal_mode Debug Impl2 = False;
equal_mode Impl2 Buechi = False;
equal_mode Buechi Impl2 = False;
equal_mode Impl2 Impl3 = False;
equal_mode Impl3 Impl2 = False;
equal_mode Impl1 Debug = False;
equal_mode Debug Impl1 = False;
equal_mode Impl1 Buechi = False;
equal_mode Buechi Impl1 = False;
equal_mode Impl1 Impl3 = False;
equal_mode Impl3 Impl1 = False;
equal_mode Impl1 Impl2 = False;
equal_mode Impl2 Impl1 = False;
equal_mode Debug Debug = True;
equal_mode Buechi Buechi = True;
equal_mode Impl3 Impl3 = True;
equal_mode Impl2 Impl2 = True;
equal_mode Impl1 Impl1 = True;

parse_convert_run_check ::
  Mode -> Nat -> Bool -> String -> Heap.ST Heap.RealWorld ();
parse_convert_run_check mode num_split dc s =
  (case binda (parse json s) convert of {
    Result
      (ids_to_names,
        (_, (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
      -> (case rename_state_space dc ids_to_names
                 (broadcast, (automata, bounds)) l_0 s_0 formula
           of {
           Result (Nothing, (_, (_, (_, _)))) -> return ();
           Result (Just r, (_, (_, (renamings, k)))) ->
             let {
               t = Prelude.const 0 ();
             } in do { 
                    ra <- r;
                    let { ta = (-) (Prelude.const 0 ()) t };
                    _ <- Printing.printM ("Time for model checking + certificate extraction: " ++
   Prelude.show ta);
                    (case renamings of {
                      (m, (num_states,
                            (num_actions,
                              (renum_acts,
                                (renum_vars,
                                  (renum_clocks,
                                    (renum_states,
                                      (inv_renum_states,
(inv_renum_vars, inv_renum_clocks)))))))))
                        -> let {
                             _ = start_timer ();
                           } in do { 
                                  state_space <-
                                    fold_map
                                      (\ (sa, xs) ->
let {
  xsa = map snd xs;
} in do { 
       xsb <- fold_map (dbm_to_list_impl m) xsa;
       return (sa, xsb)
      })
                                      ra;
                                  let { _ =
                                    save_time
                                      "Time for converting DBMs in certificate"
                                    };
                                  _ <- Printing.printM ("Number of discrete states of state space: " ++
                 show_lit (size_list state_space));
                                  let { _ =
                                    println
                                      ("Size of passed list: " ++
show_str (sum_list (map (size_list . snd) ra)))
                                    };
                                  _ <- Printing.printM ("DBM list length distribution: " ++
                 show_str (distr (map (size_list . snd) state_space)));
                                  let { split =
                                    (if equal_mode mode Impl3
                                      then split_k num_split state_space
                                      else split_ka num_split state_space)
                                    };
                                  let { split_distr =
                                    map (sum_list . map (size_list . snd)) split
                                    };
                                  _ <- Printing.printM ("Size of passed list distribution after split: " ++
                 show_str split_distr);
                                  let { tb = Prelude.const 0 () };
                                  check <-
                                    (case mode of {
                                      Impl1 ->
rename_check num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space;
                                      Impl2 ->
return
  (rename_check2 num_split dc broadcast bounds automata k l_0 s_0 formula m
    num_states num_actions renum_acts renum_vars renum_clocks renum_states
    state_space);
                                      Impl3 ->
return
  (rename_check3 num_split dc broadcast bounds automata k l_0 s_0 formula m
    num_states num_actions renum_acts renum_vars renum_clocks renum_states
    state_space);
                                      Debug ->
rename_check_dbg num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  inv_renum_states inv_renum_vars inv_renum_clocks state_space;
                                    });
                                  let { tc = (-) (Prelude.const 0 ()) tb };
                                  _ <- Printing.printM ("Time for certificate checking: " ++
                 Prelude.show tc);
                                  (case check of {
                                    Renaming_Failed ->
                                      Printing.printM "Renaming failed";
                                    Preconds_Unsat ->
                                      Printing.printM "Preconditions were not met";
                                    Sat ->
                                      Printing.printM "Certificate was accepted";
                                    Unsat ->
                                      Printing.printM "Certificate was rejected";
                                  })
                                 };
                    })
                   };
           Error a -> print_errors a;
         });
    Error a -> print_errors a;
  });

parse_convert_run_print :: Bool -> String -> Heap.ST Heap.RealWorld ();
parse_convert_run_print dc s =
  (case binda (parse json s) convert of {
    Result
      (ids_to_names,
        (_, (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
      -> (case rename_state_space dc ids_to_names
                 (broadcast, (automata, bounds)) l_0 s_0 formula
           of {
           Result (Nothing, (_, (_, (_, _)))) -> return ();
           Result (Just r, (show_clk, (show_st, (_, _)))) ->
             do { 
               ra <- r;
               let { _ =
                 println
                   ("Number of discrete states: " ++ show_str (size_list ra))
                 };
               let { _ =
                 println
                   ("Size of passed list: " ++
                     show_str (sum_list (map (size_list . snd) ra)))
                 };
               let { n = size_list (list_of_set (clk_set automata)) };
               rb <- imp_map (\ (a, b) -> do { 
    ba <- imp_map (return . snd) b;
    bb <- filter_dbm_list n ba;
    return (a, bb)
   })
                       ra;
               let { _ =
                 println
                   ("Number of discrete states: " ++ show_str (size_list rb))
                 };
               let { _ =
                 println
                   ("Size of passed list after removing subsumed states: " ++
                     show_str (sum_list (map (size_list . snd) rb)))
                 };
               let { show_dbm =
                 (\ m ->
                   do { 
                     sa <- show_dbm_impl_all n show_clk
                             (\ x -> shows_prec_int zero_nat x []) m;
                     return
                       ([Char False False True True True True False False] ++
                         sa ++ [Char False True True True True True False
                                  False])
                    })
                 };
               _ <- imp_map
                      (\ (sa, xs) ->
                        let {
                          sb = show_st sa;
                        } in do { 
                               xsa <- imp_map show_dbm xs;
                               let { _ =
                                 println
                                   (implode
                                     (sb ++
                                       [Char False True False True True True
  False False,
 Char False False False False False True False False] ++
 shows_prec_list zero_nat xsa []))
                                 };
                               return ()
                              })
                      rb;
               return ()
              };
           Error es -> let {
                         _ = map println es;
                       } in return ();
         });
    Error es -> let {
                  _ = map println es;
                } in return ();
  });

}

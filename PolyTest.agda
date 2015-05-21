module PolyTest where

-- First up, explain problem
-- Show relevance of Δ

-- This should be familiar

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

data _==_ {X : Set} (x : X) : X -> Set where
  Refl : x == x

_∎ : ∀ {X} (x : X) -> x == x
x ∎ = Refl
_=[_⟩=_ : ∀ {X} (x : X) {y z} -> x == y -> y == z -> x == z
x =[ Refl ⟩= q   = q

-- with sym
_=⟨_]=_ : ∀ {X} (x : X) {y z} -> y == x -> y == z -> x == z
x =⟨ Refl ]= q   = q

infixr 2 _∎ _=[_⟩=_ _=⟨_]=_

-- more general than cong in Exercise1
_=$=_ : ∀ {S T : Set} {f g : S -> T} {x y} -> f == g -> x == y -> f x == g y
Refl =$= Refl = Refl

-- cong like Exercise1
_$=_ : ∀ {S T : Set} (f : S -> T) {x y} -> x == y -> f x == f y
f $= q = Refl =$= q

_=$_ : ∀ {S T : Set} {f g : S -> T} -> f == g -> (x : S) -> f x == g x
q =$ x = q =$= Refl

infixl 9 _=$=_ _$=_ _=$_

-- Syntax

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO Zero #-}
{-# BUILTIN SUC Succ #-}
infixr 5 _+_
infixr 6 _×_
infix 2 _==_

-- Straightforward functions

_+_ : Nat -> Nat -> Nat
Zero + y = y
Succ x + y = Succ (x + y)

_×_ : Nat -> Nat -> Nat
Zero × y = Zero
Succ x × y = x × y + y

_^_ : Nat -> Nat -> Nat
x ^ Zero = 1
x ^ Succ n = x ^ n × x

max : Nat -> Nat -> Nat
max Zero y = y
max (Succ x) Zero = Succ x
max (Succ x) (Succ y) = Succ (max x y)

_`max`_ : Nat -> Nat -> Nat
x `max` y = max x y

-- Now it gets interesting

-- data Poly : Nat -> Set where
--   K : Nat -> Poly 0
--   I :        Poly 1
--   _⊕_ : forall {l m} -> Poly l -> Poly m -> Poly (l `max` m)
--   _⊗_ : forall {l m} -> Poly l -> Poly m -> Poly (l + m)
-- 
-- eval : forall {n} -> Poly n -> Nat -> Nat
-- eval (K n) x = n
-- eval I x = x
-- eval (p ⊕ q) x = eval p x + eval p x
-- eval (p ⊗ q) x = eval p x × eval p x

-- Δ : forall {n} -> Poly (Succ n) -> Poly n
-- Δ p = ?








-- What now?
-- When combining prescriptive and descriptive indices, ensure both
-- are in constructor form. Exclude defined functions which yield
-- unification problems.







-- data Poly : Nat -> Set where
--   K : Nat -> Poly 0
--   I :        Poly 1
--   Plus  : forall {l m n} -> Poly l -> Poly m -> l `max` m == n -> Poly n
--   Times : forall {l m n} -> Poly l -> Poly m ->     l + m == n -> Poly n

-- eval : forall {n} -> Poly n -> Nat -> Nat
-- eval (K n) x = n
-- eval I x = x
-- eval (Plus p q _) x = eval p x + eval p x
-- eval (Times p q _) x = eval p x × eval p x

-- Δ : forall {n} -> Poly (Succ n) -> Poly n
-- Δ I = K 1
-- Δ (Plus p p₁ x) = {!Plus (Δ p) (Δ p₁) !}
-- Δ (Times p p₁ x) = {!!}





-- What happened to K?
-- What about Plus and Times?
-- Something is not right...

-- Be minimally prescriptive, not maximally descriptive

-- data Poly : Nat -> Set where
--   K :     forall {n}     -> Nat ->                            Poly n
--   I :     forall {n}     ->                                   Poly (Succ n)
--   _⊕_ :   forall {n}     -> Poly n -> Poly n ->               Poly n
--   times : forall {l m n} -> Poly l -> Poly m -> l + m == n -> Poly n

-- Δ : forall {n} -> Poly (Succ n) -> Poly n
-- Δ (K x) = K 0
-- Δ I = K 1
-- Δ (x ⊕ x₁) = Δ x ⊕ Δ x₁
-- Δ (times p q r) = {!times (Δ p) (\x -> r × (1 + x))
--                    ⊕ times p (Δ r)!}

data Add : Nat -> Nat -> Nat -> Set where
  ZeSu : forall {n} -> Add Zero n n
  SuZe : forall {n} -> Add n Zero n
  SuSu : forall {l m n} -> Add l m n -> Add (Succ l) (Succ m) (Succ (Succ n))

-- a good start is to write down the case analysis we need, relationally
data Poly : Nat -> Set where
  K :     forall {n}     -> Nat ->                            Poly n
  I :     forall {n}     ->                                   Poly (Succ n)
  Shift : forall {n}     -> Poly n ->                         Poly n
  _⊕_ :   forall {n}     -> Poly n -> Poly n ->               Poly n
  Times : forall {l m n} -> Poly l -> Poly m -> Add l m n -> Poly n

eval : forall {n} -> Poly n -> Nat -> Nat
eval (K n) x = n
eval I x = x
eval (Shift p) x = eval p (Succ x)
eval (p ⊕ q) x = eval p x + eval p x
eval (Times p q _) x = eval p x × eval p x

 -- not very interesting
sul : {l m n : Nat} -> Add l m n -> Add (Succ l) m (Succ n)
sul = {!!}

sur : {l m n : Nat} -> Add l m n -> Add l (Succ m) (Succ n)
sur = {!!}

Δ : forall {n} -> Poly (Succ n) -> Poly n
Δ (K x) = K 0
Δ I = K 1
Δ (x ⊕ x₁) = Δ x ⊕ Δ x₁
Δ (Shift p) = Shift (Δ p)
Δ (Times p q ZeSu) = Times (K (eval p 0))
                           (Δ q)
                           ZeSu
Δ (Times p q SuZe) = Times (Δ p)
                           (K (eval q 0))
                           SuZe
Δ (Times p q (SuSu r)) = Times (Δ p)
                               (Shift q)
                               (sur r)
                         ⊕
                         Times p
                               (Δ q)
                               (sul r)

add : (l m : Nat) -> Add l m (l + m)
add = {!!}

_⊗_ : {l m : Nat} -> Poly l -> Poly m -> Poly (l + m)
_⊗_ {l} {m} p r = Times p r (add l m)
infixr 6 _⊗_
infixr 5 _⊕_

I1 : Poly 1
I1 = I

K0 : Nat -> Poly 0
K0 = K

-- exponentation
_∘^_ : {m : Nat} -> Poly m -> (n : Nat) -> Poly (n × m)
p ∘^ Zero = K 1
p ∘^ Succ x = p ∘^ x ⊗ p
infixr 7 _∘^_

example₀ : Poly 2
example₀ = I1 ∘^ 2 ⊕ K0 2 ⊗ I ⊕ K 1

-- STATING THE TESTING PRINCIPLE

-- unit
record Unit : Set where constructor ⟨⟩
-- pair
record _,_ (S T : Set) : Set where
  constructor _,,_
  field fst : S; snd : T
open _,_ public

testEq : (k : Nat) {n : Nat} (p r : Poly n) -> Set
testEq Zero p r = Unit -- constant, so only test at, say, zero
testEq (Succ k) p r = (eval p 0 == eval r 0) , testEq k (Shift p) (Shift r)
-- k: number tests to perform

--testLem : (n : Nat) (p r : Poly n) ->
--  testEq (Succ n) p r -> (x : Nat) -> eval p x == eval r x
--testLem = {!!}

-- Let's prove for constant polynomial (degree at most 0)

kLem : (p : Poly 0) (x y : Nat) -> eval p x == eval p y
kLem (K x) x₁ y = Refl
kLem (Shift p) x y = kLem p (Succ x) (Succ y)
kLem (p ⊕ r) x y =
  eval (p ⊕ r) x       =[ Refl ⟩= 
  eval p x + eval p x  =[ {!_+_ $= kLem p x y =$= kLem r x y!} ⟩=
  eval p y + eval p y  =⟨ Refl ]=
  eval (p ⊕ r) y ∎
  
kLem (Times p p₁ x) x₁ y = {!!}


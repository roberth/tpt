
-- First up, explain problem
-- Show relevance of Δ

-- This should be familiar

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

data _==_ {X : Set} (x : X) : X -> Set where
  Refl : x == x

-- Boring syntax

{-# BUILTIN NATURAL Nat #-}
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

data Poly : Nat -> Set where
  K :     forall {n}     -> Nat ->                            Poly n
  I :     forall {n}     ->                                   Poly (Succ n)
  _⊕_ :   forall {n}     -> Poly n -> Poly n ->               Poly n
  times : forall {l m n} -> Poly l -> Poly m -> l + m == n -> Poly n

Δ : forall {n} -> Poly (Succ n) -> Poly n
Δ (K x) = K 0
Δ I = K 1
Δ (x ⊕ x₁) = Δ x ⊕ Δ x₁
Δ (times p q r) = {!times (Δ p) (\x -> r × (1 + x))
                   ⊕ times p (Δ r)!}

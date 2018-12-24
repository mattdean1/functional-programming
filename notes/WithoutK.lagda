
  ========================
  From equalities to paths
  ========================


In previous lectures, you have seen the data type

data _≡_ {X : Set} : X → X → Set where
 refl : (x : X) → x ≡ x

can be interpreted as 'equality' of elements of a type X. Indeed,
elements of this type behave like equalities in several important
respects - see later.

If we modify Agda a tiny bit - by setting a flag - then the behaviour
of this type _≡_ is changed and a *different* interpretation seems
more suitable.  In this lecture, we will learn about the effects of
the flag to the Agda type checker, and about the new interpretation
motivated by these effects.

This new interpretation has given rise to an entire new field of
study, called Homotopy Type Theory. Based on this interpretation, a
new foundation of mathematics has been designed by Vladimir Voevodsky
(1966-2017), called "Univalent Foundations".


In this lecture, I will give a very brief overview of Univalent
Foundations.  The overview is necessarily incomplete. I will give
pointers to further material in the course of the lecture, in the form
"[Section X.Y]". Such a pointer refers to Section X.Y of the book

Homotopy Type Theory: Univalent Foundations of Mathematics

which is available under a free license from

https://homotopytypetheory.org/book/ .


Before learning about the new interpretation, let's take a look again
at the "old", traditional, interpretation:


Recap: the equality type
========================

Previously, in Martín Escardó's lecture, you have seen the equality
type defined as follows:

--\begin{code}

data _≡_ {X : Set} : X → X → Set where
 refl : (x : X) → x ≡ x

--We think of inhabitants/elements of this type as proofs
--of equality;  e : x ≡ y is a proof that x is equal to y.

--Martín then showed that functions respect equality:

cong : {X Y : Set} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong {X} {Y} f (refl x) = refl {Y} (f x)

--One can also show that equality is symmetric and transitive:

sym : {X : Set} {x y : X} → x ≡ y → y ≡ x
sym (refl x) = refl x

trans : {X : Set} {x y z : X} 
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans (refl x) p = p

--Since the equality type is a type, there is also the type of
--equalities between two "parallel" equalities (that is, with same
--start and end point), but that type is not very interesting: any two
--equalities are equal themselves

eq-eq : {X : Set} {x y : X}
  → (p q : x ≡ y)
  → p ≡ q
eq-eq (refl x) (refl _) = refl (refl x)  

--\end{code}



The type of paths
=================

In this lecture, we are going to see a different "mode" of Agda, where
the equality type has interesting structure. Indeed, the behaviour of
this "equality" will be so different from equality that we will even
give it a different name.

Instead of thinking of e : x ≡ y in X as an equality, we think of it
as a "path" from x to y in the "space" X.

The question whether two "parallel" equalities are themselves equal
(see eq-eq above) then becomes the question whether two paths from x
to y can be continuously deformed into one another.  Depending on the
space X, this may or may not be the case.

To reflect the change in the way we think about the "equality" type,
we redefine it using a different notation.

\begin{code}

--this flag changes the behaviour of Agda with respect to the equality
--type; we need to activate the flag to switch to "path" mode


{-# OPTIONS --without-K #-}


module WithoutK where

data _⟿_ {X : Set} : X → X → Set where
  Id-Path : (x : X) → x ⟿ x

\end{code}

[Section 1.12]


Paths between paths
===================


With the --without-K flag unset, the path type ⟿ behaves exactly like
the equality type ≡.  However, the following definitions will fail
once we activate
--without-K

--\begin{code}

path-path : {X : Set} {x y : X}
  → (p q : x ⟿ y)
  → p ⟿ q
path-path (Id-Path x) (Id-Path _) = Id-Path (Id-Path x)  

K : {X : Set}
  → (P : (x : X) → x ⟿ x → Set)
  → ((x : X) → P x (Id-Path _ ))
  → (x : X) (p : x ⟿ x)
  → P x p
K P f x (Id-Path _) = f x

--\end{code}

Compare K above with J below. J continues working with
--without-K

\begin{code}

J : {X : Set}
  → (P : (x y : X) → x ⟿ y → Set)
  → ((x : X) → P x x (Id-Path x))
  → (x y : X) (p : x ⟿ y) → P x y p
J A f _ _ (Id-Path x) = f x

\end{code}

The difference is that in J, the starting point x is different from
the end point y, so that one can "move the endpoint y" when
contracting the path.

The situation is very much like with a vacuum cleaner with an
automatic contraction for the electricity cable:

   paths            vacuuming
-------------------------------
   x                vacuum cleaner
   y                plug of the cleaner
   p : x ⟿ y       cable between the vacuum cleaner and the plug


Pattern matching on a path from x to y then means that we can assume
that this cable was obtained by pulling the plug out of the vacuum
cleaner.

That means that we can deform any path from x to y into the the
constant path on x:


\begin{code}

data Σ {X : Set} (T : X → Set) : Set where
  _,_ : (x : X) (y : T x) → Σ T

ConeContraction : {X : Set} (x : X)
  → (y : X) (q : x ⟿ y)
  → (y , q) ⟿ (x , (Id-Path x))
ConeContraction x _ (Id-Path .x)  = Id-Path (x , Id-Path x)

\end{code}


Operations on paths
===================

See also [Section 2.1].

We have operations on paths analogous to those on equalities:
- symmetry becomes path inversion (going a path backwards)
- transitivity becomes concatenation of paths

These operations are analogous to reversal and concatentation
of lists or vectors.

\begin{code}

inv : {X : Set}
  → {a b : X}
  → a ⟿ b → b ⟿ a
inv (Id-Path a) = Id-Path a

_·_ : {X : Set}
  → {a b c : X}
  → a ⟿ b
  → b ⟿ c
  → a ⟿ c
Id-Path a · p = p

\end{code}


Similar to the vector operations (see Martín's lecture), we can
show that thes operations on paths satisfy some laws reminiscent
of the group laws:
- associativity
- left and right neutrality
- inverse

Actually, since these laws hold up to a "path between paths",
we call them "(higher) groupoid laws":

\begin{code}

·-assoc : {X : Set} {a b c d : X}
  → (p : a ⟿ b)
  → (q : b ⟿ c)
  → (r : c ⟿ d)
  → (p · (q · r)) ⟿ ((p · q) · r)
·-assoc (Id-Path a) q r = Id-Path (q · r)

·Id-Path : {X : Set} {a b : X}
  → (p : a ⟿ b)
  → (p · Id-Path b) ⟿ p
·Id-Path (Id-Path a) = Id-Path (Id-Path a)

Id-Path· : {X : Set} {a b : X}
  → (p : a ⟿ b)
  → (Id-Path a · p) ⟿ p
Id-Path· (Id-Path a) = Id-Path (Id-Path a)

inv· : {X : Set}
  → {a b : X}
  → (p : a ⟿ b)
  → ((inv p) · p) ⟿ Id-Path b
inv· (Id-Path x) = Id-Path (Id-Path x)


\end{code}



More operations involving paths
===============================


A function f : X → Y not only maps points of X to
points of Y; it also maps paths in X to paths in Y:

\begin{code}

function-on-paths : {X Y : Set}
  → (f : X → Y)
  → {a b : X}
  → a ⟿ b
  → f a ⟿ f b
function-on-paths f (Id-Path x) = Id-Path (f x)

\end{code}

Given a predicate T : X → Set on X, it can be
transported along a path:

\begin{code}

transport : {X : Set} (T : X → Set)
  → {a b : X}
  → (e : a ⟿ b )
  → T a → T b
transport T (Id-Path _) p = p

\end{code}



Propositions
============

See also [Section 3.3].

In one of the first lectures, you have learned about the
"propositions-as-types" paradigm. There, you have learned that any
type can be considered a proposition, and its elements are the proofs
of that proposition. In particular, you learned about ⊤ ⊥ ∧ ∨ (and
Σ?).

In Univalent Foundations, only those types that satisfy a certain
condition will be called "proposition":

\begin{code}

is-a-proposition : Set → Set
is-a-proposition X = (a b : X) → a ⟿ b

\end{code}

A proposition is hence a type in which any two points are connected by
a path. Reading ⟿ as ≡ , it means that a proposition has at most one
element.

Here are some examples of types that are propositions:

\begin{code}

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

data _∧_ (A B : Set) : Set where
  _,,_ : A → B → A ∧ B

∧-Path : {A B : Set}
  → {a a' : A}
  → {b b' : B}
  → (a ⟿ a') → (b ⟿ b')
  → (a ,, b) ⟿ (a' ,, b')
∧-Path (Id-Path a) (Id-Path b) = Id-Path (a ,, b)


is-a-proposition-⊤ : is-a-proposition ⊤ 
is-a-proposition-⊤ tt tt = Id-Path tt

is-a-proposition-⊥ : is-a-proposition ⊥
is-a-proposition-⊥ a = λ ()

is-a-proposition_∧ : (X Y : Set)
  → is-a-proposition X
  → is-a-proposition Y
  → is-a-proposition (X ∧ Y)
is-a-proposition X ∧ Y pX pY (a ,, b) (a' ,, b') = goal
  where
    p1 : a ⟿ a'
    p1 = pX a a'
    p2 : b ⟿ b'
    p2 = pY b b'
    goal : (a ,, b) ⟿ (a' ,, b')
    goal = ∧-Path p1 p2

\end{code}

What about X ∨ Y ?

Even when X and Y are propositions, X ∨ Y does not need to be one.
Consider ⊤ ∨ ⊤:

\begin{code}

data _∨_ (X Y : Set) : Set where
  inl : X → X ∨ Y
  inr : Y → X ∨ Y

no-path-inl-inr : {X Y : Set}
  {a : X} {b : Y}
  → inl a ⟿ inr b → ⊥
no-path-inl-inr ()

not-a-proposition-⊤∨⊤ : is-a-proposition (⊤ ∨ ⊤) → ⊥
not-a-proposition-⊤∨⊤  x = goal
  where
    impossible-path : inl tt ⟿ inr tt
    impossible-path = x (inl tt) (inr tt)
    goal : ⊥
    goal = no-path-inl-inr impossible-path
    
\end{code}


To fix the problem that X ∨ Y is not a proposition, an additional type
constructor is added to type theory in Univalent Foundations: the
*propositional truncation*.

This type constructor associates to any type X another type, written
∥X∥, with the following structure:

1. ∥X∥ is a proposition
2. There is a function X → ∥X∥
3. Any map X → B with B a proposition factors via X → ∥X∥.

Intuitively, ∥X∥ is isomorphic to ⊤ if X is inhabited, and isomorphic
to ⊥ if X is empty.



Levels of types
===============

See also [Section 7].

In this section, we look at conditions that are analogous to that of
being a proposition.

Recall that a type X is a proposition if there is a path between any
two points of X. For reasons that will become clear later, we also say
that a type that is a proposition is *of level 1*.


We can also look at the following, similar, condition:

We say that "X is of level 2" if there is a path between any two
(parallel) paths between any two points of X.
Intuitively, this means that the space X has no "holes".

\begin{code}

is-of-level-2 : Set →  Set
is-of-level-2 X = (a b : X) (p q : a ⟿ b) → p ⟿ q

\end{code}

As we have seen, in the mode with K, one could show that there is a
path between any two paths between any x and y of a type X.  That
means that *with K, any type is of level 2*.

Without K, we can not show that every type is of level 2. But, with
the type theory that I have presented so far, we can also not
construct a type that is not of level 2. Indeed, defining a type that
is not of level 2 requires an additional axiom (postulate).


Examples of types of level 2:

1) Any type of level 1 is also of level 2.
2) The type bool is of level 2, but not of level 1.
3) The type nat of natural numbers is of level 2.

That is, a type is of level 2 if "there is a path between any
two (parallel) paths".

We can show that the booleans are of level 2, but not of level 1:

\begin{code}

data bool : Set where
  true : bool
  false : bool

bool-is-of-level-2 : is-of-level-2 bool
bool-is-of-level-2 b .b (Id-Path .b) (Id-Path .b) = Id-Path (Id-Path b)

not-bool-is-a-proposition : is-a-proposition bool → ⊥
not-bool-is-a-proposition x = goal
  where
    T : bool → Set
    T true = ⊤
    T false = ⊥
    f : T true → T false
    f = transport T (x true false)
    goal : ⊥
    goal = f tt

\end{code}


We can continue giving analogous definitions for any level n:

Say that the type  X is
- of level 1 if there is a path between any two points
- of level 2 if there is a path between any two paths between points
- of level 3 if there is a path between any two paths between any two paths between points
- of level 4 if......

We are missing level 0! We say that X is of level 0 if
- it has a distinguished element; and
- any other element has a path to that element

\begin{code}

data nat : Set where
  zero : nat
  succ : nat → nat

is-singleton : Set → Set
is-singleton X = Σ \(a : X) → (b : X) → a ⟿ b

is-of-level : (n : nat) → Set → Set
is-of-level zero X = is-singleton X
is-of-level (succ n) X = (a b : X) → is-of-level n (a ⟿ b) 

\end{code}

Showing that
`is-of-level 1`
is actually the same as
`is-a-proposition`
involves a small trick. Try at home!?

It can be shown that type constructors "are closed under levels":

* The cartesian product X × Y is of level n if X and Y are of level n.

* The function type X → Y is of level n if the target type Y is.

* The Sigma type ∑ \(x : X) → T x is of level n if X is and all (T x) are.

* The product type (x : X) → T x is of level n if all (T x) are.

* The type of lists over A is of level n if A is.

* ...


Actually, not all of these are provable without an axiom (a postulate)
that we will add:
the axiom of "function extensionality" is required to show that the level
is stable under product and function types.


Function extensionality
=======================

See also [Section 2.9].

Stating this axiom requires some work. If we think in terms of equality,
the axiom says that two functions are equal if they are pointwise equal:

postulate
  funext : (X Y : Set) (f g : X → Y) → ( (x : X) → f x ≡ g x ) → f ≡ g

In terms of paths, however, this is not the right formulation of this axiom.
The above postulate, expressed with paths, would give us *some* path f ⟿ g
from a family of paths (x : X) → f x ⟿ g x,
but we would not know how to reason about this path.

What we want to say instead is that the type of paths  f ⟿ g is
"the same" as the type of families ( (a : X) → f x ⟿ g x ).
In other words, we should say that these two types are *isomorphic*.

However, we do not want just any isomorphism between those two types;
we want an isomorphism that maps

Id-Path f   ---------->   \(x : X) → Id-Path (f x)

We first define a map from paths between functions to families of pointwise
paths:

\begin{code}

to-prod-paths : {X : Set} {T : X → Set}
  {f g : (a : X) → T a}
  → f ⟿ g → (a : X) → f a ⟿ g a
to-prod-paths (Id-Path f) a = Id-Path (f a)

\end{code}


Our new "function extensionality axiom should say that, for
any f, g : X → Y,

to-prod-paths {f} {g}

is an isomorphism.

We say that a function f : X → Y is an isomorphism by saying that the preimage
of any b : Y is a singleton.

\begin{code}

fiber : {X Y : Set} → (X → Y) → Y → Set
fiber f b = Σ \a → (f a) ⟿  b

is-iso : {X Y : Set} (f : X → Y) → Set
is-iso {X} {Y} f = (b : Y) → is-singleton (fiber f b)

iso  : Set → Set → Set
iso X Y = Σ λ (f : X → Y) →  is-iso f

postulate
  path-funext : {X : Set} {Y : X → Set} (f g : (a : X) → Y a)
    → is-iso (to-prod-paths {X} {Y} {f} {g})

\end{code}


With this postulate path-funext, we can show the stability of levels
under the aforementioned constructions.




Universes and the univalence axiom
==================================

See also [Section 2.10].


Unfortunately, I have not learned enough about Agda in time to teach
you about universes in Agda. As a consequence, at the end of this
section, there is some code that does not compile.

About universes: see blackboard explanation.

\begin{code}

id : (X : Set) → X → X
id X x = x

singleton-type : {X : Set} → X → Set
singleton-type x = Σ \y → y ⟿ x

η : {X : Set} (x : X) → singleton-type x
η x = (x , Id-Path x)

singleton-types-are-singletons : {X : Set} (x : X) → is-singleton(singleton-type x)
singleton-types-are-singletons {X} = h
 where
  A : (y x : X) → y ⟿ x → Set
  A y x p = (η x) ⟿ (y , p)
  f : (x : X) → A x x (Id-Path x)
  f x = Id-Path (η x)
  φ : (y x : X) (p : y ⟿ x) → (η x) ⟿ (y , p)
  φ = J A f
  g : (x : X) (σ : singleton-type x) → (η x) ⟿ σ
  g x (y , p) = φ y x p
  h : (x : X) → Σ \(c : singleton-type x) → (σ : singleton-type x) → c ⟿ σ
  h x = (η x , g x)


idIsEquiv : (X : Set) → is-iso(id X)
idIsEquiv X = g
 where
  g : (x : X) → is-singleton (fiber (id X) x)
  g = singleton-types-are-singletons

\end{code}



The following results in a universe problem, and hence does not
compile.  The problem is that the type of paths is defined for types
that are elements of "Set", not for "Set" itself.

Put differently, given X : Set and x and y in X, we have defined
x ⟿_X y ,
where we make the type X explicit. But we have not defined
X ⟿_Set Y yet.

The following code is a sketch of what the univalence axiom looks like
naïvely.

--\begin{code}

IdToEq : (X Y : Set) → X ⟿ Y → iso X Y
IdToEq = J A f
 where
  A : (X Y : Set) → X ⟿ Y → Set
  A X Y p = iso X Y
  f : (X : Set) → A X X (Id-Path X)
  f X = (id X , idIsEquiv X)

isUnivalent : Set
isUnivalent = (X Y : Set) → is-iso (IdToEq X Y)

--\end{code}

For a proper formulation of the Univalence Axiom, see Martin Escardo's
article "A self-contained, brief and complete formulation of
Voevodsky's Univalence Axiom" and the accompanying Agda file at
https://arxiv.org/abs/1803.02294




























Paths in cartesian products
===========================

As an example, we consider the cartesian product type:

\begin{code}

_×_ : (A B : Set) → Set
A × B = Σ \(a : A) → B

pr1 : {A B : Set}
  → A × B → A
pr1 (a , b) = a

pr2 : {A B : Set}
  → A × B → B
pr2 (a , b) = b

\end{code}


We want to show that the type of paths between pairs (a, b) and (c, d)
is isomorphic to the type of pairs of paths from a to c and from b to d.
We first define maps in both directions:

\begin{code}
dirprod-eq-pr1 : {A B : Set}
  → (s t : A × B)
  → s ⟿ t → pr1 s ⟿ pr1 t
dirprod-eq-pr1 s t p = function-on-paths pr1 p

dirprod-eq-pr2 : {A B : Set}
  → (s t : A × B)
  → s ⟿ t → pr2 s ⟿ pr2 t
dirprod-eq-pr2 s t p = function-on-paths pr2 p

dirprod-eq : {A B : Set}
  → {a a' : A}
  → {b b' : B}
  → (a ⟿ a') × (b ⟿ b')
  → (a , b) ⟿ (a' , b')
dirprod-eq ((Id-Path a) , (Id-Path b)) = Id-Path (a , b)

\end{code}
























Given a type X and its tower of paths types
⟿_A, ⟿_{⟿_A}, etc,
we can ask if that tower ever becomes 



How "interesting" is the



Characterizing the path type of a type
======================================






fiber : {X Y : Set} → (X → Y) → Y → Set
fiber f y = Σ \x → (f x) ⟿  y

isEquiv : {X : Set} {Y : Set} → (X → Y) → Set
isEquiv f = (y : _) → isSingleton(fiber f y)

Eq : Set → Set → Set
Eq X Y = Σ \(f : X → Y) → isEquiv f





-}




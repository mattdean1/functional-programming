

data List (A : Set) : Set where
  nil   : List A
  _::_  : (x : A) → List A → List A

_++_ : ∀ {A} → List A → List A → List A
nil ++ l2 = l2
(x :: l1) ++ l2 = x :: (l1 ++ l2)

[_] : ∀ {A} → A → List A
[ x ] = x :: nil

reverse : ∀ {A} → List A → List A
reverse nil = nil
reverse (x :: xs) = (reverse xs) ++ [ x ]

rev-append : ∀ {A} → List A → List A → List A
rev-append nil ys = ys
rev-append (x :: xs) ys = rev-append xs (x :: ys)

fast-reverse : ∀ {A} → List A → List A
fast-reverse l = rev-append l nil



data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x
infix 0 _≡_

≡-cong : {A : Set} → {a b : A} → (f : A → A) →  a ≡ b → f a ≡ f b
≡-cong f (refl x) = refl (f x)

≡-trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans (refl .x) (refl x) = refl x

≡-sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
≡-sym (refl a) = refl a




--appending nil is a noop
appnil : ∀ {A} → (l : List A) → l ++ nil ≡ l
appnil nil = refl nil
appnil (x :: l) = ≡-cong (λ list → x :: list) (appnil l)

-- Proof that reverse is an involution (is its own inverse)
rev-inv : {A : Set} → (l : List A) → l ≡ reverse (reverse l)
rev-inv nil = refl nil
rev-inv (x :: l) = ≡-trans (≡-cong (λ q → x :: q) (rev-inv l)) (lemma x (reverse l))
  where
  lemma : {A : Set} → (x : A) → (l : List A) → x :: reverse l ≡ reverse (l ++ [ x ])
  lemma x nil = refl (x :: nil)
  lemma x (y :: ys) = ≡-cong (λ q → q ++ [ y ]) (lemma x ys)

-- Proof that fast-reverse is equivalent to reverse
r-fr : {A : Set} → (l : List A) → reverse l ≡ fast-reverse l
r-fr nil = refl nil
r-fr (x :: xs) = lemma x xs
  where
  lemma : {A : Set} → (x : A) (xs : List A) → reverse xs ++ [ x ] ≡ rev-append xs [ x ]
  lemma a nil = refl [ a ]
  lemma a (x :: xs) = ≡-trans (≡-cong (λ q → q ++ [ a ]) (lemma x xs)) (≡-sym (lem2 xs [ x ] [ a ]))
    where
    lem2 : {A : Set} → (l1 l2 l3 : List A) → rev-append l1 (l2 ++ l3) ≡ (rev-append l1 l2) ++ l3
    lem2 nil l2 l3 = refl (l2 ++ l3)
    lem2 (x :: l1) l2 l3 = lem2 l1 (x :: l2) l3

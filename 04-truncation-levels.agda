{-# OPTIONS --without-K --exact-split #-}

module 04-truncation-levels where

open import 03-contractible-types public

is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

is-prop-map : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-prop-map f = (b : _) → is-prop (fib f b)

is-subtype : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
is-subtype B = (x : _) → is-prop (B x)

UU-Prop :
  (l : Level) → UU (lsuc l)
UU-Prop l = Σ (UU l) is-prop

type-Prop :
  {l : Level} → UU-Prop l → UU l
type-Prop P = pr1 P

is-prop-type-Prop :
  {l : Level} (P : UU-Prop l) → is-prop (type-Prop P)
is-prop-type-Prop P = pr2 P

all-elements-equal :
  {i : Level} (A : UU i) → UU i
all-elements-equal A = (x y : A) → Id x y

is-prop-all-elements-equal :
  {i : Level} {A : UU i} → all-elements-equal A → is-prop A
is-prop-all-elements-equal {i} {A} H x y =
  pair
    ( (inv (H x x)) ∙ (H x y))
    ( λ { refl → left-inv (H x x)})

is-proof-irrelevant :
  {l1 : Level} → UU l1 → UU l1
is-proof-irrelevant A = A → is-contr A

is-subterminal :
  {l1 : Level} → UU l1 → UU l1
is-subterminal A = is-emb (terminal-map {A = A})

eq-is-prop' :
  {i : Level} {A : UU i} → is-prop A → all-elements-equal A
eq-is-prop' H x y = pr1 (H x y)

eq-is-prop :
  {i : Level} {A : UU i} → is-prop A → {x y : A} → Id x y
eq-is-prop H {x} {y} = eq-is-prop' H x y

is-proof-irrelevant-all-elements-equal :
  {l1 : Level} {A : UU l1} → all-elements-equal A → is-proof-irrelevant A
is-proof-irrelevant-all-elements-equal H a = pair a (H a)

is-proof-irrelevant-is-prop :
  {i : Level} {A : UU i} → is-prop A → is-proof-irrelevant A
is-proof-irrelevant-is-prop =
  is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

is-prop-is-proof-irrelevant :
  {i : Level} {A : UU i} → is-proof-irrelevant A → is-prop A
is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

eq-is-proof-irrelevant :
  {l1 : Level} {A : UU l1} → is-proof-irrelevant A → all-elements-equal A
eq-is-proof-irrelevant H =
  eq-is-prop' (is-prop-is-proof-irrelevant H)

is-equiv-is-prop : {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
  is-prop B → {f : A → B} → (B → A) → is-equiv f
is-equiv-is-prop is-prop-A is-prop-B {f} g =
  is-equiv-has-inverse
    ( g)
    ( λ y → center (is-prop-B (f (g y)) y))
    ( λ x → center (is-prop-A (g (f x)) x))

equiv-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A → is-prop B →
  (A → B) → (B → A) → A ≃ B
equiv-prop is-prop-A is-prop-B f g =
  pair f (is-equiv-is-prop is-prop-A is-prop-B g)

is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

UU-Set :
  (i : Level) → UU (lsuc i)
UU-Set i = Σ (UU i) is-set

type-Set :
  {l : Level} → UU-Set l → UU l
type-Set X = pr1 X

is-set-type-Set :
  {l : Level} (X : UU-Set l) → is-set (type-Set X)
is-set-type-Set X = pr2 X

Id-Prop :
  {l : Level} (X : UU-Set l) (x y : type-Set X) → UU-Prop l
Id-Prop X x y = pair (Id x y) (is-set-type-Set X x y)

data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

is-trunc-map :
  {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} → (A → B) → UU (i ⊔ j)
is-trunc-map k f = (y : _) → is-trunc k (fib f y)

trunc-map : {i j : Level} (k : 𝕋) (A : UU i) (B : UU j) → UU (i ⊔ j)
trunc-map k A B = Σ (A → B) (is-trunc-map k)

UU-Truncated-Type : 𝕋 → (l : Level) → UU (lsuc l)
UU-Truncated-Type k l = Σ (UU l) (is-trunc k)

type-Truncated-Type :
  {k : 𝕋} {l : Level} → UU-Truncated-Type k l → UU l
type-Truncated-Type = pr1

is-trunc-type-Truncated-Type :
  {k : 𝕋} {l : Level} (A : UU-Truncated-Type k l) →
  is-trunc k (type-Truncated-Type A)
is-trunc-type-Truncated-Type = pr2

is-trunc-is-equiv :
  {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
  is-trunc k B → is-trunc k A
is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
  is-contr-is-equiv B f is-equiv-f H
is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
  is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y})
    ( is-emb-is-equiv is-equiv-f x y) (H (f x) (f y))
                                                  
is-set-is-equiv :
  {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
  is-set B → is-set A
is-set-is-equiv = is-trunc-is-equiv zero-𝕋

is-trunc-equiv :
  {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
  is-trunc k B → is-trunc k A
is-trunc-equiv k B (pair f is-equiv-f) =
  is-trunc-is-equiv k B f is-equiv-f

is-set-equiv :
  {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
  is-set B → is-set A
is-set-equiv = is-trunc-equiv zero-𝕋

is-trunc-is-equiv' :
  {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
  is-equiv f → is-trunc k A → is-trunc k B
is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
  is-trunc-is-equiv k A
    ( map-inv-is-equiv is-equiv-f)
    ( is-equiv-map-inv-is-equiv is-equiv-f)
    ( is-trunc-A)

is-set-is-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
  is-set A → is-set B
is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

is-trunc-equiv' :
  {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
  is-trunc k A → is-trunc k B
is-trunc-equiv' k A (pair f is-equiv-f) =
  is-trunc-is-equiv' k A f is-equiv-f

is-set-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
  is-set A → is-set B
is-set-equiv' = is-trunc-equiv' zero-𝕋

is-trunc-Σ : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
is-trunc-Σ neg-two-𝕋 is-trunc-A is-trunc-B =
  is-contr-Σ is-trunc-A is-trunc-B
is-trunc-Σ (succ-𝕋 k) {B = B} is-trunc-A is-trunc-B s t =
  is-trunc-is-equiv k
    ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
    ( pair-eq-Σ)
    ( is-equiv-pair-eq-Σ s t)
    ( is-trunc-Σ k
      ( is-trunc-A (pr1 s) (pr1 t))
      ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

is-trunc-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k A → is-trunc k B → is-trunc k (A × B)
is-trunc-prod k is-trunc-A is-trunc-B =
  is-trunc-Σ k is-trunc-A (λ x → is-trunc-B)

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') =
  is-trunc-equiv k
    ( Eq-prod (pair a b) (pair a' b'))
    ( equiv-pair-eq (pair a b) (pair a' b'))
    ( is-trunc-prod k (f b a a') (g a b b'))

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-prod A B H
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-prod k {A = Id a a'} {B = Id b b}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a' b))
      ( equiv-pair-eq (pair a b) (pair a' b))
      ( H (pair a b) (pair a' b)))
    ( refl)

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-prod A B H
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-prod k {A = Id a a} {B = Id b b'}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a b'))
      ( equiv-pair-eq (pair a b) (pair a b'))
      ( H (pair a b) (pair a b')))
    ( refl)

is-prop-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop A → is-prop B → is-prop (A × B)
is-prop-prod = is-trunc-prod neg-one-𝕋

prod-Prop : {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
prod-Prop P Q =
  pair
    ( type-Prop P × type-Prop Q)
    ( is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q))

is-set-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set A → is-set B → is-set (A × B)
is-set-prod = is-trunc-prod zero-𝕋

is-prop-is-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) (E : is-equiv f) →
  is-prop B → is-prop A
is-prop-is-equiv B f E H x y =
  is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv E x y) (H (f x) (f y))

is-prop-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) → is-prop B → is-prop A
is-prop-equiv B (pair f is-equiv-f) = is-prop-is-equiv B f is-equiv-f

is-prop-is-equiv' :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) (E : is-equiv f) →
  is-prop A → is-prop B
is-prop-is-equiv' A f E H =
  is-prop-is-equiv _ (map-inv-is-equiv E) (is-equiv-map-inv-is-equiv E) H

is-prop-equiv' :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) → is-prop A → is-prop B
is-prop-equiv' A (pair f is-equiv-f) = is-prop-is-equiv' A f is-equiv-f

equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) ≃ Σ (Σ A C) (λ t → B (pr1 t))
equiv-double-structure {A = A} B C =
  ( ( inv-assoc-Σ A C (λ t → B (pr1 t))) ∘e
    ( equiv-tot (λ x → commutative-prod))) ∘e
  ( assoc-Σ A B (λ t → C (pr1 t)))

map-equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) → Σ (Σ A C) (λ t → B (pr1 t))
map-equiv-double-structure B C = map-equiv (equiv-double-structure B C)

is-equiv-map-equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  is-equiv (map-equiv-double-structure B C)
is-equiv-map-equiv-double-structure B C =
  is-equiv-map-equiv (equiv-double-structure B C)
  
is-contr-total-Eq-substructure :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : A → UU l3} →
  is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
  is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
is-contr-total-Eq-substructure {A = A} {B} {P}
  is-contr-AB is-subtype-P a b p =
  is-contr-equiv
    ( Σ (Σ A B) (λ t → P (pr1 t)))
    ( equiv-double-structure P B)
    ( is-contr-equiv
      ( P a)
      ( left-unit-law-Σ-is-contr
        ( is-contr-AB)
        ( pair a b))
      ( is-proof-irrelevant-is-prop (is-subtype-P a) p))

Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-subtype B →
  (Σ A B) → (Σ A B) → UU l1
Eq-total-subtype is-subtype-B p p' = Id (pr1 p) (pr1 p') 

reflexive-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → Eq-total-subtype is-subtype-B p p
reflexive-Eq-total-subtype is-subtype-B (pair x y) = refl

Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → Id p p' → Eq-total-subtype is-subtype-B p p'
Eq-total-subtype-eq is-subtype-B p .p refl =
  reflexive-Eq-total-subtype is-subtype-B p

is-contr-total-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype is-subtype-B p))
is-contr-total-Eq-total-subtype is-subtype-B (pair x y) =
  is-contr-total-Eq-substructure
    ( is-contr-total-path x)
    ( is-subtype-B)
    x refl y

is-equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → is-equiv (Eq-total-subtype-eq is-subtype-B p p')
is-equiv-Eq-total-subtype-eq is-subtype-B p =
  fundamental-theorem-id p
    ( reflexive-Eq-total-subtype is-subtype-B p)
    ( is-contr-total-Eq-total-subtype is-subtype-B p)
    ( Eq-total-subtype-eq is-subtype-B p)

equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype is-subtype-B p p')
equiv-Eq-total-subtype-eq is-subtype-B p p' =
  pair
    ( Eq-total-subtype-eq is-subtype-B p p')
    ( is-equiv-Eq-total-subtype-eq is-subtype-B p p')

eq-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  {p p' : Σ A B} → Eq-total-subtype is-subtype-B p p' → Id p p'
eq-subtype is-subtype-B {p} {p'} =
  map-inv-is-equiv (is-equiv-Eq-total-subtype-eq is-subtype-B p p')

is-trunc-succ-is-trunc :
  (k : 𝕋) {i : Level} {A : UU i} →
  is-trunc k A → is-trunc (succ-𝕋 k) A
is-trunc-succ-is-trunc neg-two-𝕋 H =
  is-prop-is-contr H
is-trunc-succ-is-trunc (succ-𝕋 k) H x y =
  is-trunc-succ-is-trunc k (H x y)

is-set-is-prop :
  {l : Level} {P : UU l} → is-prop P → is-set P
is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

is-trunc-map-succ-is-trunc-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
  is-trunc-succ-is-trunc k (is-trunc-f b)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU-Truncated-Type (succ-𝕋 k) l
truncated-type-succ-Truncated-Type k A =
  pair
    ( type-Truncated-Type A)
    ( is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A))

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P

is-trunc-is-contr :
  { l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
is-trunc-is-contr (succ-𝕋 k) is-contr-A =
  is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)

is-set-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-set A
is-set-is-contr = is-trunc-is-contr zero-𝕋

is-trunc-is-prop :
  { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

is-trunc-succ-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
is-trunc-succ-empty k = ind-empty

is-trunc-is-empty :
  {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))

is-trunc-coprod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
  is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inl y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inl x) (inl y))
    ( equiv-Eq-eq-coprod A B (inl x) (inl y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( Id x y)
      ( equiv-raise _ (Id x y))
      ( is-trunc-A x y))
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inr y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inl x) (inr y))
    ( equiv-Eq-eq-coprod A B (inl x) (inr y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( empty)
      ( equiv-raise _ empty)
      ( is-trunc-succ-empty k))
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inl y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inr x) (inl y))
    ( equiv-Eq-eq-coprod A B (inr x) (inl y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( empty)
      ( equiv-raise _ empty)
      ( is-trunc-succ-empty k))
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inr y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inr x) (inr y))
    ( equiv-Eq-eq-coprod A B (inr x) (inr y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( Id x y)
      ( equiv-raise _ (Id x y))
      ( is-trunc-B x y))

is-set-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set A → is-set B → is-set (coprod A B)
is-set-coprod = is-trunc-coprod neg-two-𝕋

coprod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
coprod-Set (pair A is-set-A) (pair B is-set-B) =
  pair (coprod A B) (is-set-coprod is-set-A is-set-B)

is-prop-unit : is-prop unit
is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
unit-Prop = pair unit is-prop-unit

is-prop-empty : is-prop empty
is-prop-empty ()

empty-Prop : UU-Prop lzero
empty-Prop = pair empty is-prop-empty

is-set-unit : is-set unit
is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

unit-Set : UU-Set lzero
unit-Set = pair unit is-set-unit

is-set-empty : is-set empty
is-set-empty ()

empty-Set : UU-Set lzero
empty-Set = pair empty is-set-empty

is-set-Fin :
  (n : ℕ) → is-set (Fin n)
is-set-Fin zero-ℕ = is-set-empty
is-set-Fin (succ-ℕ n) =
  is-set-coprod (is-set-Fin n) is-set-unit

Fin-Set :
  (n : ℕ) → UU-Set lzero
Fin-Set n = pair (Fin n) (is-set-Fin n)

is-equiv-prop-in-id :
  {i j : Level} {A : UU i}
  (R : A → A → UU j)
  (p : (x y : A) → is-prop (R x y))
  (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y) →
  (x y : A) → is-equiv (i x y)
is-equiv-prop-in-id R p ρ i x =
  fundamental-theorem-id-retr x (i x)
    ( λ y → pair
      ( ind-Id x (λ z p → R x z) (ρ x) y)
      ( λ r → eq-is-prop (p x y)))

is-set-prop-in-id :
  {i j : Level} {A : UU i} (R : A → A → UU j)
  (p : (x y : A) → is-prop (R x y))
  (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y) →
  is-set A
is-set-prop-in-id R p ρ i x y =
  is-prop-is-equiv'
    ( R x y)
    ( i x y)
    ( is-equiv-prop-in-id R p ρ i x y) (p x y)

Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) → is-decidable (Id x y) → UU lzero
Eq-has-decidable-equality' x y (inl p) = unit
Eq-has-decidable-equality' x y (inr f) = empty

Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) → A → A → UU lzero
Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

is-prop-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  is-prop (Eq-has-decidable-equality' x y t)
is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

is-prop-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A)
  {x y : A} → is-prop (Eq-has-decidable-equality d x y)
is-prop-Eq-has-decidable-equality d {x} {y} =
  is-prop-Eq-has-decidable-equality' x y (d x y)

reflexive-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) (x : A) →
  Eq-has-decidable-equality d x x 
reflexive-Eq-has-decidable-equality d x with d x x
... | inl α = star
... | inr f = f refl

Eq-has-decidable-equality-eq :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Id x y → Eq-has-decidable-equality d x y
Eq-has-decidable-equality-eq {l} {A} d {x} {.x} refl =
  reflexive-Eq-has-decidable-equality d x

eq-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  Eq-has-decidable-equality' x y t → Id x y
eq-Eq-has-decidable-equality' x y (inl p) t = p
eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

eq-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Eq-has-decidable-equality d x y → Id x y
eq-Eq-has-decidable-equality d {x} {y} =
  eq-Eq-has-decidable-equality' x y (d x y)

is-set-has-decidable-equality :
  {l : Level} {A : UU l} → has-decidable-equality A → is-set A
is-set-has-decidable-equality d =
  is-set-prop-in-id
    ( λ x y → Eq-has-decidable-equality d x y)
    ( λ x y → is-prop-Eq-has-decidable-equality d)
    ( λ x → reflexive-Eq-has-decidable-equality d x)
    ( λ x y → eq-Eq-has-decidable-equality d)

is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-prop A → is-subtype B → is-prop (Σ A B)
is-prop-Σ = is-trunc-Σ neg-one-𝕋
                       
Σ-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : type-Prop P → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
Σ-Prop P Q =
  pair
    ( Σ (type-Prop P) (λ p → type-Prop (Q p)))
    ( is-prop-Σ
      ( is-prop-type-Prop P)
      ( λ p → is-prop-type-Prop (Q p)))

is-set-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
is-set-Σ = is-trunc-Σ zero-𝕋

Σ-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
Σ-Set A B =
  pair
    ( Σ (type-Set A) (λ x → (type-Set (B x))))
    ( is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x)))

prod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
prod-Set A B = Σ-Set A (λ x → B)

is-trunc-is-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
  (f : A → B) → is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
is-trunc-is-emb k f Ef H x y =
  is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

is-trunc-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} →
  (f : A ↪ B) → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)

total-subtype :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
total-subtype {A = A} P = Σ A (λ x → pr1 (P x))

is-prop-raise-unit :
  {l1 : Level} → is-prop (raise-unit l1)
is-prop-raise-unit {l1} =
  is-prop-equiv' unit (equiv-raise l1 unit) is-prop-unit

is-emb-is-prop-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop-map f → is-emb f
is-emb-is-prop-map {f = f} is-prop-map-f x =
  fundamental-theorem-id x refl
    ( is-contr-equiv
      ( fib f (f x))
      ( equiv-tot (λ y → equiv-inv (f x) (f y)))
      ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
    ( λ y → ap f)

is-prop-map-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-emb f → is-prop-map f
is-prop-map-is-emb {f = f} is-emb-f y =
  is-prop-is-proof-irrelevant α
  where
  α : (t : fib f y) → is-contr (fib f y)
  α (pair x refl) =
    fundamental-theorem-id' x refl
      ( λ y → inv ∘ ap f)
      ( λ y →
        is-equiv-comp' inv (ap f)
          ( is-emb-f x y)
          ( is-equiv-inv (f x) (f y)))

is-prop-map-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : B ↪ A) → is-prop-map (map-emb f)
is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

is-emb-is-injective' : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
  {B : UU l2} (is-set-B : is-set B) (f : A → B) →
  is-injective f → is-emb f
is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
  is-equiv-is-prop
    ( is-set-A x y)
    ( is-set-B (f x) (f y))
    ( is-injective-f)

is-set-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-set A
is-set-is-injective {f = f} H I =
  is-set-prop-in-id
    ( λ x y → Id (f x) (f y))
    ( λ x y → H (f x) (f y))
    ( λ x → refl)
    ( λ x y → I)

is-emb-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-emb f
is-emb-is-injective {f = f} H I =
  is-emb-is-injective' (is-set-is-injective H I) H f I

is-prop-map-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-prop-map f
is-prop-map-is-injective {f = f} H I =
  is-prop-map-is-emb (is-emb-is-injective H I)

is-prop-Eq-ℕ :
  (n m : ℕ) → is-prop (Eq-ℕ n m)
is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

is-set-ℕ : is-set ℕ
is-set-ℕ =
  is-set-prop-in-id
    Eq-ℕ
    is-prop-Eq-ℕ
    refl-Eq-ℕ
    eq-Eq-ℕ

ℕ-Set : UU-Set lzero
ℕ-Set = pair ℕ is-set-ℕ

is-set-ℤ : is-set ℤ
is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

ℤ-Set : UU-Set lzero
ℤ-Set = pair ℤ is-set-ℤ

fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) → B x → Σ A B
fiber-inclusion B x = pair x

fib-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A) (t : Σ A B) →
  fib (fiber-inclusion B a) t ≃ Id a (pr1 t)
fib-fiber-inclusion B a t =
  ( ( right-unit-law-Σ-is-contr
      ( λ p → is-contr-map-is-equiv (is-equiv-tr B p) (pr2 t))) ∘e
    ( equiv-left-swap-Σ)) ∘e
  ( equiv-tot (λ b → equiv-pair-eq-Σ (pair a b) t))

is-trunc-is-trunc-map-fiber-inclusion :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} →
  ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
  is-trunc (succ-𝕋 k) A
is-trunc-is-trunc-map-fiber-inclusion {l1} {l2} k {A} H x y =
  is-trunc-equiv' k
    ( fib (fiber-inclusion B x) (pair y raise-star))
    ( fib-fiber-inclusion B x (pair y raise-star))
    ( H B x (pair y raise-star))
  where
  B : A → UU l2
  B a = raise-unit l2

is-trunc-map-fiber-inclusion-is-trunc :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : A → UU l2) (a : A) →
  is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
is-trunc-map-fiber-inclusion-is-trunc k B a H t =
  is-trunc-equiv k
    ( Id a (pr1 t))
    ( fib-fiber-inclusion B a t)
    ( H a (pr1 t))

is-emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-set A → (x : A) → is-emb (fiber-inclusion B x)
is-emb-fiber-inclusion B H x =
  is-emb-is-prop-map (is-trunc-map-fiber-inclusion-is-trunc neg-one-𝕋 B x H)

emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-set A → (x : A) → B x ↪ Σ A B
emb-fiber-inclusion B H x =
  pair (fiber-inclusion B x) (is-emb-fiber-inclusion B H x)

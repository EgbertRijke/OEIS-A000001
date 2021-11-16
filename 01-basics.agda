{-# OPTIONS --without-K --exact-split #-}

module 01-basics where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

map-inv-raise :
  {l l1 : Level} {A : UU l1} → raise l A → A
map-inv-raise (map-raise x) = x

id : {i : Level} {A : UU i} → A → A
id a = a 

_∘_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b

data unit : UU lzero where
  star : unit

raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star

ind-unit : {l : Level} {P : unit → UU l} → P star → ((x : unit) → P x)
ind-unit p star = p

terminal-map : {l : Level} {A : UU l} → A → unit
terminal-map a = star

data empty : UU lzero where

raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

¬ : {l : Level} → UU l → UU l
¬ A = A → empty

¬¬ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

functor-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

is-empty : {l : Level} → UU l → UU l
is-empty = ¬

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = ¬ (is-empty A)

intro-dn : {l : Level} {P : UU l} → P → ¬¬ P
intro-dn p f = f p

data coprod {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → coprod A B
  inr : B → coprod A B

ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : coprod A B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x

map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
map-coprod f g (inl x) = inl (f x)
map-coprod f g (inr y) = inr (g y)

data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

one-ℕ : ℕ
one-ℕ = succ-ℕ zero-ℕ

add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m

mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

data Σ {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  pair : (x : A) → (B x → Σ A B)

ind-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : A) (y : B x) → C (pair x y)) → ((t : Σ A B) → C t)
ind-Σ f (pair x y) = f x y

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (pair x y)

pr1 : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → Σ A B → A
pr1 (pair a _) = a

pr2 : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → (t : Σ A B) → B (pr1 t)
pr2 (pair a b) = b

prod : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prod A B = Σ A (λ a → B)

pair' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → prod A B
pair' = pair

_×_ :  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = prod A B

map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
map-prod f g (pair a b) = pair (f a) (g b)

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

ind-Id :
  {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x B b y refl = b

is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = Id n zero-ℕ

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = Id n one-ℕ

is-successor-ℕ : ℕ → UU lzero
is-successor-ℕ n = Σ ℕ (λ y → Id n (succ-ℕ y))

_∙_ :
  {i : Level} {A : UU i} {x y z : A} → Id x y → Id y z → Id x z
refl ∙ q = q

concat :
  {i : Level} {A : UU i} {x y : A} → Id x y → (z : A) → Id y z → Id x z
concat p z q = p ∙ q

inv :
  {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv refl = refl

assoc :
  {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z)
  (r : Id z w) → Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
assoc refl q r = refl

left-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (refl ∙ p) p
left-unit = refl

right-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (p ∙ refl) p
right-unit {p = refl} = refl

left-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id ((inv p) ∙ p) refl
left-inv refl = refl

right-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (p ∙ (inv p)) refl
right-inv refl = refl

ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) →
  Id (f x) (f y)
ap f refl = refl

ap-id :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (ap id p) p
ap-id refl = refl

ap-comp :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C)
  (f : A → B) {x y : A} (p : Id x y) → Id (ap (g ∘ f) p) (ap g (ap f p))
ap-comp g f refl = refl

ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') → Id (f x y) (f x' y')
ap-binary f refl refl = refl

triangle-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap-binary f p q) (ap (λ z → f z y) p ∙ ap (f x') q)
triangle-ap-binary f refl refl = refl

triangle-ap-binary' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap-binary f p q) (ap (f x) q ∙ ap (λ z → f z y') p)
triangle-ap-binary' f refl refl = refl

left-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x : A} {y y' : B} (q : Id y y') →
  Id (ap-binary f refl q) (ap (f x) q)
left-unit-ap-binary f refl = refl

right-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y : B} →
  Id (ap-binary f p refl) (ap (λ z → f z y) p)
right-unit-ap-binary f refl = refl

tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

apd :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A}
  (p : Id x y) → Id (tr B p (f x)) (f y)
apd f refl = refl

tr-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : A → C) (g : (x : A) → B x → D (f x)) {x y : A} (p : Id x y) (z : B x) →
  Id (tr D (ap f p) (g x z)) (g y (tr B p z))
tr-ap f g refl z = refl

inv-con :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id q ((inv p) ∙ r)
inv-con refl q r = id 

con-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id p (r ∙ (inv q))
con-inv p refl r =
  ( λ α → α ∙ (inv right-unit)) ∘ (concat (inv right-unit) r)

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

is-zero-Fin : {k : ℕ} → Fin k → UU lzero
is-zero-Fin {succ-ℕ k} x = Id x zero-Fin

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  coprod A B → coprod A B → UU (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inl x) (inl y) = raise (l1 ⊔ l2) (Id x y)
Eq-coprod {l1} {l2} A B (inl x) (inr y) = raise-empty (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inr x) (inl y) = raise-empty (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inr x) (inr y) = raise (l1 ⊔ l2) (Id x y)

reflexive-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (t : coprod A B) → Eq-coprod A B t t
reflexive-Eq-coprod {l1} {l2} A B (inl x) = map-raise refl
reflexive-Eq-coprod {l1} {l2} A B (inr x) = map-raise refl

Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (s t : coprod A B) → Id s t → Eq-coprod A B s t
Eq-eq-coprod A B s .s refl = reflexive-Eq-coprod A B s

eq-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (s t : coprod A B) →
  Eq-coprod A B s t → Id s t
eq-Eq-coprod A B (inl x) (inl x') = ap inl ∘ map-inv-raise
eq-Eq-coprod A B (inl x) (inr y') = ex-falso ∘ map-inv-raise
eq-Eq-coprod A B (inr y) (inl x') = ex-falso ∘ map-inv-raise
eq-Eq-coprod A B (inr y) (inr y') = ap inr ∘ map-inv-raise

Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = ({x y : A} → Id (f x) (f y) → Id x y)

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

has-decidable-equality-Fin :
  {k : ℕ} (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin {k} x y =
  map-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

has-decidable-equality-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-prod' f g (pair x y) (pair x' y') with
  f y x x' | g x y y'
... | inl refl | inl refl = inl refl
... | inl refl | inr nq = inr (λ r → nq (ap pr2 r))
... | inr np | inl refl = inr (λ r → np (ap pr1 r))
... | inr np | inr nq = inr (λ r → np (ap pr1 r))

has-decidable-equality-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-prod d e =
  has-decidable-equality-prod' (λ y → d) (λ x → e)

has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor d b x y with d (pair x b) (pair y b)
... | inl p = inl (ap pr1 p)
... | inr np = inr (λ q → np (ap (λ z → pair z b) q))

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor d a x y with d (pair a x) (pair a y)
... | inl p = inl (ap pr2 p)
... | inr np = inr (λ q → np (ap (pair a) q))

_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↔ B = (A → B) × (B → A)

Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = unit
Eq-ℕ zero-ℕ (succ-ℕ n) = empty
Eq-ℕ (succ-ℕ m) zero-ℕ = empty
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

Eq-eq-ℕ : {x y : ℕ} → Id x y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → Id x y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = ap succ-ℕ (eq-Eq-ℕ x y e)

ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)

is-injective-inl :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-injective (inl {A = X} {B = Y})
is-injective-inl {l1} {l2} {X} {Y} {x} {y} p =
  map-inv-raise (Eq-eq-coprod X Y (inl x) (inl y) p)

is-injective-inr :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-injective (inr {A = X} {B = Y})
is-injective-inr {l1} {l2} {X} {Y} {x} {y} p =
  map-inv-raise (Eq-eq-coprod X Y (inr x) (inr y) p)

neq-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (x : A) (y : B) →
  ¬ (Id (inl x) (inr y))
neq-inl-inr {l1} {l2} {A} {B} x y =
  map-inv-raise ∘ Eq-eq-coprod A B (inl x) (inr y)

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

is-decidable-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (coprod A B)
is-decidable-coprod (inl a) y = inl (inl a)
is-decidable-coprod (inr na) (inl b) = inl (inr b)
is-decidable-coprod (inr na) (inr nb) = inr (ind-coprod (λ x → empty) na nb)

is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-prod (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-prod (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty

Peano-8 : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
Peano-8 x p = Eq-eq-ℕ p

is-nonzero-succ-ℕ : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
is-nonzero-succ-ℕ = Peano-8

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ {.succ-ℕ x} (pair x refl) = Peano-8 x

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
is-successor-is-nonzero-ℕ {succ-ℕ x} H = pair x refl

ap-add-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (add-ℕ m n) (add-ℕ m' n')
ap-add-ℕ p q = ap-binary add-ℕ p q

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  map-coprod f (functor-neg g)

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-zero-Fin {succ-ℕ k} (inl x) = inl (skip-zero-Fin x)
skip-zero-Fin {succ-ℕ k} (inr star) = inr star

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ k} (inl x) = skip-zero-Fin x
succ-Fin {succ-ℕ k} (inr star) = zero-Fin

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (mod-succ-ℕ k n)

leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ

is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m

antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → Id m n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-leq-ℕ m n p q)

minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)

leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P zero-ℕ) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ind-empty (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-minimal-element-succ-ℕ (λ x → P (succ-ℕ x)) (λ x → d (succ-ℕ x)) m pm
    ( λ m → is-lower-bound-m (succ-ℕ m))
    ( is-lower-bound-m zero-ℕ)
    ( n)
    ( psuccn)
  
well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
well-ordering-principle-succ-ℕ P d n p (inl p0) _ =
  pair zero-ℕ (pair p0 (λ m q → leq-zero-ℕ m))
well-ordering-principle-succ-ℕ P d n p
  (inr neg-p0) (pair m (pair pm is-min-m)) =
  pair
    ( succ-ℕ m)
    ( pair pm
      ( is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0))

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  Σ ℕ P → minimal-element-ℕ P
well-ordering-principle-ℕ P d (pair zero-ℕ p) =
  pair zero-ℕ (pair p (λ m q → leq-zero-ℕ m))
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))

number-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (nP : Σ ℕ P) → ℕ
number-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ

is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ {x} {y} e = eq-Eq-ℕ x y (Eq-eq-ℕ e)

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = Peano-8 y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)

dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ n = n
dist-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
dist-ℕ (succ-ℕ m) (succ-ℕ n) = dist-ℕ m n

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ = ind-empty
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

preserves-le-succ-ℕ :
  (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)

strict-upper-bound-dist-ℕ :
  (b x y : ℕ) → le-ℕ x b → le-ℕ y b → le-ℕ (dist-ℕ x y) b
strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = K
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  preserves-le-succ-ℕ (dist-ℕ x y) b (strict-upper-bound-dist-ℕ b x y H K)

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin {succ-ℕ k} (inr star) =
  succ-le-ℕ k

is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p =
  refl

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = cong-ℕ k x y

contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → Id n n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

transitive-leq-ℕ :
  (n m l : ℕ) → (n ≤-ℕ m) → (m ≤-ℕ l) → (n ≤-ℕ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q

succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (add-ℕ m n)
leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ m (add-ℕ m n) (succ-ℕ (add-ℕ m n))
    ( leq-add-ℕ m n)
    ( succ-leq-ℕ (add-ℕ m n))

right-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)

left-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
left-successor-law-add-ℕ x zero-ℕ = refl
left-successor-law-add-ℕ x (succ-ℕ y) =
  ap succ-ℕ (left-successor-law-add-ℕ x y)
                                        
right-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
right-successor-law-add-ℕ x y = refl

associative-add-ℕ :
  (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
associative-add-ℕ x y zero-ℕ = refl 
associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
commutative-add-ℕ (succ-ℕ x) y =
  (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (add-ℕ n m)
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)

is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (mul-ℕ k d)) p))

eq-dist-ℕ :
  (m n : ℕ) → is-zero-ℕ (dist-ℕ m n) → Id m n
eq-dist-ℕ zero-ℕ zero-ℕ p = refl
eq-dist-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (eq-dist-ℕ m n p)

eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → Id x y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)

eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → Id x y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)

left-zero-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
left-zero-law-mul-ℕ x = refl

right-zero-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
right-zero-law-mul-ℕ zero-ℕ = refl
right-zero-law-mul-ℕ (succ-ℕ x) =
  ( right-unit-law-add-ℕ (mul-ℕ x zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

dist-eq-ℕ' :
  (n : ℕ) → is-zero-ℕ (dist-ℕ n n)
dist-eq-ℕ' zero-ℕ = refl
dist-eq-ℕ' (succ-ℕ n) = dist-eq-ℕ' n

dist-eq-ℕ :
  (m n : ℕ) → Id m n → is-zero-ℕ (dist-ℕ m n)
dist-eq-ℕ m .m refl = dist-eq-ℕ' m

refl-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
refl-cong-ℕ k x =
  pair zero-ℕ ((left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl)))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = refl-cong-ℕ k x

is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (zero-Fin {k}))
is-zero-nat-zero-Fin {zero-ℕ} = refl 
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

decide-leq-ℕ :
  (m n : ℕ) → coprod (m ≤-ℕ n) (n ≤-ℕ m)
decide-leq-ℕ zero-ℕ zero-ℕ = inl star
decide-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
decide-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) = decide-leq-ℕ m n

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coprod (pair star) (pair star) (decide-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coprod (pair star) (pair star) (decide-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coprod (pair star) (pair star) (decide-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = 
  coprod
    ( Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z))
    ( coprod
      ( Id (add-ℕ (dist-ℕ y z) (dist-ℕ x z)) (dist-ℕ x y))
      ( Id (add-ℕ (dist-ℕ x z) (dist-ℕ x y)) (dist-ℕ y z)))

is-additive-right-inverse-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → Id (add-ℕ x (dist-ℕ x y)) y
is-additive-right-inverse-dist-ℕ zero-ℕ zero-ℕ H = refl
is-additive-right-inverse-dist-ℕ zero-ℕ (succ-ℕ y) star = left-unit-law-add-ℕ (succ-ℕ y)
is-additive-right-inverse-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
  ( ap succ-ℕ (is-additive-right-inverse-dist-ℕ x y H))

triangle-equality-dist-ℕ :
  (x y z : ℕ) → (x ≤-ℕ y) → (y ≤-ℕ z) →
  Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z)
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = refl
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star =
  ap succ-ℕ (left-unit-law-add-ℕ z)
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 =
  left-successor-law-add-ℕ y (dist-ℕ y z) ∙
  ap succ-ℕ (is-additive-right-inverse-dist-ℕ y z H2)
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 =
  triangle-equality-dist-ℕ x y z H1 H2

symmetric-dist-ℕ :
  (m n : ℕ) → Id (dist-ℕ m n) (dist-ℕ n m)
symmetric-dist-ℕ zero-ℕ zero-ℕ = refl
symmetric-dist-ℕ zero-ℕ (succ-ℕ n) = refl
symmetric-dist-ℕ (succ-ℕ m) zero-ℕ = refl
symmetric-dist-ℕ (succ-ℕ m) (succ-ℕ n) = symmetric-dist-ℕ m n

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2)))) 
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → Id y z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

left-successor-law-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
left-successor-law-mul-ℕ x y = refl

right-successor-law-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
right-successor-law-mul-ℕ zero-ℕ y = refl
right-successor-law-mul-ℕ (succ-ℕ x) y =
  ( ( ap (λ t → succ-ℕ (add-ℕ t y)) (right-successor-law-mul-ℕ x y)) ∙
    ( ap succ-ℕ (associative-add-ℕ x (mul-ℕ x y) y))) ∙
  ( inv (left-successor-law-add-ℕ x (add-ℕ (mul-ℕ x y) y)))

left-distributive-mul-add-ℕ :
  (x y z : ℕ) → Id (mul-ℕ x (add-ℕ y z)) (add-ℕ (mul-ℕ x y) (mul-ℕ x z))
left-distributive-mul-add-ℕ zero-ℕ y z = refl
left-distributive-mul-add-ℕ (succ-ℕ x) y z =
  ( left-successor-law-mul-ℕ x (add-ℕ y z)) ∙ 
  ( ( ap (add-ℕ' (add-ℕ y z)) (left-distributive-mul-add-ℕ x y z)) ∙ 
    ( ( associative-add-ℕ (mul-ℕ x y) (mul-ℕ x z) (add-ℕ y z)) ∙
      ( ( ap ( add-ℕ (mul-ℕ x y)) 
             ( ( inv (associative-add-ℕ (mul-ℕ x z) y z)) ∙
               ( ( ap (add-ℕ' z) (commutative-add-ℕ (mul-ℕ x z) y)) ∙
                 ( associative-add-ℕ y (mul-ℕ x z) z)))) ∙ 
        ( inv (associative-add-ℕ (mul-ℕ x y) y (add-ℕ (mul-ℕ x z) z))))))

commutative-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
commutative-mul-ℕ (succ-ℕ x) y =
  ( commutative-add-ℕ (mul-ℕ x y) y) ∙ 
  ( ( ap (add-ℕ y) (commutative-mul-ℕ x y)) ∙
    ( inv (right-successor-law-mul-ℕ y x)))

right-distributive-mul-add-ℕ :
  (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
right-distributive-mul-add-ℕ x y z =
  ( commutative-mul-ℕ (add-ℕ x y) z) ∙ 
  ( ( left-distributive-mul-add-ℕ z x y) ∙ 
    ( ( ap (add-ℕ' (mul-ℕ z y)) (commutative-mul-ℕ z x)) ∙ 
      ( ap (add-ℕ (mul-ℕ x z)) (commutative-mul-ℕ z y))))

div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
div-add-ℕ d x y (pair n p) (pair m q) =
  pair
    ( add-ℕ n m)
    ( ( right-distributive-mul-add-ℕ n m d) ∙
      ( ap-add-ℕ p q))

is-injective-add-ℕ' : (k : ℕ) → is-injective (add-ℕ' k)
is-injective-add-ℕ' zero-ℕ = id
is-injective-add-ℕ' (succ-ℕ k) p = is-injective-add-ℕ' k (is-injective-succ-ℕ p)

mul-ℕ' : ℕ → (ℕ → ℕ)
mul-ℕ' x y = mul-ℕ y x

leq-leq-add-ℕ :
  (m n x : ℕ) → (add-ℕ m x) ≤-ℕ (add-ℕ n x) → m ≤-ℕ n
leq-leq-add-ℕ m n zero-ℕ H = H
leq-leq-add-ℕ m n (succ-ℕ x) H = leq-leq-add-ℕ m n x H

concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → Id x' x → x ≤-ℕ y → Id y y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → Id m' m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H

leq-leq-add-ℕ' :
  (m n x : ℕ) → (add-ℕ x m) ≤-ℕ (add-ℕ x n) → m ≤-ℕ n
leq-leq-add-ℕ' m n x H =
  leq-leq-add-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m x)
      ( H)
      ( commutative-add-ℕ x n))


leq-leq-mul-ℕ :
  (m n x : ℕ) → (mul-ℕ (succ-ℕ x) m) ≤-ℕ (mul-ℕ (succ-ℕ x) n) → m ≤-ℕ n
leq-leq-mul-ℕ zero-ℕ zero-ℕ x H = star
leq-leq-mul-ℕ zero-ℕ (succ-ℕ n) x H = star
leq-leq-mul-ℕ (succ-ℕ m) zero-ℕ x H =
  ex-falso
    ( concatenate-leq-eq-ℕ
      ( mul-ℕ (succ-ℕ x) (succ-ℕ m))
      ( H)
      ( right-zero-law-mul-ℕ (succ-ℕ x)))
leq-leq-mul-ℕ (succ-ℕ m) (succ-ℕ n) x H =
  leq-leq-mul-ℕ m n x
    ( leq-leq-add-ℕ' (mul-ℕ (succ-ℕ x) m) (mul-ℕ (succ-ℕ x) n) (succ-ℕ x)
      ( concatenate-eq-leq-eq-ℕ
        ( inv (right-successor-law-mul-ℕ (succ-ℕ x) m))
        ( H)
        ( right-successor-law-mul-ℕ (succ-ℕ x) n)))

leq-leq-mul-ℕ' :
  (m n x : ℕ) → (mul-ℕ m (succ-ℕ x)) ≤-ℕ (mul-ℕ n (succ-ℕ x)) → m ≤-ℕ n
leq-leq-mul-ℕ' m n x H =
  leq-leq-mul-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ (succ-ℕ x) m)
      ( H)
      ( commutative-mul-ℕ n (succ-ℕ x)))

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p) =
  pair
    ( dist-ℕ m n)
    ( is-injective-add-ℕ' (mul-ℕ m (succ-ℕ d))
      ( ( inv
          ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
            ( commutative-add-ℕ
              ( mul-ℕ m (succ-ℕ d))
              ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙ 
        ( ( ap
            ( mul-ℕ' (succ-ℕ d))
            ( is-additive-right-inverse-dist-ℕ m n
              ( leq-leq-mul-ℕ' m n d
                ( concatenate-eq-leq-eq-ℕ q
                  ( leq-add-ℕ' y x)
                  ( inv p))))) ∙
          ( p ∙ (ap (add-ℕ x) (inv q))))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))

trans-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
trans-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
trans-cong-ℕ k x y z d e | inl α =
  concatenate-div-eq-ℕ (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e) α
trans-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e
    ( concatenate-div-eq-ℕ d (inv α))
trans-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d
    ( concatenate-div-eq-ℕ e (inv α))

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  trans-cong-ℕ k x y z H K
  
concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
concatenate-eq-cong-eq-cong-eq-ℕ k {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  trans-cong-ℕ k x y z H K

nat-skip-zero-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (skip-zero-Fin x)) (succ-ℕ (nat-Fin x))
nat-skip-zero-Fin {succ-ℕ k} (inl x) = nat-skip-zero-Fin x
nat-skip-zero-Fin {succ-ℕ k} (inr star) = refl

nat-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (succ-Fin (inl x))) (succ-ℕ (nat-Fin x))
nat-succ-Fin {k} x = nat-skip-zero-Fin x

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ k refl H = H

symm-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
symm-cong-ℕ k x y (pair d p) =
  pair d (p ∙ (symmetric-dist-ℕ x y))

right-unit-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ x one-ℕ) x
right-unit-law-mul-ℕ zero-ℕ = refl
right-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-mul-ℕ x)

left-unit-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ one-ℕ x) x
left-unit-law-mul-ℕ zero-ℕ = refl
left-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-mul-ℕ x)

left-unit-law-dist-ℕ :
  (n : ℕ) → Id (dist-ℕ zero-ℕ n) n
left-unit-law-dist-ℕ zero-ℕ = refl
left-unit-law-dist-ℕ (succ-ℕ n) = refl

right-unit-law-dist-ℕ :
  (n : ℕ) → Id (dist-ℕ n zero-ℕ) n
right-unit-law-dist-ℕ zero-ℕ = refl
right-unit-law-dist-ℕ (succ-ℕ n) = refl

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
cong-zero-ℕ k =
  pair one-ℕ ((left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k)))

cong-zero-ℕ' :
  (k : ℕ) → cong-ℕ k zero-ℕ k
cong-zero-ℕ' k =
  symm-cong-ℕ k k zero-ℕ (cong-zero-ℕ k)

cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → cong-ℕ k (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-Fin (inl x))}
    { succ-ℕ (nat-Fin x)}
    ( nat-succ-Fin x)
cong-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-cong-ℕ
    ( succ-ℕ k)
    { nat-Fin {succ-ℕ k} zero-Fin}
    { zero-ℕ}
    { succ-ℕ k}
    ( is-zero-nat-zero-Fin {k})
    ( cong-zero-ℕ' (succ-ℕ k))

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k zero-ℕ =
  cong-identification-ℕ (succ-ℕ k) (is-zero-nat-zero-Fin {k})
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  trans-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x) )
    ( cong-nat-mod-succ-ℕ k x)

issec-nat-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin {k} x =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( nat-Fin x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( strict-upper-bound-nat-Fin x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin x)))

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

div-Fin : {k : ℕ} → Fin k → Fin k → UU lzero
div-Fin {k} x y = Σ (Fin k) (λ u → Id (mul-Fin u x) y)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ (succ-ℕ k) (nat-Fin x) (nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( H))

eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-mod-succ-cong-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( trans-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( trans-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (one-Fin {succ-ℕ k}))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-mod-succ-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( is-one-nat-one-Fin k)) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin x)

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

refl-div-Fin : {k : ℕ} (x : Fin k) → div-Fin x x
refl-div-Fin {succ-ℕ k} x = pair one-Fin (left-unit-law-mul-Fin x)

associative-mul-ℕ :
  (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
associative-mul-ℕ zero-ℕ y z = refl
associative-mul-ℕ (succ-ℕ x) y z =
  ( right-distributive-mul-add-ℕ (mul-ℕ x y) y z) ∙ 
  ( ap (add-ℕ' (mul-ℕ y z)) (associative-mul-ℕ x y z))

dist-ℕ' : ℕ → ℕ → ℕ
dist-ℕ' m n = dist-ℕ n m

ap-dist-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (dist-ℕ m n) (dist-ℕ m' n')
ap-dist-ℕ p q = ap-binary dist-ℕ p q

translation-invariant-dist-ℕ :
  (k m n : ℕ) → Id (dist-ℕ (add-ℕ k m) (add-ℕ k n)) (dist-ℕ m n)
translation-invariant-dist-ℕ zero-ℕ m n =
  ap-dist-ℕ (left-unit-law-add-ℕ m) (left-unit-law-add-ℕ n)
translation-invariant-dist-ℕ (succ-ℕ k)  m n =
  ( ap-dist-ℕ (left-successor-law-add-ℕ k m) (left-successor-law-add-ℕ k n)) ∙
  ( translation-invariant-dist-ℕ k m n)

translation-invariant-dist-ℕ' :
  (k m n : ℕ) → Id (dist-ℕ (add-ℕ m k) (add-ℕ n k)) (dist-ℕ m n)
translation-invariant-dist-ℕ' k m n =
  ( ap-dist-ℕ (commutative-add-ℕ m k) (commutative-add-ℕ n k)) ∙
  ( translation-invariant-dist-ℕ k m n)

left-distributive-mul-dist-ℕ :
  (m n k : ℕ) → Id (mul-ℕ k (dist-ℕ m n)) (dist-ℕ (mul-ℕ k m) (mul-ℕ k n))
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = refl
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ k
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = refl
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  ap ( dist-ℕ' (mul-ℕ (succ-ℕ k) (succ-ℕ n)))
     ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  ap ( dist-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ m)))
     ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = refl
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  inv
    ( ( ap-dist-ℕ
        ( right-successor-law-mul-ℕ (succ-ℕ k) m)
        ( right-successor-law-mul-ℕ (succ-ℕ k) n)) ∙
      ( ( translation-invariant-dist-ℕ
          ( succ-ℕ k)
          ( mul-ℕ (succ-ℕ k) m)
          ( mul-ℕ (succ-ℕ k) n)) ∙
        ( inv (left-distributive-mul-dist-ℕ m n (succ-ℕ k)))))

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
scalar-invariant-cong-ℕ k x y z (pair d p) =
  pair
    ( mul-ℕ z d)
    ( ( associative-mul-ℕ z d k) ∙
      ( ( ap (mul-ℕ z) p) ∙
        ( left-distributive-mul-dist-ℕ x y z)))

concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ k refl H refl = H

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  trans-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symm-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

trans-div-Fin :
  {k : ℕ} (x y z : Fin k) → div-Fin x y → div-Fin y z → div-Fin x z
trans-div-Fin x y z (pair u p) (pair v q) =
  pair (mul-Fin v u) (associative-mul-Fin v u x ∙ (ap (mul-Fin v) p ∙ q))

left-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin zero-Fin x) zero-Fin
left-zero-law-mul-Fin {k} x =
  ( eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x))
    ( nat-Fin (zero-Fin {k}))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      { mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x)}
      { nat-Fin (zero-Fin {k})}
      ( ap (mul-ℕ' (nat-Fin x)) (is-zero-nat-zero-Fin {k}) ∙ inv (is-zero-nat-zero-Fin {k})))) ∙
  ( issec-nat-Fin (zero-Fin {k}))

div-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin x zero-Fin
div-zero-Fin x = pair zero-Fin (left-zero-law-mul-Fin x)

div-one-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin one-Fin x
div-one-Fin x = pair x (right-unit-law-mul-Fin x)

right-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x zero-Fin) zero-Fin
right-zero-law-mul-Fin x =
  ( commutative-mul-Fin x zero-Fin) ∙
  ( left-zero-law-mul-Fin x)

is-zero-div-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin zero-Fin x → is-zero-Fin x
is-zero-div-zero-Fin {k} x (pair u p) = inv p ∙ right-zero-law-mul-Fin u

is-unit-Fin : {k : ℕ} → Fin k → UU lzero
is-unit-Fin {succ-ℕ k} x = div-Fin x one-Fin

unit-Fin : ℕ → UU lzero
unit-Fin k = Σ (Fin k) is-unit-Fin

is-unit-one-Fin : {k : ℕ} → is-unit-Fin (one-Fin {k})
is-unit-one-Fin {k} = refl-div-Fin one-Fin

one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
one-unit-Fin {k} = pair one-Fin is-unit-one-Fin

square-ℕ : ℕ → ℕ
square-ℕ x = mul-ℕ x x

square-succ-ℕ :
  (k : ℕ) →
  Id (square-ℕ (succ-ℕ k)) (succ-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k))
square-succ-ℕ k =
  ( right-successor-law-mul-ℕ (succ-ℕ k) k) ∙
  ( commutative-add-ℕ (succ-ℕ k) (mul-ℕ (succ-ℕ k) k))

is-unit-neg-one-Fin : {k : ℕ} → is-unit-Fin (neg-one-Fin {k})
is-unit-neg-one-Fin {zero-ℕ} = refl-div-Fin neg-one-Fin
is-unit-neg-one-Fin {succ-ℕ k} =
  pair
    ( neg-one-Fin)
    ( eq-mod-succ-cong-ℕ
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) (succ-ℕ k))
      ( one-ℕ)
      ( concatenate-eq-cong-ℕ
        ( succ-ℕ (succ-ℕ k))
        { x3 = one-ℕ}
        ( square-succ-ℕ k)
        ( pair k
          ( ( commutative-mul-ℕ k (succ-ℕ (succ-ℕ k))) ∙
            ( inv (right-unit-law-dist-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k)))))))

neg-one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
neg-one-unit-Fin = pair neg-one-Fin is-unit-neg-one-Fin

mul-Fin' :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin' {k} x y = mul-Fin y x

is-unit-mul-Fin :
  {k : ℕ} {x y : Fin k} →
  is-unit-Fin x → is-unit-Fin y → is-unit-Fin (mul-Fin x y)
is-unit-mul-Fin {succ-ℕ k} {x} {y} (pair d p) (pair e q) =
  pair
    ( mul-Fin e d)
    ( ( associative-mul-Fin e d (mul-Fin x y)) ∙
      ( ( ap
          ( mul-Fin e)
          ( ( inv (associative-mul-Fin d x y)) ∙
            ( ap (mul-Fin' y) p ∙ left-unit-law-mul-Fin y))) ∙
        ( q)))

mul-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k → unit-Fin k
mul-unit-Fin u v =
  pair (mul-Fin (pr1 u) (pr1 v)) (is-unit-mul-Fin (pr2 u) (pr2 v))

inv-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k
inv-unit-Fin {succ-ℕ k} (pair u (pair v p)) =
  pair v (pair u (commutative-mul-Fin u v ∙ p))

sim-unit-Fin :
  {k : ℕ} → Fin k → Fin k → UU lzero
sim-unit-Fin {k} x y = Σ (unit-Fin k) (λ u → Id (mul-Fin (pr1 u) x) y)

refl-sim-unit-Fin :
  {k : ℕ} (x : Fin k) → sim-unit-Fin x x
refl-sim-unit-Fin {succ-ℕ k} x = pair one-unit-Fin (left-unit-law-mul-Fin x)

symm-sim-unit-Fin :
  {k : ℕ} (x y : Fin k) → sim-unit-Fin x y → sim-unit-Fin y x
symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p) =
  pair
    ( inv-unit-Fin (pair u (pair v q)))
    ( ( ( ( ap (mul-Fin v) (inv p)) ∙
          ( inv (associative-mul-Fin v u x))) ∙
        ( ap (mul-Fin' x) q)) ∙
      ( left-unit-law-mul-Fin x))

trans-sim-unit-Fin :
  {k : ℕ} (x y z : Fin k) → sim-unit-Fin x y → sim-unit-Fin y z →
  sim-unit-Fin x z
trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q) =
  pair
    ( mul-unit-Fin v u)
    ( associative-mul-Fin (pr1 v) (pr1 u) x ∙ (ap (mul-Fin (pr1 v)) p ∙ q))

is-mod-unit-ℕ : (k x : ℕ) → UU lzero
is-mod-unit-ℕ k x = Σ ℕ (λ l → cong-ℕ k (mul-ℕ l x) one-ℕ)

cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-mod-succ-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)

is-mod-unit-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (mod-succ-ℕ k x) one-Fin → is-mod-unit-ℕ (succ-ℕ k) x
is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p) =
  pair
    ( nat-Fin (pr1 u))
    ( cong-eq-mod-succ-ℕ k
      ( mul-ℕ (nat-Fin (pr1 u)) x)
      ( one-ℕ)
      ( ( eq-mod-succ-cong-ℕ k
          ( mul-ℕ (nat-Fin (pr1 u)) x)
          ( mul-ℕ (nat-Fin (pr1 u)) (nat-Fin (mod-succ-ℕ k x)))
          ( scalar-invariant-cong-ℕ
            ( succ-ℕ k)
            ( x)
            ( nat-Fin (mod-succ-ℕ k x))
            ( nat-Fin (pr1 u))
            ( symm-cong-ℕ
              ( succ-ℕ k)
              ( nat-Fin (mod-succ-ℕ k x))
              ( x)
              ( cong-nat-mod-succ-ℕ k x)))) ∙
        ( p)))

is-decidable-Σ-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
is-decidable-Σ-Fin {l} {zero-ℕ} {P} d = inr pr1
is-decidable-Σ-Fin {l} {succ-ℕ k} {P} d with d (inr star)
... | inl p = inl (pair (inr star) p)
... | inr f =
  is-decidable-iff
    ( λ t → pair (inl (pr1 t)) (pr2 t))
    ( g)
    ( is-decidable-Σ-Fin {l} {k} {P ∘ inl} (λ x → d (inl x)))
  where
  g : Σ (Fin (succ-ℕ k)) P → Σ (Fin k) (P ∘ inl)
  g (pair (inl x) p) = pair x p
  g (pair (inr star) p) = ex-falso (f p)

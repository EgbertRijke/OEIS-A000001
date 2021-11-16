{-# OPTIONS --without-K --exact-split #-}

module 03-contractible-types where

open import 02-equivalences public

-- Contractible types

is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → Id a x)

center :
  {l : Level} {A : UU l} → is-contr A → A
center = pr1

eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → Id x y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → Id x y
eq-is-contr (pair c C) {x} {y} = (inv (C x)) ∙ (C y)

contraction :
  {l : Level} {A : UU l} (is-contr-A : is-contr A) →
  (const A A (center is-contr-A) ~ id)
contraction (pair c C) x = eq-is-contr (pair c C)

coh-contraction :
  {l : Level} {A : UU l} (is-contr-A : is-contr A) →
  Id (contraction is-contr-A (center is-contr-A)) refl
coh-contraction (pair c C) = left-inv (C c)

ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a

is-singleton :
  (l : Level) {i : Level} (A : UU i) → A → UU (lsuc l ⊔ i)
is-singleton l A a = (B : A → UU l) → sec (ev-pt a B)

ind-singleton-is-contr :
  {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
  B a → (x : A) → B x
ind-singleton-is-contr a is-contr-A B b x =
  tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b

comp-singleton-is-contr :
  {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
  ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
comp-singleton-is-contr a is-contr-A B b =
  ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-contr-ind-singleton :
  {i : Level} (A : UU i) (a : A) →
  ({l : Level} (P : A → UU l) → P a → (x : A) → P x) → is-contr A
pr1 (is-contr-ind-singleton A a S) = a
pr2 (is-contr-ind-singleton A a S) = S (λ x → Id a x) refl

is-contr-is-singleton :
  {i : Level} (A : UU i) (a : A) →
  ({l : Level} → is-singleton l A a) → is-contr A
is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
pr1 (is-singleton-is-contr a is-contr-A B) =
  ind-singleton-is-contr a is-contr-A B
pr2 (is-singleton-is-contr a is-contr-A B) =
  comp-singleton-is-contr a is-contr-A B

is-singleton-unit : {l : Level} → is-singleton l unit star
pr1 (is-singleton-unit B) = ind-unit
pr2 (is-singleton-unit B) b = refl

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-singleton unit star (is-singleton-unit)

is-singleton-total-path :
  {i l : Level} (A : UU i) (a : A) →
  is-singleton l (Σ A (λ x → Id a x)) (pair a refl)
pr1 (is-singleton-total-path A a B) = ind-Σ ∘ (ind-Id a _)
pr2 (is-singleton-total-path A a B) = refl-htpy

is-contr-total-path :
  {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id a x))
is-contr-total-path {A = A} a =
  is-contr-is-singleton _ _ (is-singleton-total-path A a)

fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
map-inv-is-contr-map is-contr-f y = pr1 (center (is-contr-f y))

issec-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → (f ∘ (map-inv-is-contr-map is-contr-f)) ~ id
issec-map-inv-is-contr-map is-contr-f y = pr2 (center (is-contr-f y))

isretr-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → ((map-inv-is-contr-map is-contr-f) ∘ f) ~ id
isretr-map-inv-is-contr-map {_} {_} {A} {B} {f} is-contr-f x =
  ap ( pr1 {B = λ z → Id (f z) (f x)})
     ( ( inv
         ( contraction
           ( is-contr-f (f x))
           ( pair
             ( map-inv-is-contr-map is-contr-f (f x))
             ( issec-map-inv-is-contr-map is-contr-f (f x))))) ∙
       ( contraction (is-contr-f (f x)) (pair x refl)))

is-equiv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → is-equiv f
is-equiv-is-contr-map is-contr-f =
  is-equiv-has-inverse
    ( map-inv-is-contr-map is-contr-f)
    ( issec-map-inv-is-contr-map is-contr-f)
    ( isretr-map-inv-is-contr-map is-contr-f)

coherence-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
coherence-is-coherently-invertible f g G H = (G ·r f) ~ (f ·l H)

is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-coherently-invertible {l1} {l2} {A} {B} f =
  Σ ( B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id)
        (λ H → ((G ·r f) ~ (f ·l H)))))

inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-coherently-invertible f → B → A
inv-is-coherently-invertible = pr1

issec-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
issec-inv-is-coherently-invertible H = pr1 (pr2 H)

isretr-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

coh-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) →
  coherence-is-coherently-invertible f
    ( inv-is-coherently-invertible H)
    ( issec-inv-is-coherently-invertible H)
    ( isretr-inv-is-coherently-invertible H)
coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))

center-fib-is-coherently-invertible :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-coherently-invertible f → (y : B) → fib f y
pr1 (center-fib-is-coherently-invertible {i} {j} {A} {B} {f} H y) =
  inv-is-coherently-invertible H y
pr2 (center-fib-is-coherently-invertible {i} {j} {A} {B} {f} H y) =
  issec-inv-is-coherently-invertible H y

Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib f y → UU (i ⊔ j)
Eq-fib f y s t =
  Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

reflexive-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  (s : fib f y) → Eq-fib f y s s
pr1 (reflexive-Eq-fib f y s) = refl
pr2 (reflexive-Eq-fib f y s) = refl

Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → (Id s t) → Eq-fib f y s t
Eq-fib-eq f y {s} refl = reflexive-Eq-fib f y s

eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t → Id s t
eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

contraction-fib-is-coherently-invertible :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
  Id (center-fib-is-coherently-invertible H y) t
contraction-fib-is-coherently-invertible {f = f} H y (pair x refl) =
  eq-Eq-fib f y
    ( pair 
      ( isretr-inv-is-coherently-invertible H x)
      ( ( right-unit) ∙
        ( inv ( coh-inv-is-coherently-invertible H x))))

is-contr-map-is-coherently-invertible : 
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-coherently-invertible f → is-contr-map f
pr1 (is-contr-map-is-coherently-invertible H y) =
  center-fib-is-coherently-invertible H y
pr2 (is-contr-map-is-coherently-invertible H y) =
  contraction-fib-is-coherently-invertible H y

htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : has-inverse f)
  where
  
  inv-has-inverse : B → A
  inv-has-inverse = pr1 H
  
  issec-inv-has-inverse : (f ∘ inv-has-inverse) ~ id
  issec-inv-has-inverse y =
    ( inv (pr1 (pr2 H) (f (inv-has-inverse y)))) ∙
    ( ap f (pr2 (pr2 H) (inv-has-inverse y)) ∙ (pr1 (pr2 H) y))
  
  isretr-inv-has-inverse : (inv-has-inverse ∘ f) ~ id
  isretr-inv-has-inverse = pr2 (pr2 H)
  
  coherence-inv-has-inverse :
    (issec-inv-has-inverse ·r f) ~ (f ·l isretr-inv-has-inverse)
  coherence-inv-has-inverse x =
    inv
      ( inv-con
        ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
        ( ap f (pr2 (pr2 H) x))
        ( (ap f (pr2 (pr2 H) (inv-has-inverse (f x)))) ∙ (pr1 (pr2 H) (f x)))
        ( sq-top-whisk
          ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
          ( ap f (pr2 (pr2 H) x))
          ( (ap (f ∘ (inv-has-inverse ∘ f)) (pr2 (pr2 H) x)))
          ( ( ap-comp f (inv-has-inverse ∘ f) (pr2 (pr2 H) x)) ∙
            ( inv (ap (ap f) (htpy-red (pr2 (pr2 H)) x))))
          ( pr1 (pr2 H) (f x))
          ( htpy-nat (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  is-coherently-invertible-has-inverse : is-coherently-invertible f
  pr1 is-coherently-invertible-has-inverse = inv-has-inverse
  pr1 (pr2 is-coherently-invertible-has-inverse) = issec-inv-has-inverse
  pr1 (pr2 (pr2 is-coherently-invertible-has-inverse)) = isretr-inv-has-inverse
  pr2 (pr2 (pr2 is-coherently-invertible-has-inverse)) =
    coherence-inv-has-inverse

is-contr-map-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → is-contr-map f
is-contr-map-is-equiv =
  is-contr-map-is-coherently-invertible ∘
    ( is-coherently-invertible-has-inverse ∘
      has-inverse-is-equiv)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  issec-map-inv-is-equiv : (f ∘ map-inv-is-equiv H) ~ id
  issec-map-inv-is-equiv = issec-inv-has-inverse (has-inverse-is-equiv H)

  isretr-map-inv-is-equiv : (map-inv-is-equiv H ∘ f) ~ id
  isretr-map-inv-is-equiv =
    isretr-inv-has-inverse (has-inverse-is-equiv H)
  
  coherence-map-inv-is-equiv :
    ( issec-map-inv-is-equiv ·r f) ~ (f ·l isretr-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coherence-inv-has-inverse (has-inverse-is-equiv H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv : ((map-equiv e) ∘ map-inv-equiv) ~ id
  issec-map-inv-equiv = issec-map-inv-is-equiv (is-equiv-map-equiv e)

  isretr-map-inv-equiv : (map-inv-equiv ∘ (map-equiv e)) ~ id
  isretr-map-inv-equiv =
    isretr-map-inv-is-equiv (is-equiv-map-equiv e)
  
  coherence-map-inv-equiv :
    ( issec-map-inv-equiv ·r (map-equiv e)) ~
    ( (map-equiv e) ·l isretr-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

is-contr-is-equiv-const :
  {i : Level} {A : UU i} → is-equiv (terminal-map {A = A}) → is-contr A
pr1 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = h star
pr2 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = isretr

is-equiv-terminal-map-is-contr :
  {i : Level} {A : UU i} → is-contr A → is-equiv (terminal-map {A = A})
pr1 (pr1 (is-equiv-terminal-map-is-contr {i} {A} is-contr-A)) =
  ind-unit (center is-contr-A)
pr2 (pr1 (is-equiv-terminal-map-is-contr {i} {A} is-contr-A)) = ind-unit refl
pr1 (pr2 (is-equiv-terminal-map-is-contr {i} {A} is-contr-A)) =
  const unit A (center is-contr-A)
pr2 (pr2 (is-equiv-terminal-map-is-contr {i} {A} is-contr-A)) =
  contraction is-contr-A

is-contr-is-equiv :
  {i j : Level} {A : UU i} (B : UU j) (f : A → B) →
  is-equiv f → is-contr B → is-contr A
is-contr-is-equiv B f is-equiv-f is-contr-B =
  is-contr-is-equiv-const
    ( is-equiv-comp'
      ( terminal-map)
      ( f)
      ( is-equiv-f)
      ( is-equiv-terminal-map-is-contr is-contr-B))

is-contr-is-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (f : A → B) →
  is-equiv f → is-contr A → is-contr B
is-contr-is-equiv' A f is-equiv-f is-contr-A =
  is-contr-is-equiv A
    ( map-inv-is-equiv is-equiv-f)
    ( is-equiv-map-inv-is-equiv is-equiv-f)
    ( is-contr-A)

is-equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-contr A → is-contr B → is-equiv f
is-equiv-is-contr {i} {j} {A} {B} f is-contr-A is-contr-B =
  is-equiv-has-inverse
    ( const B A (center is-contr-A))
    ( ind-singleton-is-contr _ is-contr-B _
      ( inv (contraction is-contr-B (f (center is-contr-A)))))
    ( contraction is-contr-A)

equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → A ≃ B
pr1 (equiv-is-contr is-contr-A is-contr-B) a = center is-contr-B
pr2 (equiv-is-contr is-contr-A is-contr-B) =
  is-equiv-is-contr _ is-contr-A is-contr-B
 
is-contr-equiv :
  {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) → is-contr B → is-contr A
is-contr-equiv B (pair e is-equiv-e) is-contr-B =
  is-contr-is-equiv B e is-equiv-e is-contr-B

is-contr-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) → is-contr A → is-contr B
is-contr-equiv' A (pair e is-equiv-e) is-contr-A =
  is-contr-is-equiv' A e is-equiv-e is-contr-A

contraction-is-prop-is-contr :
  {i : Level} {A : UU i} (H : is-contr A) {x y : A} →
  (p : Id x y) → Id (eq-is-contr H) p
contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

is-prop-is-contr : {i : Level} {A : UU i} → is-contr A →
  (x y : A) → is-contr (Id x y)
pr1 (is-prop-is-contr {i} {A} is-contr-A x y) = eq-is-contr is-contr-A
pr2 (is-prop-is-contr {i} {A} is-contr-A x y) =
  contraction-is-prop-is-contr is-contr-A

is-contr-raise-unit :
  {l1 : Level} → is-contr (raise-unit l1)
is-contr-raise-unit {l1} =
  is-contr-equiv' unit (equiv-raise l1 unit) is-contr-unit

map-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  fib (pr1 {B = B}) a → B a
map-fib-pr1 B a (pair (pair x y) p) = tr B p y

map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → B a → fib (pr1 {B = B}) a
map-inv-fib-pr1 B a b = pair (pair a b) refl

issec-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((map-inv-fib-pr1 B a) ∘ (map-fib-pr1 B a)) ~ id
issec-map-inv-fib-pr1 B a (pair (pair .a y) refl) = refl

isretr-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((map-fib-pr1 B a) ∘ (map-inv-fib-pr1 B a)) ~ id
isretr-map-inv-fib-pr1 B a b = refl

is-equiv-map-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  is-equiv (map-fib-pr1 B a)
is-equiv-map-fib-pr1 B a =
  is-equiv-has-inverse
    ( map-inv-fib-pr1 B a)
    ( isretr-map-inv-fib-pr1 B a)
    ( issec-map-inv-fib-pr1 B a)

equiv-fib-pr1 :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) → fib (pr1 {B = B}) a ≃ B a
pr1 (equiv-fib-pr1 {B = B} a) = map-fib-pr1 B a
pr2 (equiv-fib-pr1 {B = B} a) = is-equiv-map-fib-pr1 B a

map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → (Σ B (fib f)) → A
map-equiv-total-fib f t = pr1 (pr2 t)

triangle-map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  pr1 ~ (f ∘ (map-equiv-total-fib f))
triangle-map-equiv-total-fib f t = inv (pr2 (pr2 t))

map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A → Σ B (fib f)
pr1 (map-inv-equiv-total-fib f x) = f x
pr1 (pr2 (map-inv-equiv-total-fib f x)) = x
pr2 (pr2 (map-inv-equiv-total-fib f x)) = refl

isretr-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((map-inv-equiv-total-fib f) ∘ (map-equiv-total-fib f)) ~ id
isretr-map-inv-equiv-total-fib f (pair .(f x) (pair x refl)) = refl

issec-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((map-equiv-total-fib f) ∘ (map-inv-equiv-total-fib f)) ~ id
issec-map-inv-equiv-total-fib f x = refl

is-equiv-map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-equiv (map-equiv-total-fib f)
is-equiv-map-equiv-total-fib f =
  is-equiv-has-inverse
    ( map-inv-equiv-total-fib f)
    ( issec-map-inv-equiv-total-fib f)
    ( isretr-map-inv-equiv-total-fib f)

is-equiv-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-equiv (map-inv-equiv-total-fib f)
is-equiv-map-inv-equiv-total-fib f =
  is-equiv-has-inverse
    ( map-equiv-total-fib f)
    ( isretr-map-inv-equiv-total-fib f)
    ( issec-map-inv-equiv-total-fib f)

equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → Σ B (fib f) ≃ A
pr1 (equiv-total-fib f) = map-equiv-total-fib f
pr2 (equiv-total-fib f) = is-equiv-map-equiv-total-fib f

inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A ≃ Σ B (fib f)
pr1 (inv-equiv-total-fib f) = map-inv-equiv-total-fib f
pr2 (inv-equiv-total-fib f) = is-equiv-map-inv-equiv-total-fib f

is-equiv-pr1-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
is-equiv-pr1-is-contr {B = B} is-contr-B =
  is-equiv-is-contr-map
    ( λ x → is-contr-equiv
      ( B x)
      ( equiv-fib-pr1 x)
      ( is-contr-B x))

equiv-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
pr1 (equiv-pr1 is-contr-B) = pr1
pr2 (equiv-pr1 is-contr-B) = is-equiv-pr1-is-contr is-contr-B

right-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
right-unit-law-Σ-is-contr = equiv-pr1

right-unit-law-prod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-contr B → (A × B) ≃ A
right-unit-law-prod-is-contr {l1} {l2} {A} {B} H =
  right-unit-law-Σ-is-contr (λ a → H)

is-contr-is-equiv-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (is-equiv (pr1 {B = B})) → ((a : A) → is-contr (B a))
is-contr-is-equiv-pr1 {B = B} is-equiv-pr1-B a =
  is-contr-equiv'
    ( fib pr1 a)
    ( equiv-fib-pr1 a)
    ( is-contr-map-is-equiv is-equiv-pr1-B a)
      
is-equiv-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  is-equiv (map-inv-fib-pr1 B a)
is-equiv-map-inv-fib-pr1 B a =
  is-equiv-has-inverse
    ( map-fib-pr1 B a)
    ( issec-map-inv-fib-pr1 B a)
    ( isretr-map-inv-fib-pr1 B a)

inv-equiv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  B a ≃ fib (pr1 {B = B}) a
pr1 (inv-equiv-fib-pr1 B a) = map-inv-fib-pr1 B a
pr2 (inv-equiv-fib-pr1 B a) = is-equiv-map-inv-fib-pr1 B a

map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → B x) → (A → Σ A B)
pr1 (map-section b a) = a
pr2 (map-section b a) = b a

htpy-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (pr1 ∘ map-section b) ~ id
htpy-map-section b a = refl

is-equiv-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  ((x : A) → is-contr (B x)) → is-equiv (map-section b)
is-equiv-map-section b C =
  is-equiv-right-factor
    ( id)
    ( pr1)
    ( map-section b)
    ( htpy-map-section b)
    ( is-equiv-pr1-is-contr C)
    ( is-equiv-id)

equiv-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  ((x : A) → is-contr (B x)) → A ≃ Σ A B
pr1 (equiv-section b C) = map-section b
pr2 (equiv-section b C) = is-equiv-map-section b C

is-contr-fam-is-equiv-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-equiv (map-section b) → ((x : A) → is-contr (B x))
is-contr-fam-is-equiv-map-section b H =
  is-contr-is-equiv-pr1
    ( is-equiv-left-factor id pr1
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-id)
      ( H))

-- !! this one potentially causes a slowdown
tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → ( Σ A B → Σ A C)
pr1 (tot f t) = pr1 t
pr2 (tot f t) = f (pr1 t) (pr2 t)

tot-htpy :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair-Σ refl (H x y)

tot-id :
  {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (pair x y) = refl

tot-comp :
  {i j j' j'' : Level}
  {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (pair x y) = refl

fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (tot f) t → fib (f (pr1 t)) (pr2 t)
pr1 (fib-ftr-fib-tot f .(tot f (pair x y)) (pair (pair x y) refl)) = y
pr2 (fib-ftr-fib-tot f .(tot f (pair x y)) (pair (pair x y) refl)) = refl

fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (f (pr1 t)) (pr2 t) → fib (tot f) t
pr1 (pr1 (fib-tot-fib-ftr F (pair a .(F a y)) (pair y refl))) = a
pr2 (pr1 (fib-tot-fib-ftr F (pair a .(F a y)) (pair y refl))) = y
pr2 (fib-tot-fib-ftr F (pair a .(F a y)) (pair y refl)) = refl

issec-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (pair x .(f x y)) (pair y refl) = refl

isretr-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(pair x (f x y)) (pair (pair x y) refl) = refl

is-equiv-fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  is-equiv (fib-ftr-fib-tot f t)
is-equiv-fib-ftr-fib-tot f t =
  is-equiv-has-inverse
    ( fib-tot-fib-ftr f t)
    ( issec-fib-tot-fib-ftr f t)
    ( isretr-fib-tot-fib-ftr f t)

is-equiv-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  is-equiv (fib-tot-fib-ftr f t)
is-equiv-fib-tot-fib-ftr f t =
  is-equiv-has-inverse
    ( fib-ftr-fib-tot f t)
    ( isretr-fib-tot-fib-ftr f t)
    ( issec-fib-tot-fib-ftr f t)

is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

is-equiv-tot-is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  {f : (x : A) → B x → C x} → is-fiberwise-equiv f →
  is-equiv (tot f )
is-equiv-tot-is-fiberwise-equiv {f = f} H =
  is-equiv-is-contr-map
    ( λ t → is-contr-is-equiv _
      ( fib-ftr-fib-tot f t)
      ( is-equiv-fib-ftr-fib-tot f t)
      ( is-contr-map-is-equiv (H _) (pr2 t)))

is-fiberwise-equiv-is-equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-equiv (tot f) →
  is-fiberwise-equiv f
is-fiberwise-equiv-is-equiv-tot {A = A} {B} {C} f is-equiv-tot-f x =
  is-equiv-is-contr-map
    ( λ z → is-contr-is-equiv'
      ( fib (tot f) (pair x z))
      ( fib-ftr-fib-tot f (pair x z))
      ( is-equiv-fib-ftr-fib-tot f (pair x z))
      ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
pr1 (equiv-tot e) = tot (λ x → map-equiv (e x))
pr2 (equiv-tot e) =
  is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x))

fundamental-theorem-id :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
fundamental-theorem-id {A = A} a b is-contr-AB f =
  is-fiberwise-equiv-is-equiv-tot f
    ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

fundamental-theorem-id' :
  {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (b : B a) (f : (x : A) → Id a x → B x) →
  is-fiberwise-equiv f → is-contr (Σ A B)
fundamental-theorem-id' {A = A} {B = B} a b f is-fiberwise-equiv-f =
  is-contr-is-equiv'
    ( Σ A (Id a))
    ( tot f)
    ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
    ( is-contr-total-path a)

is-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

_↪_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A ↪ B = Σ (A → B) is-emb

map-emb :
  {i j : Level} {A : UU i} {B : UU j} → A ↪ B → A → B
map-emb f = pr1 f

is-emb-map-emb :
  { i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → is-emb (map-emb f)
is-emb-map-emb f = pr2 f

equiv-ap-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ↪ B) {x y : A} →
  Id x y ≃ Id (map-emb e x) (map-emb e y)
pr1 (equiv-ap-emb e {x} {y}) = ap (map-emb e)
pr2 (equiv-ap-emb e {x} {y}) = is-emb-map-emb e x y

is-injective-is-emb : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-emb f → is-injective f
is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

is-injective-emb :
  {i j : Level} {A : UU i} {B : UU j} (e : A ↪ B) → is-injective (map-emb e)
is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)

is-emb-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → is-emb f
is-emb-is-equiv {i} {j} {A} {B} {f} is-equiv-f x =
  fundamental-theorem-id x refl
    ( is-contr-equiv
      ( fib f (f x))
      ( equiv-tot (λ y → equiv-inv (f x) (f y)))
      ( is-contr-map-is-equiv is-equiv-f (f x)))
    ( λ y p → ap f p)

emb-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A ↪ B)
pr1 (emb-equiv e) = map-equiv e
pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)

emb-id :
  {i : Level} {A : UU i} → (A ↪ A)
emb-id {i} {A} = emb-equiv equiv-id

is-emb-id : {l : Level} {A : UU l} → is-emb (id {A = A})
is-emb-id = is-emb-map-emb emb-id

equiv-ap :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) (x y : A) →
  (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
pr1 (equiv-ap e x y) = ap (map-equiv e) {x} {y}
pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y

is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
  A retract-of B → is-contr B → is-contr A
pr1 (is-contr-retract-of B (pair i (pair r isretr)) is-contr-B) =
  r (center is-contr-B)
pr2 (is-contr-retract-of B (pair i (pair r isretr)) is-contr-B) x =
  (ap r (contraction is-contr-B (i x))) ∙ (isretr x)

is-contr-left-factor-prod :
  {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr A
is-contr-left-factor-prod A B is-contr-AB =
  is-contr-retract-of
    ( A × B)
    ( pair
      ( λ x → pair x (pr2 (center is-contr-AB)))
      ( pair pr1 (λ x → refl)))
    ( is-contr-AB)

is-contr-right-factor-prod :
  {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr B
is-contr-right-factor-prod A B is-contr-AB =
  is-contr-left-factor-prod B A
    ( is-contr-equiv
      ( A × B)
      ( equiv-swap-prod B A)
      ( is-contr-AB))

is-contr-prod :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → is-contr (A × B)
pr1 (pr1 (is-contr-prod {A = A} {B = B} (pair a C) (pair b D))) = a
pr2 (pr1 (is-contr-prod {A = A} {B = B} (pair a C) (pair b D))) = b
pr2 (is-contr-prod {A = A} {B = B} (pair a C) (pair b D)) (pair x y) =
  eq-pair (C x) (D y)

map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-contr A → (a : A) →
  B a → Σ A B
pr1 (map-inv-left-unit-law-Σ-is-contr C a b) = a
pr2 (map-inv-left-unit-law-Σ-is-contr C a b) = b

map-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-contr A → (a : A) →
  Σ A B → B a
map-left-unit-law-Σ-is-contr {B = B} C a =
  ind-Σ
    ( ind-singleton-is-contr a C
      ( λ x → B x → B a)
      ( id))

issec-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  ( ( map-left-unit-law-Σ-is-contr {B = B} C a) ∘
    ( map-inv-left-unit-law-Σ-is-contr {B = B} C a)) ~ id
issec-map-inv-left-unit-law-Σ-is-contr {B = B} C a b =
  ap ( λ (f : B a → B a) → f b)
     ( comp-singleton-is-contr a C (λ x → B x → B a) id)

isretr-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  ( ( map-inv-left-unit-law-Σ-is-contr {B = B} C a) ∘
    ( map-left-unit-law-Σ-is-contr {B = B} C a)) ~ id
isretr-map-inv-left-unit-law-Σ-is-contr {B = B} C a = 
  ind-Σ
    ( ind-singleton-is-contr a C
      ( λ x → (y : B x) →
        Id ( ( ( map-inv-left-unit-law-Σ-is-contr C a) ∘
               ( map-left-unit-law-Σ-is-contr C a))
             ( pair x y))
           ( id (pair x y)))
      ( λ y → ap
        ( map-inv-left-unit-law-Σ-is-contr C a)
        ( ap ( λ f → f y)
             ( comp-singleton-is-contr a C (λ x → B x → B a) id))))

is-equiv-map-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  is-equiv (map-left-unit-law-Σ-is-contr {B = B} C a)
is-equiv-map-left-unit-law-Σ-is-contr C a =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-Σ-is-contr C a)
    ( issec-map-inv-left-unit-law-Σ-is-contr C a)
    ( isretr-map-inv-left-unit-law-Σ-is-contr C a)

left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  Σ A B ≃ B a
pr1 (left-unit-law-Σ-is-contr C a) = map-left-unit-law-Σ-is-contr C a
pr2 (left-unit-law-Σ-is-contr C a) = is-equiv-map-left-unit-law-Σ-is-contr C a

left-unit-law-prod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (C : is-contr A) → (A × B) ≃ B
left-unit-law-prod-is-contr C =
  left-unit-law-Σ-is-contr C (center C)

is-equiv-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  is-equiv (map-inv-left-unit-law-Σ-is-contr {B = B} C a)
is-equiv-map-inv-left-unit-law-Σ-is-contr C a =
  is-equiv-has-inverse
    ( map-left-unit-law-Σ-is-contr C a)
    ( isretr-map-inv-left-unit-law-Σ-is-contr C a)
    ( issec-map-inv-left-unit-law-Σ-is-contr C a)

inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  B a ≃ Σ A B
pr1 (inv-left-unit-law-Σ-is-contr C a) = map-inv-left-unit-law-Σ-is-contr C a
pr2 (inv-left-unit-law-Σ-is-contr C a) =
  is-equiv-map-inv-left-unit-law-Σ-is-contr C a

is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-split {A = A} {B = B} f =
  sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

is-path-split-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-path-split f
pr1 (is-path-split-is-equiv f is-equiv-f) = pr1 is-equiv-f
pr2 (is-path-split-is-equiv f is-equiv-f) x y =
  pr1 (is-emb-is-equiv is-equiv-f x y)

is-coherently-invertible-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-split f → is-coherently-invertible f
pr1 ( is-coherently-invertible-is-path-split {A = A} {B = B} f
      ( pair (pair g issec-g) sec-ap-f)) = g
pr1 ( pr2
      ( is-coherently-invertible-is-path-split {A = A} {B = B} f
        ( pair (pair g issec-g) sec-ap-f))) = issec-g
pr2 ( pr2
      ( is-coherently-invertible-is-path-split {A = A} {B = B} f
        ( pair (pair g issec-g) sec-ap-f))) =
  φ ( λ x → pair
      ( pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
      ( pr2 (sec-ap-f (g (f x)) x) (issec-g (f x))))
  where
  φ : ((x : A) → fib (ap f) (issec-g (f x))) →
      Σ ( (g ∘ f) ~ id)
        ( λ H → (htpy-right-whisk issec-g f) ~ (htpy-left-whisk f H))
  φ = ( tot (λ H' → inv-htpy)) ∘
      ( λ s → pair (λ x → pr1 (s x)) (λ x → pr2 (s x)))

is-equiv-is-coherently-invertible :
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → is-coherently-invertible f → is-equiv f
is-equiv-is-coherently-invertible f (pair g (pair G (pair H K))) =
  is-equiv-has-inverse g G H

is-equiv-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-split f → is-equiv f
is-equiv-is-path-split f =
  ( is-equiv-is-coherently-invertible f) ∘
  ( is-coherently-invertible-is-path-split f)

is-coherently-invertible-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-coherently-invertible f
is-coherently-invertible-is-equiv f =
  ( is-coherently-invertible-is-path-split f) ∘ (is-path-split-is-equiv f)

swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
  Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
pr1 (pr1 (swap-total-Eq-structure B C D (pair (pair a b) (pair c d)))) = a
pr2 (pr1 (swap-total-Eq-structure B C D (pair (pair a b) (pair c d)))) = c
pr1 (pr2 (swap-total-Eq-structure B C D (pair (pair a b) (pair c d)))) = b
pr2 (pr2 (swap-total-Eq-structure B C D (pair (pair a b) (pair c d)))) = d

htpy-swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  ( ( swap-total-Eq-structure B C D) ∘
    ( swap-total-Eq-structure C B (λ x z y → D x y z))) ~ id
htpy-swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) = refl

is-equiv-swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  is-equiv (swap-total-Eq-structure B C D)
is-equiv-swap-total-Eq-structure B C D =
  is-equiv-has-inverse
    ( swap-total-Eq-structure C B (λ x z y → D x y z))
    ( htpy-swap-total-Eq-structure B C D)
    ( htpy-swap-total-Eq-structure C B (λ x z y → D x y z))

is-contr-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
is-contr-Σ {A = A} {B = B} is-contr-A is-contr-B =
  is-contr-equiv
    ( B (center is-contr-A))
    ( left-unit-law-Σ-is-contr is-contr-A (center is-contr-A))
    ( is-contr-B (center is-contr-A))

is-contr-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
is-contr-Σ' {A = A} {B} is-contr-A a is-contr-B =
  is-contr-equiv
    ( B a)
    ( left-unit-law-Σ-is-contr is-contr-A a)
    ( is-contr-B)

is-contr-total-Eq-structure :
  { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4) →
  ( is-contr-AC : is-contr (Σ A C)) →
  ( t : Σ A C) →
  is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
  is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
is-contr-total-Eq-structure
  {A = A} {B = B} {C = C} D is-contr-AC t is-contr-BD =
  is-contr-is-equiv
    ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
    ( swap-total-Eq-structure B C D)
    ( is-equiv-swap-total-Eq-structure B C D)
    ( is-contr-Σ' is-contr-AC t is-contr-BD)

IND-identity-system :
  {i j : Level} (k : Level) {A : UU i} (B : A → UU j) (a : A) (b : B a) → UU _
IND-identity-system k {A} B a b =
  ( P : (x : A) (y : B x) → UU k) →
    sec (λ (h : (x : A) (y : B x) → P x y) → h a b)

fam-Σ :
  {i j k : Level} {A : UU i} {B : A → UU j} (C : (x : A) → B x → UU k) →
  Σ A B → UU k
fam-Σ C (pair x y) = C x y

ind-identity-system :
  {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-contr-AB : is-contr (Σ A B)) (P : (x : A) → B x → UU k) →
  P a b → (x : A) (y : B x) → P x y
ind-identity-system a b is-contr-AB P p x y =
  tr ( fam-Σ P)
     ( eq-is-contr is-contr-AB)
     ( p)

comp-identity-system :
  {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-contr-AB : is-contr (Σ A B)) →
  (P : (x : A) → B x → UU k) (p : P a b) →
  Id (ind-identity-system a b is-contr-AB P p a b) p
comp-identity-system a b is-contr-AB P p =
  ap ( λ t → tr (fam-Σ P) t p)
     ( eq-is-contr'
       ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
       ( eq-is-contr is-contr-AB)
       ( refl))

Ind-identity-system :
  {i j : Level} (k : Level) {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-contr-AB : is-contr (Σ A B)) →
  IND-identity-system k B a b
pr1 (Ind-identity-system k a b is-contr-AB P) =
  ind-identity-system a b is-contr-AB P
pr2 (Ind-identity-system k a b is-contr-AB P) =
  comp-identity-system a b is-contr-AB P

is-contr-total-Eq-coprod-inl :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
  is-contr (Σ (coprod A B) (Eq-coprod A B (inl x)))
is-contr-total-Eq-coprod-inl A B x =
  is-contr-equiv
    ( coprod
      ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
      ( Σ B (λ y → Eq-coprod A B (inl x) (inr y))))
    ( right-distributive-Σ-coprod A B (Eq-coprod A B (inl x)))
    ( is-contr-equiv'
      ( coprod
        ( Σ A (Id x))
        ( Σ B (λ y → empty)))
      ( equiv-coprod
        ( equiv-tot (λ y → equiv-raise _ (Id x y)))
        ( equiv-tot (λ y → equiv-raise _ empty)))
      ( is-contr-equiv
        ( coprod (Σ A (Id x)) empty)
        ( equiv-coprod equiv-id (right-absorption-Σ B))
        ( is-contr-equiv'
          ( Σ A (Id x))
          ( inv-right-unit-law-coprod (Σ A (Id x)))
          ( is-contr-total-path x))))

is-contr-total-Eq-coprod-inr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
  is-contr (Σ (coprod A B) (Eq-coprod A B (inr x)))
is-contr-total-Eq-coprod-inr A B x =
  is-contr-equiv
    ( coprod
      ( Σ A (λ y → Eq-coprod A B (inr x) (inl y)))
      ( Σ B (λ y → Eq-coprod A B (inr x) (inr y))))
    ( right-distributive-Σ-coprod A B (Eq-coprod A B (inr x)))
    ( is-contr-equiv'
      ( coprod (Σ A (λ y → empty)) (Σ B (Id x)))
      ( equiv-coprod
        ( equiv-tot (λ y → equiv-raise _ empty))
        ( equiv-tot (λ y → equiv-raise _ (Id x y))))
      ( is-contr-equiv
        ( coprod empty (Σ B (Id x)))
        ( equiv-coprod (right-absorption-Σ A) equiv-id)
        ( is-contr-equiv'
          ( Σ B (Id x))
          ( inv-left-unit-law-coprod (Σ B (Id x)))
          ( is-contr-total-path x))))

is-equiv-Eq-eq-coprod-inl :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
  is-fiberwise-equiv (Eq-eq-coprod A B (inl x))
is-equiv-Eq-eq-coprod-inl A B x =
  fundamental-theorem-id
    ( inl x)
    ( reflexive-Eq-coprod A B (inl x))
    ( is-contr-total-Eq-coprod-inl A B x)
    ( Eq-eq-coprod A B (inl x))

is-equiv-Eq-eq-coprod-inr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
  is-fiberwise-equiv (Eq-eq-coprod A B (inr x))
is-equiv-Eq-eq-coprod-inr A B x =
  fundamental-theorem-id
    ( inr x)
    ( reflexive-Eq-coprod A B (inr x))
    ( is-contr-total-Eq-coprod-inr A B x)
    ( Eq-eq-coprod A B (inr x))

is-equiv-Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  (s : coprod A B) → is-fiberwise-equiv (Eq-eq-coprod A B s)
is-equiv-Eq-eq-coprod A B (inl x) = is-equiv-Eq-eq-coprod-inl A B x
is-equiv-Eq-eq-coprod A B (inr x) = is-equiv-Eq-eq-coprod-inr A B x

equiv-Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x y : coprod A B) →
  Id x y ≃ Eq-coprod A B x y
pr1 (equiv-Eq-eq-coprod A B x y) = Eq-eq-coprod A B x y
pr2 (equiv-Eq-eq-coprod A B x y) = is-equiv-Eq-eq-coprod A B x y

map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → Id (inl {B = B} x) (inl {B = B} x') → Id x x'
map-compute-eq-coprod-inl-inl x x' =
  ( map-inv-is-equiv (is-equiv-map-raise _ (Id x x'))) ∘
    ( Eq-eq-coprod _ _ (inl x) (inl x')) 

is-equiv-map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → is-equiv (map-compute-eq-coprod-inl-inl {B = B} x x')
is-equiv-map-compute-eq-coprod-inl-inl x x' =
  is-equiv-comp
    ( map-compute-eq-coprod-inl-inl x x')
    ( map-inv-is-equiv (is-equiv-map-raise _ (Id x x')))
    ( Eq-eq-coprod _ _ (inl x) (inl x'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inl x) (inl x'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ (Id x x')))

compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → (Id (inl {B = B} x) (inl x')) ≃ (Id x x')
pr1 (compute-eq-coprod-inl-inl x x') = map-compute-eq-coprod-inl-inl x x'
pr2 (compute-eq-coprod-inl-inl x x') =
  is-equiv-map-compute-eq-coprod-inl-inl x x'

map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → Id (inl x) (inr y') → empty
map-compute-eq-coprod-inl-inr x y' =
  ( map-inv-is-equiv (is-equiv-map-raise _ empty)) ∘
    ( Eq-eq-coprod _ _ (inl x) (inr y'))

is-equiv-map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → is-equiv (map-compute-eq-coprod-inl-inr x y')
is-equiv-map-compute-eq-coprod-inl-inr x y' =
  is-equiv-comp
    ( map-compute-eq-coprod-inl-inr x y')
    ( map-inv-is-equiv (is-equiv-map-raise _ empty))
    ( Eq-eq-coprod _ _ (inl x) (inr y'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inl x) (inr y'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ empty))
  
compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → (Id (inl x) (inr y')) ≃ empty
pr1 (compute-eq-coprod-inl-inr x y') = map-compute-eq-coprod-inl-inr x y'
pr2 (compute-eq-coprod-inl-inr x y') =
  is-equiv-map-compute-eq-coprod-inl-inr x y'

map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr {A = A} y) (inl x')) → empty
map-compute-eq-coprod-inr-inl y x' =
   ( map-inv-is-equiv (is-equiv-map-raise _ empty)) ∘
     ( Eq-eq-coprod _ _ (inr y) (inl x'))

is-equiv-map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → is-equiv (map-compute-eq-coprod-inr-inl y x')
is-equiv-map-compute-eq-coprod-inr-inl y x' =
  is-equiv-comp
    ( map-compute-eq-coprod-inr-inl y x')
    ( map-inv-is-equiv (is-equiv-map-raise _ empty))
    ( Eq-eq-coprod _ _ (inr y) (inl x'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inr y) (inl x'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ empty))

compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr y) (inl x')) ≃ empty
pr1 (compute-eq-coprod-inr-inl y x') = map-compute-eq-coprod-inr-inl y x'
pr2 (compute-eq-coprod-inr-inl y x') =
  is-equiv-map-compute-eq-coprod-inr-inl y x'

map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) → Id y y'
map-compute-eq-coprod-inr-inr y y' =
  ( map-inv-is-equiv (is-equiv-map-raise _ (Id y y'))) ∘
    ( Eq-eq-coprod _ _ (inr y) (inr y'))

is-equiv-map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → is-equiv (map-compute-eq-coprod-inr-inr {A = A} y y')
is-equiv-map-compute-eq-coprod-inr-inr y y' =
  is-equiv-comp
    ( map-compute-eq-coprod-inr-inr y y')
    ( map-inv-is-equiv (is-equiv-map-raise _ (Id y y')))
    ( Eq-eq-coprod _ _ (inr y) (inr y'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inr y) (inr y'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ (Id y y')))

compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) ≃ (Id y y')
pr1 (compute-eq-coprod-inr-inr y y') = map-compute-eq-coprod-inr-inr y y'
pr2 (compute-eq-coprod-inr-inr y y') =
  is-equiv-map-compute-eq-coprod-inr-inr y y'

map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  Σ A (λ x → C (f x)) → Σ B C
pr1 (map-Σ-map-base f C s) = f (pr1 s)
pr2 (map-Σ-map-base f C s) = pr2 s

fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib f (pr1 t) → fib (map-Σ-map-base f C) t
pr1 (pr1 (fib-map-Σ-map-base-fib f C (pair .(f x) z) (pair x refl))) = x
pr2 (pr1 (fib-map-Σ-map-base-fib f C (pair .(f x) z) (pair x refl))) = z
pr2 (fib-map-Σ-map-base-fib f C (pair .(f x) z) (pair x refl)) = refl

fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib (map-Σ-map-base f C) t → fib f (pr1 t)
pr1 ( fib-fib-map-Σ-map-base f C .(map-Σ-map-base f C (pair x z))
      ( pair (pair x z) refl)) = x
pr2 ( fib-fib-map-Σ-map-base f C .(map-Σ-map-base f C (pair x z))
      ( pair (pair x z) refl)) = refl

issec-fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-map-Σ-map-base-fib f C t) ∘ (fib-fib-map-Σ-map-base f C t)) ~ id
issec-fib-fib-map-Σ-map-base f C .(pair (f x) z) (pair (pair x z) refl) =
  refl

isretr-fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-fib-map-Σ-map-base f C t) ∘ (fib-map-Σ-map-base-fib f C t)) ~ id
isretr-fib-fib-map-Σ-map-base f C (pair .(f x) z) (pair x refl) = refl

is-equiv-fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → is-equiv (fib-map-Σ-map-base-fib f C t)
is-equiv-fib-map-Σ-map-base-fib f C t =
  is-equiv-has-inverse
    ( fib-fib-map-Σ-map-base f C t)
    ( issec-fib-fib-map-Σ-map-base f C t)
    ( isretr-fib-fib-map-Σ-map-base f C t)

equiv-fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → (fib f (pr1 t)) ≃ (fib (map-Σ-map-base f C) t)
pr1 (equiv-fib-map-Σ-map-base-fib f C t) = fib-map-Σ-map-base-fib f C t
pr2 (equiv-fib-map-Σ-map-base-fib f C t) = is-equiv-fib-map-Σ-map-base-fib f C t

is-contr-map-map-Σ-map-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
  is-contr-map f → is-contr-map (map-Σ-map-base f C)
is-contr-map-map-Σ-map-base C f is-contr-f (pair y z) =
  is-contr-is-equiv'
    ( fib f y)
    ( fib-map-Σ-map-base-fib f C (pair y z))
    ( is-equiv-fib-map-Σ-map-base-fib f C (pair y z))
    ( is-contr-f y)

is-equiv-map-Σ-map-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
  is-equiv f → is-equiv (map-Σ-map-base f C)
is-equiv-map-Σ-map-base C f is-equiv-f =
  is-equiv-is-contr-map
    ( is-contr-map-map-Σ-map-base C f (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ (map-equiv e)) ≃ Σ B C
pr1 (equiv-Σ-equiv-base C (pair f is-equiv-f)) = map-Σ-map-base f C
pr2 (equiv-Σ-equiv-base C (pair f is-equiv-f)) =
  is-equiv-map-Σ-map-base C f is-equiv-f

map-equiv-Fin-one-ℕ : Fin one-ℕ → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin one-ℕ
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin one-ℕ ≃ unit
pr1 equiv-Fin-one-ℕ = map-equiv-Fin-one-ℕ
pr2 equiv-Fin-one-ℕ = is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

is-contr-total-path' :
  {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id x a))
is-contr-total-path' a = is-contr-map-is-equiv is-equiv-id a
  
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fib f y)

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
  is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} (pair (pair g G) (pair h H)) =
    is-decidable-retract-of (pair f (pair h H))

  is-decidable-equiv :
    (e : A ≃ B) → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)

has-decidable-equality-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  has-decidable-equality B → has-decidable-equality A
has-decidable-equality-equiv e dB x y =
  is-decidable-equiv (equiv-ap e x y) (dB (map-equiv e x) (map-equiv e y))

has-decidable-equality-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  has-decidable-equality A → has-decidable-equality B
has-decidable-equality-equiv' e = has-decidable-equality-equiv (inv-equiv e)

fundamental-theorem-id-retr :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
  (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
  is-fiberwise-equiv i
fundamental-theorem-id-retr {_} {_} {A} {B} a i R =
  is-fiberwise-equiv-is-equiv-tot i
    ( is-equiv-is-contr (tot i)
      ( is-contr-retract-of (Σ _ (λ y → Id a y))
        ( pair (tot i)
          ( pair (tot λ x → pr1 (R x))
            ( ( inv-htpy (tot-comp i (λ x → pr1 (R x)))) ∙h
              ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
        ( is-contr-total-path a))
      ( is-contr-total-path a))

map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  Σ A C → Σ B D
pr1 (map-Σ D f g t) = f (pr1 t)
pr2 (map-Σ D f g t) = g (pr1 t) (pr2 t)

triangle-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  (map-Σ D f g) ~ ((map-Σ-map-base f D) ∘ (tot g))
triangle-map-Σ D f g t = refl

is-fiberwise-equiv-is-equiv-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  is-equiv f → is-equiv (map-Σ D f g) → is-fiberwise-equiv g
is-fiberwise-equiv-is-equiv-map-Σ
  D f g is-equiv-f is-equiv-map-Σ-fg =
  is-fiberwise-equiv-is-equiv-tot g
    ( is-equiv-right-factor
      ( map-Σ D f g)
      ( map-Σ-map-base f D)
      ( tot g)
      ( triangle-map-Σ D f g)
      ( is-equiv-map-Σ-map-base D f is-equiv-f)
      ( is-equiv-map-Σ-fg))

is-equiv-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  is-equiv f → (is-fiberwise-equiv g) →
  is-equiv (map-Σ D f g)
is-equiv-map-Σ
  D f g is-equiv-f is-fiberwise-equiv-g =
  is-equiv-comp
    ( map-Σ D f g)
    ( map-Σ-map-base f D)
    ( tot g)
    ( triangle-map-Σ D f g)
    ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
    ( is-equiv-map-Σ-map-base D f is-equiv-f)

equiv-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) →
  Σ A C ≃ Σ B D
pr1 (equiv-Σ D e g) = map-Σ D (map-equiv e) (λ x → map-equiv (g x))
pr2 (equiv-Σ D e g) =
  is-equiv-map-Σ D
    ( map-equiv e)
    ( λ x → map-equiv (g x))
    ( is-equiv-map-equiv e)
    ( λ x → is-equiv-map-equiv (g x))

is-equiv-top-is-equiv-left-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  is-equiv i → is-equiv f → is-equiv g → is-equiv h
is-equiv-top-is-equiv-left-square f g h i H is-equiv-i is-equiv-f is-equiv-g =
  is-equiv-right-factor (i ∘ f) g h H is-equiv-g
    ( is-equiv-comp' i f is-equiv-f is-equiv-i)

is-emb-htpy :
  {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
  is-emb g → is-emb f
is-emb-htpy f g H is-emb-g x y =
  is-equiv-top-is-equiv-left-square
    ( ap g)
    ( concat' (f x) (H y))
    ( ap f)
    ( concat (H x) (g y))
    ( htpy-nat H)
    ( is-equiv-concat (H x) (g y))
    ( is-emb-g x y)
    ( is-equiv-concat' (f x) (H y))

is-emb-htpy' :
  {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
  is-emb f → is-emb g
is-emb-htpy' f g H is-emb-f =
  is-emb-htpy g f (inv-htpy H) is-emb-f

is-emb-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
  is-emb h → is-emb f
is-emb-comp f g h H is-emb-g is-emb-h =
  is-emb-htpy f (g ∘ h) H
    ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
      ( is-emb-h x y)
      ( is-emb-g (h x) (h y)))

is-emb-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (g : B → X) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

comp-emb :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B ↪ C) → (A ↪ B) → (A ↪ C)
pr1 (comp-emb (pair g H) (pair f K)) = g ∘ f
pr2 (comp-emb (pair g H) (pair f K)) = is-emb-comp' g f H K

is-emb-inl :
  {i j : Level} (A : UU i) (B : UU j) → is-emb (inl {A = A} {B = B})
is-emb-inl A B x =
  fundamental-theorem-id x refl
    ( is-contr-is-equiv
      ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
      ( tot (λ y → Eq-eq-coprod A B (inl x) (inl y)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-Eq-eq-coprod A B (inl x) (inl y)))
      ( is-contr-equiv'
        ( Σ A (Id x))
        ( equiv-tot (λ y → equiv-raise _ (Id x y)))
        ( is-contr-total-path x)))
    ( λ y → ap inl)

emb-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ↪ coprod A B
pr1 (emb-inl {l1} {l2} {A} {B}) = inl
pr2 (emb-inl {l1} {l2} {A} {B}) = is-emb-inl A B

is-emb-inr :
  {i j : Level} (A : UU i) (B : UU j) → is-emb (inr {A = A} {B = B})
is-emb-inr A B x =
  fundamental-theorem-id x refl
    ( is-contr-is-equiv
      ( Σ B (λ y → Eq-coprod A B (inr x) (inr y)))
      ( tot (λ y → Eq-eq-coprod A B (inr x) (inr y)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-Eq-eq-coprod A B (inr x) (inr y)))
      ( is-contr-equiv'
        ( Σ B (Id x))
        ( equiv-tot (λ y → equiv-raise _ (Id x y)))
        ( is-contr-total-path x)))
    ( λ y → ap inr)

emb-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → B ↪ coprod A B
pr1 (emb-inr {l1} {l2} {A} {B}) = inr
pr2 (emb-inr {l1} {l2} {A} {B}) = is-emb-inr A B

is-emb-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f : A → C} {g : B → C} → is-emb f → is-emb g → ((a : A) (b : B) →
  ¬ (Id (f a) (g b))) → is-emb (ind-coprod (λ x → C) f g)
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inl a) (inl a') =
  is-equiv-left-factor
    ( ap f)
    ( ap (ind-coprod (λ x → C) f g))
    ( ap inl)
    ( λ p → ap-comp (ind-coprod (λ x → C) f g) inl p)
    ( H a a')
    ( is-emb-inl A B a a')
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inl a) (inr b') =
  is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a b')
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inr b) (inl a') =
  is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a' b ∘ inv)
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inr b) (inr b') =
  is-equiv-left-factor
    ( ap g)
    ( ap (ind-coprod (λ x → C) f g))
    ( ap inr)
    ( λ p → ap-comp (ind-coprod (λ x → C) f g) inr p)
    ( K b b')
    ( is-emb-inr A B b b')

is-emb-right-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
  is-emb f → is-emb h
is-emb-right-factor f g h H is-emb-g is-emb-f x y =
  is-equiv-right-factor
    ( ap (g ∘ h))
    ( ap g)
    ( ap h)
    ( ap-comp g h)
    ( is-emb-g (h x) (h y))
    ( is-emb-htpy (g ∘ h) f (inv-htpy H) is-emb-f x y)

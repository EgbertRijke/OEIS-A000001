{-# OPTIONS --without-K --exact-split #-}

module 02-equivalences where

open import 01-basics public

-- Equivalences

_~_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → UU (l1 ⊔ l2)
f ~ g = (x : _) → Id (f x) (g x)

refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
inv-htpy H x = inv (H x)

_∙h_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (h : (x : A) → B x) → (g ~ h) → (f ~ h)
concat-htpy H h K x = concat (H x) (h x) (K x)

square :
  {l1 : Level} {A : UU l1} {x y1 y2 z : A}
  (p-left : Id x y1) (p-bottom : Id y1 z)
  (p-top : Id x y2) (p-right : Id y2 z) → UU l1
square p-left p-bottom p-top p-right = Id (p-left ∙ p-bottom) (p-top ∙ p-right)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

sq-left-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq

left-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit

sec :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

retr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A → B)
map-equiv e = pr1 e

is-equiv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-equiv e)
is-equiv-map-equiv e = pr2 e

is-equiv-id :
  {i : Level} {A : UU i} → is-equiv (id {i} {A})
is-equiv-id = pair (pair id refl-htpy) (pair id refl-htpy)

equiv-id :
  {i : Level} {A : UU i} → A ≃ A
equiv-id = pair id is-equiv-id

has-inverse :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f =
  Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

is-equiv-has-inverse' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → is-equiv f
is-equiv-has-inverse' (pair g (pair H K)) = pair (pair g H) (pair g K)

is-equiv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
is-equiv-has-inverse g H K =
  is-equiv-has-inverse' (pair g (pair H K))

htpy-section-retraction :
  { i j : Level} {A : UU i} {B : UU j} {f : A → B}
  ( is-equiv-f : is-equiv f) →
  ( (pr1 (pr1 is-equiv-f))) ~ (pr1 (pr2 is-equiv-f))
htpy-section-retraction {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
    (inv-htpy (H ·r g)) ∙h (h ·l G)

has-inverse-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → has-inverse f
has-inverse-is-equiv {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
  let is-equiv-f = pair (pair g G) (pair h H) in
  pair g (pair G (((htpy-section-retraction is-equiv-f) ·r f) ∙h H))

map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
map-inv-is-equiv is-equiv-f = pr1 (has-inverse-is-equiv is-equiv-f)

issec-map-inv-is-equiv' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → (f ∘ (map-inv-is-equiv is-equiv-f)) ~ id
issec-map-inv-is-equiv' is-equiv-f = pr1 (pr2 (has-inverse-is-equiv is-equiv-f))

isretr-map-inv-is-equiv' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → ((map-inv-is-equiv is-equiv-f) ∘ f) ~ id
isretr-map-inv-is-equiv' is-equiv-f =
  pr2 (pr2 (has-inverse-is-equiv is-equiv-f))

is-equiv-map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → is-equiv (map-inv-is-equiv is-equiv-f)
is-equiv-map-inv-is-equiv {i} {j} {A} {B} {f} is-equiv-f =
  is-equiv-has-inverse f
    ( isretr-map-inv-is-equiv' is-equiv-f)
    ( issec-map-inv-is-equiv' is-equiv-f)

map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B → A)
map-inv-equiv' e = map-inv-is-equiv (is-equiv-map-equiv e)

issec-map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-equiv e) ∘ (map-inv-equiv' e)) ~ id
issec-map-inv-equiv' e = issec-map-inv-is-equiv' (is-equiv-map-equiv e)

isretr-map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-inv-equiv' e) ∘ (map-equiv e)) ~ id
isretr-map-inv-equiv' e = isretr-map-inv-is-equiv' (is-equiv-map-equiv e)

is-equiv-map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-inv-equiv' e)
is-equiv-map-inv-equiv e =
  is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B ≃ A)
inv-equiv e = pair (map-inv-equiv' e) (is-equiv-map-inv-equiv e)

triangle-section :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) →
  g ~ (f ∘ (pr1 S))
triangle-section f g h H (pair s issec) =
  inv-htpy (( H ·r s) ∙h (g ·l issec))

section-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec f → sec g
section-comp f g h H sec-h sec-f =
  pair (h ∘ (pr1 sec-f)) ((inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f))

section-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec g → sec f
section-comp' f g h H sec-h sec-g =
  pair
    ( (pr1 sec-h) ∘ (pr1 sec-g))
    ( ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
      ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g))))

triangle-retraction :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g) →
  h ~ ((pr1 R) ∘ f)
triangle-retraction f g h H (pair r isretr) =
  inv-htpy (( r ·l H) ∙h (isretr ·r h))

retraction-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr f → retr h
retraction-comp f g h H retr-g retr-f =
  pair
    ( (pr1 retr-f) ∘ g)
    ( (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f))

retraction-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr h → retr f
retraction-comp' f g h H retr-g retr-h =
  pair
    ( (pr1 retr-h) ∘ (pr1 retr-g))
    ( ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
      ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h)))

is-equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  is-equiv h → is-equiv g → is-equiv f
is-equiv-comp f g h H (pair sec-h retr-h) (pair sec-g retr-g) =
  pair
    ( section-comp' f g h H sec-h sec-g)
    ( retraction-comp' f g h H retr-g retr-h)

is-equiv-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
  is-equiv h → is-equiv g → is-equiv (g ∘ h)
is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
equiv-comp g h =
  pair ((pr1 g) ∘ (pr1 h)) (is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g))

_∘e_ :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
_∘e_ = equiv-comp

is-equiv-left-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  is-equiv f → is-equiv h → is-equiv g
is-equiv-left-factor f g h H
  ( pair sec-f retr-f)
  ( pair (pair sh sh-issec) retr-h) =
  pair
    ( section-comp f g h H (pair sh sh-issec) sec-f)
    ( retraction-comp' g f sh
      ( triangle-section f g h H (pair sh sh-issec))
      ( retr-f)
      ( pair h sh-issec))

is-equiv-left-factor' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
  is-equiv (g ∘ h) → is-equiv h → is-equiv g
is-equiv-left-factor' g h =
  is-equiv-left-factor (g ∘ h) g h refl-htpy

is-equiv-right-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  is-equiv g → is-equiv f → is-equiv h
is-equiv-right-factor f g h H
  ( pair sec-g (pair rg rg-isretr))
  ( pair sec-f retr-f) =
  pair
    ( section-comp' h rg f
      ( triangle-retraction f g h H (pair rg rg-isretr))
      ( sec-f)
      ( pair g rg-isretr))
    ( retraction-comp f g h H (pair rg rg-isretr) retr-f)

is-equiv-right-factor' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) → 
  is-equiv g → is-equiv (g ∘ h) → is-equiv h
is-equiv-right-factor' g h =
  is-equiv-right-factor (g ∘ h) g h refl-htpy

is-equiv-is-section-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
  is-equiv f → (f ∘ g) ~ id → is-equiv g
is-equiv-is-section-is-equiv {B = B} {f = f} {g = g} is-equiv-f H =
  is-equiv-right-factor id f g (inv-htpy H) is-equiv-f is-equiv-id

is-equiv-is-retraction-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
  is-equiv f  → (g ∘ f) ~ id → is-equiv g
is-equiv-is-retraction-is-equiv {A = A} {f = f} {g = g} is-equiv-f H =
  is-equiv-left-factor id g f (inv-htpy H) is-equiv-id is-equiv-f

inv-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

is-equiv-inv :
  {i : Level} {A : UU i} (x y : A) →
  is-equiv (λ (p : Id x y) → inv p)
is-equiv-inv x y =
  is-equiv-has-inverse inv inv-inv inv-inv

equiv-inv :
  {i : Level} {A : UU i} (x y : A) → (Id x y) ≃ (Id y x)
equiv-inv x y = pair inv (is-equiv-inv x y)

inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} →
  Id x y → B y → B x
inv-tr B p = tr B (inv p)

isretr-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
isretr-inv-tr B refl b = refl

issec-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
issec-inv-tr B refl b = refl

is-equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → is-equiv (tr B p)
is-equiv-tr B p =
  is-equiv-has-inverse
    ( inv-tr B p)
    ( issec-inv-tr B p)
    ( isretr-inv-tr B p)

equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → (B x) ≃ (B y)
equiv-tr B p = pair (tr B p) (is-equiv-tr B p)

Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → UU (i ⊔ j)
Eq-Σ {B = B} s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

reflexive-Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s : Σ A B) → Eq-Σ s s
reflexive-Eq-Σ (pair a b) = pair refl refl

pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Id s t) → Eq-Σ s t
pair-eq-Σ {s = s} refl = reflexive-Eq-Σ s

eq-pair-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
eq-pair-Σ {B = B} {pair x y} {pair .x .y} refl refl = refl

eq-pair-Σ' :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  Eq-Σ s t → Id s t
eq-pair-Σ' (pair α β) = eq-pair-Σ α β

isretr-pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((pair-eq-Σ {s = s} {t}) ∘ (eq-pair-Σ' {s = s} {t})) ~ id {A = Eq-Σ s t}
isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((eq-pair-Σ' {s = s} {t}) ∘ (pair-eq-Σ {s = s} {t})) ~ id
issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

is-equiv-eq-pair-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  is-equiv (eq-pair-Σ' {s = s} {t})
is-equiv-eq-pair-Σ s t =
  is-equiv-has-inverse
    ( pair-eq-Σ)
    ( issec-pair-eq-Σ s t)
    ( isretr-pair-eq-Σ s t)

equiv-eq-pair-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) → Eq-Σ s t ≃ Id s t
equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

is-equiv-pair-eq-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) →
  is-equiv (pair-eq-Σ {s = s} {t})
is-equiv-pair-eq-Σ s t =
  is-equiv-has-inverse
    ( eq-pair-Σ')
    ( isretr-pair-eq-Σ s t)
    ( issec-pair-eq-Σ s t)

equiv-pair-eq-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) → Id s t ≃ Eq-Σ s t
equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

η-pair :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (t : Σ A B) →
  Id (pair (pr1 t) (pr2 t)) t
η-pair t = eq-pair-Σ refl refl

Eq-prod :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) → UU (i ⊔ j)
Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))

eq-pair' :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Eq-prod s t → Id s t
eq-pair' {s = pair x y} {pair .x .y} (pair refl refl) = refl

eq-pair :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Id (pr1 s) (pr1 t) → Id (pr2 s) (pr2 t) → Id s t
eq-pair p q = eq-pair' (pair p q)

pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Id s t → Eq-prod s t
pair-eq α = pair (ap pr1 α) (ap pr2 α)

isretr-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  ((pair-eq {s = s} {t}) ∘ (eq-pair' {s = s} {t})) ~ id
isretr-pair-eq {s = pair x y} {pair .x .y} (pair refl refl) = refl

issec-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  ((eq-pair' {s = s} {t}) ∘ (pair-eq {s = s} {t})) ~ id
issec-pair-eq {s = pair x y} {pair .x .y} refl = refl

is-equiv-eq-pair :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  is-equiv (eq-pair' {s = s} {t})
is-equiv-eq-pair s t =
  is-equiv-has-inverse pair-eq issec-pair-eq isretr-pair-eq

equiv-eq-pair :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Eq-prod s t ≃ Id s t
equiv-eq-pair s t = pair eq-pair' (is-equiv-eq-pair s t)

is-equiv-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) →
  is-equiv (pair-eq {s = s} {t})
is-equiv-pair-eq s t =
  is-equiv-has-inverse eq-pair' isretr-pair-eq issec-pair-eq

equiv-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) →
  Id s t ≃ Eq-prod s t
equiv-pair-eq s t = pair pair-eq (is-equiv-pair-eq s t)

swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → prod A B → prod B A
swap-prod A B t = pair (pr2 t) (pr1 t)

swap-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-prod B A) ∘ (swap-prod A B)) ~ id
swap-swap-prod A B (pair x y) = refl

is-equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  is-equiv (swap-prod A B)
is-equiv-swap-prod A B =
  is-equiv-has-inverse
    ( swap-prod B A)
    ( swap-swap-prod B A)
    ( swap-swap-prod A B)

equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → (A × B) ≃ (B × A)
equiv-swap-prod A B = pair (swap-prod A B) (is-equiv-swap-prod A B)

triple :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (a : A) (b : B a) → C a b → Σ A (λ x → Σ (B x) (C x))
triple a b c = pair a (pair b c)

triple' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  (a : A) (b : B a) → C (pair a b) → Σ (Σ A B) C
triple' a b c = pair (pair a b) c

map-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
map-assoc-Σ A B C (pair (pair x y) z) = triple x y z

map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) → Σ (Σ A B) C
map-inv-assoc-Σ A B C t = triple' (pr1 t) (pr1 (pr2 t)) (pr2 (pr2 t))

isretr-map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((map-inv-assoc-Σ  A B C) ∘ (map-assoc-Σ A B C)) ~ id
isretr-map-inv-assoc-Σ A B C (pair (pair x y) z) = refl

issec-map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((map-assoc-Σ A B C) ∘ (map-inv-assoc-Σ A B C)) ~ id
issec-map-inv-assoc-Σ A B C (pair x (pair y z)) = refl

is-equiv-map-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → is-equiv (map-assoc-Σ A B C)
is-equiv-map-assoc-Σ A B C =
  is-equiv-has-inverse
    ( map-inv-assoc-Σ A B C)
    ( issec-map-inv-assoc-Σ A B C)
    ( isretr-map-inv-assoc-Σ A B C)

assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
assoc-Σ A B C =
  pair (map-assoc-Σ A B C) (is-equiv-map-assoc-Σ A B C)

inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) ≃ Σ (Σ A B) C
inv-assoc-Σ A B C =
  pair
    ( map-inv-assoc-Σ A B C)
    ( is-equiv-has-inverse
      ( map-assoc-Σ A B C)
      ( isretr-map-inv-assoc-Σ A B C)
      ( issec-map-inv-assoc-Σ A B C))

map-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A × B → B × A
map-commutative-prod A B (pair a b) = pair b a

map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → B × A → A × B
map-inv-commutative-prod A B = map-commutative-prod B A

issec-map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-commutative-prod A B ∘ map-inv-commutative-prod A B) ~ id
issec-map-inv-commutative-prod A B (pair b a) = refl

isretr-map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-inv-commutative-prod A B ∘ map-commutative-prod A B) ~ id
isretr-map-inv-commutative-prod A B (pair a b) = refl

is-equiv-map-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-equiv (map-commutative-prod A B)
is-equiv-map-commutative-prod A B =
  is-equiv-has-inverse
    ( map-inv-commutative-prod A B)
    ( issec-map-inv-commutative-prod A B)
    ( isretr-map-inv-commutative-prod A B)

commutative-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A × B) ≃ (B × A)
commutative-prod {l1} {l2} {A} {B} =
  pair (map-commutative-prod A B) (is-equiv-map-commutative-prod A B)

map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → coprod A B → A
map-right-unit-law-coprod-is-empty A B nb (inl a) = a
map-right-unit-law-coprod-is-empty A B nb (inr b) = ex-falso (nb b)

map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → coprod A B → B
map-left-unit-law-coprod-is-empty A B na (inl a) = ex-falso (na a)
map-left-unit-law-coprod-is-empty A B na (inr b) = b

map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → B → coprod A B
map-inv-left-unit-law-coprod-is-empty A B H = inr

issec-map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  ( map-left-unit-law-coprod-is-empty A B H ∘ map-inv-left-unit-law-coprod-is-empty A B H) ~ id
issec-map-inv-left-unit-law-coprod-is-empty A B H a = refl

isretr-map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  ( map-inv-left-unit-law-coprod-is-empty A B H ∘ map-left-unit-law-coprod-is-empty A B H) ~ id
isretr-map-inv-left-unit-law-coprod-is-empty A B H (inl a) = ex-falso (H a)
isretr-map-inv-left-unit-law-coprod-is-empty A B H (inr b) = refl

is-equiv-map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  is-equiv (map-left-unit-law-coprod-is-empty A B H)
is-equiv-map-left-unit-law-coprod-is-empty A B H =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-left-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-left-unit-law-coprod-is-empty A B H)

left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  coprod A B ≃ B
left-unit-law-coprod-is-empty A B H =
  pair (map-left-unit-law-coprod-is-empty A B H) (is-equiv-map-left-unit-law-coprod-is-empty A B H)

inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  B ≃ coprod A B
inv-left-unit-law-coprod-is-empty A B H =
  pair ( map-inv-left-unit-law-coprod-is-empty A B H)
       ( is-equiv-has-inverse
         ( map-left-unit-law-coprod-is-empty A B H)
         ( isretr-map-inv-left-unit-law-coprod-is-empty A B H)
         ( issec-map-inv-left-unit-law-coprod-is-empty A B H))

map-left-unit-law-coprod :
  {l : Level} (B : UU l) → coprod empty B → B
map-left-unit-law-coprod B =
  map-left-unit-law-coprod-is-empty empty B id

map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) → B → coprod empty B
map-inv-left-unit-law-coprod B = inr

issec-map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) →
  ( map-left-unit-law-coprod B ∘ map-inv-left-unit-law-coprod B) ~ id
issec-map-inv-left-unit-law-coprod B =
  issec-map-inv-left-unit-law-coprod-is-empty empty B id

isretr-map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) →
  ( map-inv-left-unit-law-coprod B ∘ map-left-unit-law-coprod B) ~ id
isretr-map-inv-left-unit-law-coprod B =
  isretr-map-inv-left-unit-law-coprod-is-empty empty B id

is-equiv-map-left-unit-law-coprod :
  {l : Level} (B : UU l) → is-equiv (map-left-unit-law-coprod B)
is-equiv-map-left-unit-law-coprod B =
  is-equiv-map-left-unit-law-coprod-is-empty empty B id

left-unit-law-coprod :
  {l : Level} (B : UU l) → coprod empty B ≃ B
left-unit-law-coprod B =
  left-unit-law-coprod-is-empty empty B id

inv-left-unit-law-coprod :
  {l : Level} (B : UU l) → B ≃ (coprod empty B)
inv-left-unit-law-coprod B =
  inv-left-unit-law-coprod-is-empty empty B id

map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → A → coprod A B
map-inv-right-unit-law-coprod-is-empty A B is-empty-B = inl

issec-map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  ( map-right-unit-law-coprod-is-empty A B H ∘ map-inv-right-unit-law-coprod-is-empty A B H) ~ id
issec-map-inv-right-unit-law-coprod-is-empty A B H a = refl

isretr-map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  ( map-inv-right-unit-law-coprod-is-empty A B H ∘ map-right-unit-law-coprod-is-empty A B H) ~ id
isretr-map-inv-right-unit-law-coprod-is-empty A B H (inl a) = refl
isretr-map-inv-right-unit-law-coprod-is-empty A B H (inr b) = ex-falso (H b)

is-equiv-map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  is-equiv (map-right-unit-law-coprod-is-empty A B H)
is-equiv-map-right-unit-law-coprod-is-empty A B H =
  is-equiv-has-inverse
    ( map-inv-right-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-right-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)

is-equiv-inl-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty B → is-equiv (inl {l1} {l2} {A} {B})
is-equiv-inl-is-empty A B H =
  is-equiv-has-inverse
    ( map-right-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-right-unit-law-coprod-is-empty A B H)

right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B →
  (coprod A B) ≃ A
right-unit-law-coprod-is-empty A B H =
  pair ( map-right-unit-law-coprod-is-empty A B H)
       ( is-equiv-map-right-unit-law-coprod-is-empty A B H)

inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B →
  A ≃ (coprod A B)
inv-right-unit-law-coprod-is-empty A B H =
  pair ( inl)
       ( is-equiv-has-inverse
         ( map-right-unit-law-coprod-is-empty A B H)
          ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)
         ( issec-map-inv-right-unit-law-coprod-is-empty A B H))

map-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → coprod A empty → A
map-right-unit-law-coprod A = map-right-unit-law-coprod-is-empty A empty id

map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → A → coprod A empty
map-inv-right-unit-law-coprod A = inl

issec-map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) →
  ( map-right-unit-law-coprod A ∘ map-inv-right-unit-law-coprod A) ~ id
issec-map-inv-right-unit-law-coprod A =
  issec-map-inv-right-unit-law-coprod-is-empty A empty id

isretr-map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) →
  ( map-inv-right-unit-law-coprod A ∘ map-right-unit-law-coprod A) ~ id
isretr-map-inv-right-unit-law-coprod A =
  isretr-map-inv-right-unit-law-coprod-is-empty A empty id

is-equiv-map-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → is-equiv (map-right-unit-law-coprod A)
is-equiv-map-right-unit-law-coprod A =
  is-equiv-map-right-unit-law-coprod-is-empty A empty id

right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → coprod A empty ≃ A
right-unit-law-coprod A =
  right-unit-law-coprod-is-empty A empty id

inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → A ≃ coprod A empty
inv-right-unit-law-coprod A =
  inv-right-unit-law-coprod-is-empty A empty id

htpy-map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g') →
  (map-coprod f g) ~ (map-coprod f' g')
htpy-map-coprod H K (inl x) = ap inl (H x)
htpy-map-coprod H K (inr y) = ap inr (K y)

id-map-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-coprod (id {A = A}) (id {A = B})) ~ id
id-map-coprod A B (inl x) = refl
id-map-coprod A B (inr x) = refl

compose-map-coprod :
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  (map-coprod (f' ∘ f) (g' ∘ g)) ~
  ((map-coprod f' g') ∘ (map-coprod f g))
compose-map-coprod f f' g g' (inl x) = refl
compose-map-coprod f f' g g' (inr y) = refl

is-equiv-map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f : A → A'} {g : B → B'} →
  is-equiv f → is-equiv g → is-equiv (map-coprod f g)
is-equiv-map-coprod {A = A} {B = B} {A' = A'} {B' = B'} {f = f} {g = g}
  (pair (pair sf issec-sf) (pair rf isretr-rf))
  (pair (pair sg issec-sg) (pair rg isretr-rg)) =
  pair
    ( pair
      ( map-coprod sf sg)
      ( ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
          ( htpy-map-coprod issec-sf issec-sg)) ∙h
        ( id-map-coprod A' B')))
    ( pair
      ( map-coprod rf rg)
      ( ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
          ( htpy-map-coprod isretr-rf isretr-rg)) ∙h
        ( id-map-coprod A B)))
  
equiv-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A ≃ A') → (B ≃ B') → ((coprod A B) ≃ (coprod A' B'))
equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f) =
  pair
    ( map-coprod e f)
    ( is-equiv-map-coprod is-equiv-e is-equiv-f)

map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C → coprod A (coprod B C)
map-assoc-coprod (inl (inl x)) = inl x
map-assoc-coprod (inl (inr x)) = inr (inl x)
map-assoc-coprod (inr x) = inr (inr x)

map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod A (coprod B C) → coprod (coprod A B) C
map-inv-assoc-coprod (inl x) = inl (inl x)
map-inv-assoc-coprod (inr (inl x)) = inl (inr x)
map-inv-assoc-coprod (inr (inr x)) = inr x

issec-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  ( map-assoc-coprod {A = A} {B} {C} ∘ map-inv-assoc-coprod) ~ id
issec-map-inv-assoc-coprod (inl x) = refl
issec-map-inv-assoc-coprod (inr (inl x)) = refl
issec-map-inv-assoc-coprod (inr (inr x)) = refl

isretr-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  ( map-inv-assoc-coprod ∘ map-assoc-coprod {A = A} {B} {C}) ~ id
isretr-map-inv-assoc-coprod (inl (inl x)) = refl
isretr-map-inv-assoc-coprod (inl (inr x)) = refl
isretr-map-inv-assoc-coprod (inr x) = refl

is-equiv-map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  is-equiv (map-assoc-coprod {A = A} {B} {C})
is-equiv-map-assoc-coprod =
  is-equiv-has-inverse
    map-inv-assoc-coprod
    issec-map-inv-assoc-coprod
    isretr-map-inv-assoc-coprod

is-equiv-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  is-equiv (map-inv-assoc-coprod {A = A} {B} {C})
is-equiv-map-inv-assoc-coprod =
  is-equiv-has-inverse
    map-assoc-coprod
    isretr-map-inv-assoc-coprod
    issec-map-inv-assoc-coprod

assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C ≃ coprod A (coprod B C)
assoc-coprod = pair map-assoc-coprod is-equiv-map-assoc-coprod

inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod A (coprod B C) ≃ coprod (coprod A B) C
inv-assoc-coprod = pair map-inv-assoc-coprod is-equiv-map-inv-assoc-coprod

coprod-Fin :
  (k l : ℕ) → coprod (Fin k) (Fin l) ≃ Fin (add-ℕ k l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) equiv-id) ∘e inv-assoc-coprod

map-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) → Σ (coprod A B) C →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
map-right-distributive-Σ-coprod A B C (pair (inl x) z) = inl (pair x z)
map-right-distributive-Σ-coprod A B C (pair (inr y) z) = inr (pair y z)

map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
map-inv-right-distributive-Σ-coprod A B C (inl (pair x z)) = pair (inl x) z
map-inv-right-distributive-Σ-coprod A B C (inr (pair y z)) = pair (inr y) z

issec-map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (map-right-distributive-Σ-coprod A B C) ∘
    (map-inv-right-distributive-Σ-coprod A B C)) ~ id
issec-map-inv-right-distributive-Σ-coprod A B C (inl (pair x z)) = refl
issec-map-inv-right-distributive-Σ-coprod A B C (inr (pair y z)) = refl

isretr-map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (map-inv-right-distributive-Σ-coprod A B C) ∘
    (map-right-distributive-Σ-coprod A B C)) ~ id
isretr-map-inv-right-distributive-Σ-coprod A B C (pair (inl x) z) = refl
isretr-map-inv-right-distributive-Σ-coprod A B C (pair (inr y) z) = refl

is-equiv-map-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  is-equiv (map-right-distributive-Σ-coprod A B C)
is-equiv-map-right-distributive-Σ-coprod A B C =
  is-equiv-has-inverse
    ( map-inv-right-distributive-Σ-coprod A B C)
    ( issec-map-inv-right-distributive-Σ-coprod A B C)
    ( isretr-map-inv-right-distributive-Σ-coprod A B C)

right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
right-distributive-Σ-coprod A B C =
  pair ( map-right-distributive-Σ-coprod A B C)
       ( is-equiv-map-right-distributive-Σ-coprod A B C)

issec-map-inv-raise :
  {l l1 : Level} {A : UU l1} (x : raise l A) →
  Id (map-raise (map-inv-raise x)) x
issec-map-inv-raise (map-raise x) = refl

isretr-map-inv-raise :
  {l l1 : Level} {A : UU l1} (x : A) → Id (map-inv-raise {l} (map-raise x)) x
isretr-map-inv-raise x = refl

is-equiv-map-raise :
  (l : Level) {l1 : Level} (A : UU l1) → is-equiv (map-raise {l} {l1} {A})
is-equiv-map-raise l A =
  is-equiv-has-inverse
    map-inv-raise
    ( issec-map-inv-raise)
    ( isretr-map-inv-raise {l})

equiv-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
equiv-raise l A = pair map-raise (is-equiv-map-raise l A)

equiv-raise-unit : (l : Level) → unit ≃ raise-unit l
equiv-raise-unit l = equiv-raise l unit

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty

Raise :
  (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
Raise l A = pair (raise l A) (equiv-raise l A)

is-equiv-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-empty B → is-equiv f
is-equiv-is-empty f H =
  is-equiv-has-inverse
    ( ex-falso ∘ H)
    ( λ y → ex-falso (H y))
    ( λ x → ex-falso (H (f x)))

is-equiv-is-empty' :
  {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
is-equiv-is-empty' f = is-equiv-is-empty f id

map-right-absorption-Σ :
  {l : Level} (A : UU l) → Σ A (λ x → empty) → empty
map-right-absorption-Σ A (pair x ())

map-right-absorption-prod = map-right-absorption-Σ

is-equiv-map-right-absorption-Σ :
  {l : Level} (A : UU l) → is-equiv (map-right-absorption-Σ A)
is-equiv-map-right-absorption-Σ A =
  is-equiv-is-empty' (map-right-absorption-Σ A)

is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ

right-absorption-Σ :
  {l : Level} (A : UU l) → Σ A (λ x → empty) ≃ empty
right-absorption-Σ A =
  pair (map-right-absorption-Σ A) (is-equiv-map-right-absorption-Σ A)

right-absorption-prod :
  {l : Level} (A : UU l) → (A × empty) ≃ empty
right-absorption-prod = right-absorption-Σ

map-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → Σ unit A → A star
map-left-unit-law-Σ A (pair star a) = a

map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → A star → Σ unit A
map-inv-left-unit-law-Σ A a = (pair star a)

issec-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) →
  ( map-left-unit-law-Σ A ∘ map-inv-left-unit-law-Σ A) ~ id
issec-map-inv-left-unit-law-Σ A a = refl

isretr-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) →
  ( map-inv-left-unit-law-Σ A ∘ map-left-unit-law-Σ A) ~ id
isretr-map-inv-left-unit-law-Σ A (pair star a) = refl

is-equiv-map-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → is-equiv (map-left-unit-law-Σ A)
is-equiv-map-left-unit-law-Σ A =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-Σ A)
    ( issec-map-inv-left-unit-law-Σ A)
    ( isretr-map-inv-left-unit-law-Σ A)

left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → Σ unit A ≃ A star
left-unit-law-Σ A =
  pair (map-left-unit-law-Σ A) (is-equiv-map-left-unit-law-Σ A)

is-equiv-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → is-equiv (map-inv-left-unit-law-Σ A)
is-equiv-map-inv-left-unit-law-Σ A =
  is-equiv-has-inverse
    ( map-left-unit-law-Σ A)
    ( isretr-map-inv-left-unit-law-Σ A)
    ( issec-map-inv-left-unit-law-Σ A)

map-left-unit-law-prod :
  {l : Level} (A : UU l) → unit × A → A
map-left-unit-law-prod A = pr2

map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) → A → unit × A
map-inv-left-unit-law-prod A = map-inv-left-unit-law-Σ (λ x → A)

issec-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) →
  ( map-left-unit-law-prod A ∘ map-inv-left-unit-law-prod A) ~ id
issec-map-inv-left-unit-law-prod A =
  issec-map-inv-left-unit-law-Σ (λ x → A)

isretr-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) →
  ( map-inv-left-unit-law-prod A ∘ map-left-unit-law-prod A) ~ id
isretr-map-inv-left-unit-law-prod A (pair star a) = refl

is-equiv-map-left-unit-law-prod :
  {l : Level} (A : UU l) → is-equiv (map-left-unit-law-prod A)
is-equiv-map-left-unit-law-prod A =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-prod A)
    ( issec-map-inv-left-unit-law-prod A)
    ( isretr-map-inv-left-unit-law-prod A)

left-unit-law-prod :
  {l : Level} (A : UU l) → (unit × A) ≃ A
left-unit-law-prod A =
  pair
    ( map-left-unit-law-prod A)
    ( is-equiv-map-left-unit-law-prod A)

is-equiv-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) → is-equiv (map-inv-left-unit-law-prod A)
is-equiv-map-inv-left-unit-law-prod A =
  is-equiv-has-inverse
    ( map-left-unit-law-prod A)
    ( isretr-map-inv-left-unit-law-prod A)
    ( issec-map-inv-left-unit-law-prod A)

inv-left-unit-law-prod :
  {l : Level} (A : UU l) → A ≃ (unit × A)
inv-left-unit-law-prod A =
  pair
    ( map-inv-left-unit-law-prod A)
    ( is-equiv-map-inv-left-unit-law-prod A)

map-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → A × unit → A
map-right-unit-law-prod = pr1

map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → A → A × unit
map-inv-right-unit-law-prod a = pair a star

issec-map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} →
  (map-right-unit-law-prod {A = A} ∘ map-inv-right-unit-law-prod {A = A}) ~ id
issec-map-inv-right-unit-law-prod a = refl

isretr-map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} →
  (map-inv-right-unit-law-prod {A = A} ∘ map-right-unit-law-prod {A = A}) ~ id
isretr-map-inv-right-unit-law-prod (pair a star) = refl

is-equiv-map-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → is-equiv (map-right-unit-law-prod {A = A})
is-equiv-map-right-unit-law-prod =
  is-equiv-has-inverse
    map-inv-right-unit-law-prod
    issec-map-inv-right-unit-law-prod
    isretr-map-inv-right-unit-law-prod

right-unit-law-prod : {l1 : Level} {A : UU l1} → (A × unit) ≃ A
right-unit-law-prod =
  pair map-right-unit-law-prod is-equiv-map-right-unit-law-prod

is-injective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-injective f
is-injective-is-equiv {l1} {l2} {A} {B} {f} H {x} {y} p =
  ( inv (isretr-map-inv-is-equiv' H x)) ∙
  ( ( ap (map-inv-is-equiv H) p) ∙
    ( isretr-map-inv-is-equiv' H y))

is-injective-map-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-injective (map-equiv e)
is-injective-map-equiv (pair f H) = is-injective-is-equiv H

is-injective-map-inv-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-injective (map-inv-equiv' e)
is-injective-map-inv-equiv e =
  is-injective-is-equiv (is-equiv-map-inv-equiv e)

map-left-absorption-Σ :
  {l : Level} (A : empty → UU l) → Σ empty A → empty
map-left-absorption-Σ A = pr1

map-left-absorption-prod :
  {l : Level} (A : UU l) → empty × A → empty
map-left-absorption-prod A = map-left-absorption-Σ (λ x → A)

is-equiv-map-left-absorption-Σ :
  {l : Level} (A : empty → UU l) → is-equiv (map-left-absorption-Σ A)
is-equiv-map-left-absorption-Σ A =
  is-equiv-is-empty' (map-left-absorption-Σ A)

is-equiv-map-left-absorption-prod :
  {l : Level} (A : UU l) → is-equiv (map-left-absorption-prod A)
is-equiv-map-left-absorption-prod A =
  is-equiv-map-left-absorption-Σ (λ x → A)

left-absorption-Σ :
  {l : Level} (A : empty → UU l) → Σ empty A ≃ empty
left-absorption-Σ A =
  pair (map-left-absorption-Σ A) (is-equiv-map-left-absorption-Σ A)

left-absorption-prod :
  {l : Level} (A : UU l) → (empty × A) ≃ empty
left-absorption-prod A = left-absorption-Σ (λ x → A)

map-prod-pr1 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
map-prod-pr1 f g (pair a b) = refl

map-prod-pr2 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
map-prod-pr2 f g (pair a b) = refl

map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl

map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k (pair a b) = refl

htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair (H a) (K b)

is-equiv-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) →
  is-equiv f → is-equiv g → is-equiv (map-prod f g)
is-equiv-map-prod f g
  ( pair (pair sf issec-sf) (pair rf isretr-rf))
  ( pair (pair sg issec-sg) (pair rg isretr-rg)) =
  pair
    ( pair
      ( map-prod sf sg)
      ( ( inv-htpy (map-prod-comp sf sg f g)) ∙h
        ( (htpy-map-prod issec-sf issec-sg) ∙h map-prod-id)))
    ( pair
      ( map-prod rf rg)
      ( ( inv-htpy (map-prod-comp f g rf rg)) ∙h
        ( (htpy-map-prod isretr-rf isretr-rg) ∙h map-prod-id)))

equiv-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
equiv-prod (pair f is-equiv-f) (pair g is-equiv-g) =
  pair (map-prod f g) (is-equiv-map-prod f g is-equiv-f is-equiv-g)

map-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  (coprod A B) × C → coprod (A × C) (B × C)
map-right-distributive-prod-coprod A B C =
  map-right-distributive-Σ-coprod A B (λ x → C)

map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  coprod (A × C) (B × C) → (coprod A B) × C
map-inv-right-distributive-prod-coprod A B C =
  map-inv-right-distributive-Σ-coprod A B (λ x → C)

issec-map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( (map-right-distributive-prod-coprod A B C) ∘
    (map-inv-right-distributive-prod-coprod A B C)) ~ id
issec-map-inv-right-distributive-prod-coprod A B C =
  issec-map-inv-right-distributive-Σ-coprod A B (λ x → C)

isretr-map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( (map-inv-right-distributive-prod-coprod A B C) ∘
    (map-right-distributive-prod-coprod A B C)) ~ id
isretr-map-inv-right-distributive-prod-coprod A B C =
  isretr-map-inv-right-distributive-Σ-coprod A B (λ x → C)

is-equiv-map-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  is-equiv (map-right-distributive-prod-coprod A B C)
is-equiv-map-right-distributive-prod-coprod A B C =
  is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)

right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ((coprod A B) × C) ≃ coprod (A × C) (B × C)
right-distributive-prod-coprod A B C =
  right-distributive-Σ-coprod A B (λ x → C)

prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (mul-ℕ k l)
prod-Fin zero-ℕ l = left-absorption-prod (Fin l)
prod-Fin (succ-ℕ k) l =
  ( ( coprod-Fin (mul-ℕ k l) l) ∘e
    ( equiv-coprod (prod-Fin k l) (left-unit-law-prod (Fin l)))) ∘e
  ( right-distributive-prod-coprod (Fin k) unit (Fin l))

Fin-mul-ℕ : (k l : ℕ) → (Fin (mul-ℕ k l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = inv-equiv (prod-Fin k l)

is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv {f = f} {g} i j H K =
  is-equiv-right-factor'
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-comp
      ( map-equiv j ∘ f)
      ( g)
      ( map-equiv i)
      ( H)
      ( is-equiv-map-equiv i)
      ( K))

is-equiv-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv f → is-equiv g
is-equiv-equiv' {f = f} {g} i j H K =
  is-equiv-left-factor'
    ( g)
    ( map-equiv i)
    ( is-equiv-comp
      ( g ∘ map-equiv i)
      ( map-equiv j)
      ( f)
      ( inv-htpy H)
      ( K)
      ( is-equiv-map-equiv j))
    ( is-equiv-map-equiv i)

concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z → Id x y → Id x z
concat' x q p = p ∙ q

inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z →
  Id x z → Id x y
inv-concat' x q = concat' x (inv q)

isretr-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((inv-concat' x q) ∘ (concat' x q)) ~ id
isretr-inv-concat' x refl refl = refl

issec-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((concat' x q) ∘ (inv-concat' x q)) ~ id
issec-inv-concat' x refl refl = refl

is-equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  is-equiv (concat' x q)
is-equiv-concat' x q =
  is-equiv-has-inverse
    ( inv-concat' x q)
    ( issec-inv-concat' x q)
    ( isretr-inv-concat' x q)

equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  Id x y ≃ Id x z
equiv-concat' x q = pair (concat' x q) (is-equiv-concat' x q)

inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  (Id x z) → (Id y z)
inv-concat p = concat (inv p)

isretr-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((inv-concat p z) ∘ (concat p z)) ~ id
isretr-inv-concat refl z q = refl

issec-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((concat p z) ∘ (inv-concat p z)) ~ id
issec-inv-concat refl z refl = refl

is-equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  is-equiv (concat p z)
is-equiv-concat p z =
  is-equiv-has-inverse
    ( inv-concat p z)
    ( issec-inv-concat p z)
    ( isretr-inv-concat p z)

equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  Id y z ≃ Id x z
equiv-concat p z = pair (concat p z) (is-equiv-concat p z)

convert-eq-values-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → Id (f x) (f y) ≃ Id (g x) (g y)
convert-eq-values-htpy {f = f} {g} H x y =
  ( equiv-concat' (g x) (H y)) ∘e (equiv-concat (inv (H x)) (f y))

is-equiv-htpy :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} (g : A → B) →
  f ~ g → is-equiv g → is-equiv f
is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)) =
  pair
    ( pair gs ((H ·r gs) ∙h issec))
    ( pair gr ((gr ·l H) ∙h isretr))

is-equiv-htpy-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} (e : A ≃ B) →
  f ~ map-equiv e → is-equiv f
is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

map-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ A (λ x → coprod (B x) (C x)) → coprod (Σ A B) (Σ A C)
map-left-distributive-Σ-coprod A B C (pair x (inl y)) = inl (pair x y)
map-left-distributive-Σ-coprod A B C (pair x (inr z)) = inr (pair x z)

map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  coprod (Σ A B) (Σ A C) → Σ A (λ x → coprod (B x) (C x))
map-inv-left-distributive-Σ-coprod A B C (inl (pair x y)) = pair x (inl y)
map-inv-left-distributive-Σ-coprod A B C (inr (pair x z)) = pair x (inr z)

issec-map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ( ( map-left-distributive-Σ-coprod A B C) ∘
    ( map-inv-left-distributive-Σ-coprod A B C)) ~ id
issec-map-inv-left-distributive-Σ-coprod A B C (inl (pair x y)) = refl
issec-map-inv-left-distributive-Σ-coprod A B C (inr (pair x z)) = refl

isretr-map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ( ( map-inv-left-distributive-Σ-coprod A B C) ∘
    ( map-left-distributive-Σ-coprod A B C)) ~ id
isretr-map-inv-left-distributive-Σ-coprod A B C (pair x (inl y)) = refl
isretr-map-inv-left-distributive-Σ-coprod A B C (pair x (inr z)) = refl

is-equiv-map-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  is-equiv (map-left-distributive-Σ-coprod A B C)
is-equiv-map-left-distributive-Σ-coprod A B C =
  is-equiv-has-inverse
    ( map-inv-left-distributive-Σ-coprod A B C)
    ( issec-map-inv-left-distributive-Σ-coprod A B C)
    ( isretr-map-inv-left-distributive-Σ-coprod A B C)

left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ A (λ x → coprod (B x) (C x)) ≃ coprod (Σ A B) (Σ A C)
left-distributive-Σ-coprod A B C =
  pair ( map-left-distributive-Σ-coprod A B C)
       ( is-equiv-map-left-distributive-Σ-coprod A B C)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  map-left-swap-Σ t = pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))
  
  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  map-inv-left-swap-Σ t = pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))
  
  isretr-map-inv-left-swap-Σ : (map-inv-left-swap-Σ ∘ map-left-swap-Σ) ~ id
  isretr-map-inv-left-swap-Σ (pair x (pair y z)) = refl

  issec-map-inv-left-swap-Σ : (map-left-swap-Σ ∘ map-inv-left-swap-Σ) ~ id
  issec-map-inv-left-swap-Σ (pair x (pair y z)) = refl
  
  is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
  is-equiv-map-left-swap-Σ =
    is-equiv-has-inverse
      ( map-inv-left-swap-Σ)
      ( issec-map-inv-left-swap-Σ)
      ( isretr-map-inv-left-swap-Σ)
  
  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  equiv-left-swap-Σ = pair map-left-swap-Σ is-equiv-map-left-swap-Σ

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  map-right-swap-Σ t = pair (pair (pr1 (pr1 t)) (pr2 t)) (pr2 (pr1 t))

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  map-inv-right-swap-Σ t = pair (pair (pr1 (pr1 t)) (pr2 t)) (pr2 (pr1 t))

  issec-map-inv-right-swap-Σ : (map-right-swap-Σ ∘ map-inv-right-swap-Σ) ~ id
  issec-map-inv-right-swap-Σ (pair (pair x y) z) = refl

  isretr-map-inv-right-swap-Σ : (map-inv-right-swap-Σ ∘ map-right-swap-Σ) ~ id
  isretr-map-inv-right-swap-Σ (pair (pair x z) y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-has-inverse
      map-inv-right-swap-Σ
      issec-map-inv-right-swap-Σ
      isretr-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  equiv-right-swap-Σ = pair map-right-swap-Σ is-equiv-map-right-swap-Σ


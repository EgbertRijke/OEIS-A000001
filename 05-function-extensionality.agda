{-# OPTIONS --without-K --exact-split #-}

module 05-function-extensionality where

open import 04-truncation-levels public

htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = refl-htpy

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

WEAK-FUNEXT-FUNEXT :
  {l1 l2 : Level} →
  ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
  ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
pr1 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) x = center (is-contr-B x)
pr2 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) f =
  map-inv-is-equiv
    ( funext A B (λ x → center (is-contr-B x)) f)
    ( λ x → contraction (is-contr-B x) (f x))

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) ≃ (f ~ g)
pr1 (equiv-funext {f = f} {g}) = htpy-eq
pr2 (equiv-funext {f = f} {g}) = funext f g

eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → Id f g
eq-htpy = map-inv-is-equiv (funext _ _)
  
issec-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
issec-eq-htpy = issec-map-inv-is-equiv (funext _ _)
  
isretr-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
isretr-eq-htpy = isretr-map-inv-is-equiv (funext _ _)

is-equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j}
  (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext _ _)

eq-htpy-refl-htpy :
  {i j : Level} {A : UU i} {B : A → UU j}
  (f : (x : A) → B x) → Id (eq-htpy (refl-htpy {f = f})) refl
eq-htpy-refl-htpy f = isretr-eq-htpy refl

equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) ≃ Id f g
pr1 (equiv-eq-htpy {f = f} {g}) = eq-htpy
pr2 (equiv-eq-htpy {f = f} {g}) = is-equiv-eq-htpy f g

ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-refl-htpy f C)

is-contr-total-htpy-FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
  FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy-FUNEXT f funext-f =
  fundamental-theorem-id' f refl-htpy (λ g → htpy-eq {g = g}) funext-f

IND-HTPY-FUNEXT :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
  FUNEXT f → IND-HTPY {l3 = l3} f
IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
  Ind-identity-system l3 f
    ( refl-htpy)
    ( is-contr-total-htpy-FUNEXT f funext-f)

Ind-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
  IND-HTPY {l3 = l3} f
Ind-htpy f = IND-HTPY-FUNEXT f (funext f)
  
ind-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g
  
comp-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  (c : C f refl-htpy) →
  Id (ind-htpy f C c refl-htpy) c
comp-htpy f C = pr2 (Ind-htpy f C)

is-contr-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B

is-trunc-Π :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
  is-trunc-is-equiv k (f ~ g) htpy-eq
    ( funext f g)
    ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

is-prop-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-prop ((x : A) → B x)
is-prop-Π = is-trunc-Π neg-one-𝕋

type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop A P = (x : A) → type-Prop (P x)

is-prop-type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → is-prop (type-Π-Prop A P)
is-prop-type-Π-Prop A P = is-prop-Π (λ x → is-prop-type-Prop (P x))

Π-Prop :
  {l1 l2 : Level} (A : UU l1) →
  (A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
pr1 (Π-Prop A P) = type-Π-Prop A P
pr2 (Π-Prop A P) = is-prop-type-Π-Prop A P

type-function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-trunc-function-type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k B → is-trunc k (A → B)
is-trunc-function-type k {A} {B} is-trunc-B =
  is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)
                                          
is-prop-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop B → is-prop (A → B)
is-prop-function-type = is-trunc-function-type neg-one-𝕋

is-set-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set B → is-set (A → B)
is-set-function-type = is-trunc-function-type zero-𝕋

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : UU-Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop A P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (function-Prop A P) = type-function-Prop A P
pr2 (function-Prop A P) = is-prop-type-function-Prop A P

type-hom-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop P Q = type-function-Prop (type-Prop P) Q

is-prop-type-hom-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-type-hom-Prop P Q = is-prop-type-function-Prop (type-Prop P) Q

hom-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (hom-Prop P Q) = type-hom-Prop P Q
pr2 (hom-Prop P Q) = is-prop-type-hom-Prop P Q

is-prop-Π' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-prop ({x : A} → B x)
is-prop-Π' {l1} {l2} {A} {B} H =
  is-prop-equiv
    ( (x : A) → B x)
    ( pair
      ( λ f x → f {x})
      ( is-equiv-has-inverse
        ( λ g {x} → g x)
        ( refl-htpy)
        ( refl-htpy)))
    ( is-prop-Π H)

is-set-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
is-set-Π = is-trunc-Π zero-𝕋

is-contr-total-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
  is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
pr1 (pr1 (is-contr-total-htpy f)) = f
pr2 (pr1 (is-contr-total-htpy f)) = refl-htpy
pr2 (is-contr-total-htpy f) t =
  ( inv
    ( contraction
      ( is-contr-total-htpy-FUNEXT f (funext f))
      ( pair f refl-htpy))) ∙
  ( contraction (is-contr-total-htpy-FUNEXT f (funext f)) t)

Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Π-total-fam {A = A} {B} C = (x : A) → Σ (B x) (C x)

type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
type-choice-∞ {A = A} {B} C = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-type-choice-∞ {A = A} {B} C t t' =
  type-choice-∞
    ( λ (x : A) (p : Id ((pr1 t) x) ((pr1 t') x)) →
      Id (tr (C x) p ((pr2 t) x)) ((pr2 t') x))

reflexive-Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : type-choice-∞ C) → Eq-type-choice-∞ C t t
pr1 (reflexive-Eq-type-choice-∞ C (pair f g)) = refl-htpy
pr2 (reflexive-Eq-type-choice-∞ C (pair f g)) = refl-htpy

Eq-type-choice-∞-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → Id t t' → Eq-type-choice-∞ C t t'
Eq-type-choice-∞-eq C t .t refl = reflexive-Eq-type-choice-∞ C t

is-contr-total-Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : type-choice-∞ C) →
  is-contr (Σ (type-choice-∞ C) (Eq-type-choice-∞ C t))
is-contr-total-Eq-type-choice-∞ {A = A} {B} C t =
  is-contr-total-Eq-structure
    ( λ f g H → (x : A) → Id (tr (C x) (H x) ((pr2 t) x)) (g x))
    ( is-contr-total-htpy (pr1 t))
    ( pair (pr1 t) refl-htpy)
    ( is-contr-total-htpy (pr2 t))
  
is-equiv-Eq-type-choice-∞-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → is-equiv (Eq-type-choice-∞-eq C t t')
is-equiv-Eq-type-choice-∞-eq C t =
  fundamental-theorem-id t
    ( reflexive-Eq-type-choice-∞ C t)
    ( is-contr-total-Eq-type-choice-∞ C t)
    ( Eq-type-choice-∞-eq C t)

eq-Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  {t t' : type-choice-∞ C} → Eq-type-choice-∞ C t t' → Id t t'
eq-Eq-type-choice-∞ C {t} {t'} =
  map-inv-is-equiv (is-equiv-Eq-type-choice-∞-eq C t t')

choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C → type-choice-∞ C
pr1 (choice-∞ φ) x = pr1 (φ x)
pr2 (choice-∞ φ) x = pr2 (φ x)

inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  type-choice-∞ C → Π-total-fam C
pr1 (inv-choice-∞ ψ x) = pr1 ψ x
pr2 (inv-choice-∞ ψ x) = pr2 ψ x

issec-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( choice-∞ {A = A} {B = B} {C = C}) ∘
    ( inv-choice-∞ {A = A} {B = B} {C = C})) ~ id
issec-inv-choice-∞ {A = A} {C = C} (pair ψ ψ') =
  eq-Eq-type-choice-∞ C (pair refl-htpy refl-htpy)

isretr-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( inv-choice-∞ {A = A} {B = B} {C = C}) ∘
    ( choice-∞ {A = A} {B = B} {C = C})) ~ id
isretr-inv-choice-∞ φ =
  eq-htpy (λ x → eq-pair-Σ refl refl)

is-equiv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  is-equiv (choice-∞ {A = A} {B = B} {C = C})
is-equiv-choice-∞ {A = A} {B = B} {C = C} =
  is-equiv-has-inverse
    ( inv-choice-∞ {A = A} {B = B} {C = C})
    ( issec-inv-choice-∞ {A = A} {B = B} {C = C})
    ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-choice-∞ :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ type-choice-∞ C
pr1 equiv-choice-∞ = choice-∞
pr2 equiv-choice-∞ = is-equiv-choice-∞

distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ type-choice-∞ C
distributive-Π-Σ = equiv-choice-∞

is-equiv-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  is-equiv (inv-choice-∞ {A = A} {B = B} {C = C})
is-equiv-inv-choice-∞ {A = A} {B = B} {C = C} =
  is-equiv-has-inverse
    ( choice-∞ {A = A} {B = B} {C = C})
    ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})
    ( issec-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
pr1 (equiv-inv-choice-∞ C) = inv-choice-∞
pr2 (equiv-inv-choice-∞ C) = is-equiv-inv-choice-∞

inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
inv-distributive-Π-Σ = equiv-inv-choice-∞

is-equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  is-equiv (ev-pair {C = C})
pr1 (pr1 is-equiv-ev-pair) = ind-Σ
pr2 (pr1 is-equiv-ev-pair) = refl-htpy
pr1 (pr2 is-equiv-ev-pair) = ind-Σ
pr2 (pr2 is-equiv-ev-pair) f = eq-htpy (ind-Σ (λ x y → refl))

equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (pair a b))
pr1 equiv-ev-pair = ev-pair
pr2 equiv-ev-pair = is-equiv-ev-pair

precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

is-equiv-precomp-Π-is-coherently-invertible :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-coherently-invertible f →
  (C : B → UU l3) → is-equiv (precomp-Π f C)
is-equiv-precomp-Π-is-coherently-invertible f
  ( pair g (pair issec-g (pair isretr-g coh))) C = 
  is-equiv-has-inverse
    (λ s y → tr C (issec-g y) (s (g y)))
    ( λ s → eq-htpy (λ x → 
      ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
      ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
        ( apd s (isretr-g x)))))
    ( λ s → eq-htpy λ y → apd s (issec-g y))

is-equiv-precomp-Π-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
  (C : B → UU l3) → is-equiv (precomp-Π f C)
is-equiv-precomp-Π-is-equiv f is-equiv-f =
  is-equiv-precomp-Π-is-coherently-invertible f
    ( is-coherently-invertible-is-path-split f
      ( is-path-split-is-equiv f is-equiv-f))

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) =
  is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C

ind-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
  ((x : A) → C (f x)) → ((y : B) → C y)
ind-is-equiv C f is-equiv-f =
  map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)
  
comp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
  Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
comp-is-equiv C f is-equiv-f h =
  issec-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h
  
htpy-comp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f)
  (h : (x : A) → C (f x)) →
  (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) ~ h
htpy-comp-is-equiv C f is-equiv-f h = htpy-eq (comp-is-equiv C f is-equiv-f h)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)

is-equiv-precomp-is-equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
  ((C : UU l3) → is-equiv (precomp f C))
is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
  is-equiv-precomp-Π-f (λ y → C)

is-equiv-precomp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
  (C : UU l3) → is-equiv (precomp f C)
is-equiv-precomp-is-equiv f is-equiv-f =
  is-equiv-precomp-is-equiv-precomp-Π f
    ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
pr1 (equiv-precomp e C) = precomp (map-equiv e) C
pr2 (equiv-precomp e C) =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C

is-equiv-is-equiv-precomp-subuniverse :
  { l1 l2 : Level}
  ( α : Level → Level) (P : (l : Level) → UU l → UU (α l))
  ( A : Σ (UU l1) (P l1)) (B : Σ (UU l2) (P l2)) (f : pr1 A → pr1 B) →
  ( (l : Level) (C : Σ (UU l) (P l)) →
    is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-subuniverse α P A B f is-equiv-precomp-f =
  let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f _ A) id) in
  is-equiv-has-inverse
    ( pr1 retr-f)
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
               ( pair
                 ( f ∘ (pr1 retr-f))
                 ( ap (λ (g : pr1 A → pr1 A) → f ∘ g) (pr2 retr-f)))
               ( pair id refl))))
    ( htpy-eq (pr2 retr-f))

is-equiv-is-equiv-precomp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ((l : Level) (C : UU l) → is-equiv (precomp f C)) → is-equiv f
is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
  is-equiv-is-equiv-precomp-subuniverse
    ( const Level Level lzero)
    ( λ l X → unit)
    ( pair A star)
    ( pair B star)
    ( f)
    ( λ l C → is-equiv-precomp-f l (pr1 C))

is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : UU-Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : UU-Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : UU-Truncated-Type k l1) (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : UU-Truncated-Type k l) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-trunc k) A B f
      ( λ l → H {l})

postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X → Y) → (A → X) → (A → Y)
postcomp A f h = f ∘ h

map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
map-Π f h i = f i (h i)

htpy-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  (map-Π f) ~ (map-Π f')
htpy-map-Π H h = eq-htpy (λ i → H i (h i))

map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) → 
  ((i : I) → A i → B i) → ((j : J) → A (α j)) → ((j : J) → B (α j))
map-Π' α f = map-Π (λ j → f (α j))

htpy-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) {f f' : (i : I) → A i → B i} →
  ((i : I) → (f i) ~ (f' i)) → (map-Π' α f ~ map-Π' α f')
htpy-map-Π' α H = htpy-map-Π (λ j → H (α j))

equiv-fib-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fib (f i) (h i)) ≃ fib (map-Π f) h
equiv-fib-map-Π f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e equiv-choice-∞

is-trunc-map-map-Π :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
is-trunc-map-map-Π k {I = I} f H h =
  is-trunc-equiv' k
    ( (i : I) → fib (f i) (h i))
    ( equiv-fib-map-Π f h)
    ( is-trunc-Π k (λ i → H i (h i)))

is-equiv-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (is-equiv-f : is-fiberwise-equiv f) →
  is-equiv (map-Π f)
is-equiv-map-Π f is-equiv-f =
  is-equiv-is-contr-map
    ( is-trunc-map-map-Π neg-two-𝕋 f
      ( λ i → is-contr-map-is-equiv (is-equiv-f i)))

equiv-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
pr1 (equiv-map-Π e) = map-Π (λ i → map-equiv (e i))
pr2 (equiv-map-Π e) = is-equiv-map-Π _ (λ i → is-equiv-map-equiv (e i))

module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where
  
  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π =
    ( map-Π
      ( λ a →
        ( tr B (issec-map-inv-equiv e a)) ∘
        ( map-equiv (f (map-inv-equiv e a))))) ∘
    ( precomp-Π (map-inv-equiv e) B')

  compute-map-equiv-Π :
    (h : (a' : A') → B' a') (a' : A') →
    Id ( map-equiv-Π h (map-equiv e a')) (map-equiv (f a') (h a'))
  compute-map-equiv-Π h a' =
    ( ap
      ( λ t →
        tr B t ( map-equiv
                 ( f (map-inv-equiv e (map-equiv e a')))
                 ( h (map-inv-equiv e (map-equiv e a')))))
      ( coherence-map-inv-equiv e a')) ∙
    ( ( tr-ap
        ( map-equiv e)
        ( λ _ → id)
        ( isretr-map-inv-equiv e a')
        ( map-equiv
          ( f (map-inv-equiv e (map-equiv e a')))
          ( h (map-inv-equiv e (map-equiv e a'))))) ∙
      ( α ( map-inv-equiv e (map-equiv e a'))
          ( isretr-map-inv-equiv e a')))
    where
    α : (x : A') (p : Id x a') →
        Id ( tr (B ∘ map-equiv e) p (map-equiv (f x) (h x)))
           ( map-equiv (f a') (h a'))
    α x refl = refl

  is-equiv-map-equiv-Π : is-equiv map-equiv-Π
  is-equiv-map-equiv-Π =
    is-equiv-comp'
      ( map-Π (λ a →
        ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
        ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
      ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
      ( is-equiv-precomp-Π-is-equiv
        ( map-inv-is-equiv (is-equiv-map-equiv e))
        ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
        ( B'))
      ( is-equiv-map-Π _
        ( λ a → is-equiv-comp'
          ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))
          ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-map-equiv
            ( f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))))

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  pr1 equiv-Π = map-equiv-Π
  pr2 equiv-Π = is-equiv-map-equiv-Π

id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (equiv-id {A = A}) (λ a → equiv-id {A = B a})) ~ id
id-map-equiv-Π B = refl-htpy

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ev-inl-inr :
    {l3 : Level} (P : coprod A B → UU l3) →
    ((t : coprod A B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  pr1 (ev-inl-inr P s) x = s (inl x)
  pr2 (ev-inl-inr P s) y = s (inr y)

  dependent-universal-property-coprod :
    {l3 : Level} (P : coprod A B → UU l3) → is-equiv (ev-inl-inr P)
  dependent-universal-property-coprod P =
    is-equiv-has-inverse
      ( λ p → ind-coprod P (pr1 p) (pr2 p))
      ( ind-Σ (λ f g → eq-pair refl refl))
      ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

  equiv-dependent-universal-property-coprod :
    {l3 : Level} (P : coprod A B → UU l3) →
    ((x : coprod A B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  pr1 (equiv-dependent-universal-property-coprod P) = ev-inl-inr P
  pr2 (equiv-dependent-universal-property-coprod P) =
    dependent-universal-property-coprod P
  
  universal-property-coprod :
    {l3 : Level} (X : UU l3) →
    is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
  universal-property-coprod X = dependent-universal-property-coprod (λ t → X)
  
  equiv-universal-property-coprod :
    {l3 : Level} (X : UU l3) →
    (coprod A B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coprod X =
    equiv-dependent-universal-property-coprod (λ t → X)
  
  uniqueness-coprod :
    {l3 : Level} {Y : UU l3} (i : A → Y) (j : B → Y) →
    ((l : Level) (X : UU l) →
      is-equiv (λ (s : Y → X) → pair' (s ∘ i) (s ∘ j))) →
    is-equiv (ind-coprod (λ t → Y) i j)
  uniqueness-coprod {Y = Y} i j H =
    is-equiv-is-equiv-precomp
      ( ind-coprod _ i j)
      ( λ l X → is-equiv-right-factor'
        ( ev-inl-inr (λ t → X))
        ( precomp (ind-coprod (λ t → Y) i j) X)
        ( universal-property-coprod X)
        ( H _ X))

  universal-property-coprod-is-equiv-ind-coprod :
    {l3 : Level} (X : UU l3) (i : A → X) (j : B → X) →
    is-equiv (ind-coprod (λ t → X) i j) →
    (l4 : Level) (Y : UU l4) →
      is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j))
  universal-property-coprod-is-equiv-ind-coprod X i j H l Y =
    is-equiv-comp
      ( λ s → pair (s ∘ i) (s ∘ j))
      ( ev-inl-inr (λ t → Y))
      ( precomp (ind-coprod (λ t → X) i j) Y)
      ( λ s → refl)
      ( is-equiv-precomp-is-equiv
        ( ind-coprod (λ t → X) i j)
        ( H)
        ( Y))
      ( universal-property-coprod Y)

fib-emb-Prop :
  {i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → B → UU-Prop (i ⊔ j)
pr1 (fib-emb-Prop f y) = fib (map-emb f) y
pr2 (fib-emb-Prop f y) = is-prop-map-is-emb (is-emb-map-emb f) y

is-emb-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-emb (pr1 {B = B})
is-emb-pr1 {B = B} H =
  is-emb-is-prop-map (λ x → is-prop-equiv (B x) (equiv-fib-pr1 x) (H x))

equiv-ap-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
  is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
pr1 (equiv-ap-pr1 is-subtype-B {s} {t}) = ap pr1
pr2 (equiv-ap-pr1 is-subtype-B {s} {t}) = is-emb-pr1 is-subtype-B s t

is-subtype-is-emb-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
  is-emb (pr1 {B = B}) → is-subtype B
is-subtype-is-emb-pr1 H x =
  is-prop-equiv' (fib pr1 x) (equiv-fib-pr1 x) (is-prop-map-is-emb H x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-sec-is-equiv : {f : A → B} → is-equiv f → is-contr (sec f)
  is-contr-sec-is-equiv {f} is-equiv-f =
    is-contr-equiv'
      ( (b : B) → fib f b)
      ( equiv-choice-∞) 
      ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))

  is-contr-retr-is-equiv : {f : A → B} → is-equiv f → is-contr (retr f)
  is-contr-retr-is-equiv {f} is-equiv-f =
    is-contr-is-equiv'
      ( Σ (B → A) (λ h → Id (h ∘ f) id))
      ( tot (λ h → htpy-eq))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → funext (h ∘ f) id))
      ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f)

  is-subtype-is-equiv : is-subtype (is-equiv {A = A} {B = B})
  is-subtype-is-equiv f = is-prop-is-proof-irrelevant
    ( λ is-equiv-f → is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f))

  is-equiv-Prop : (f : A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-equiv-Prop f) = is-equiv f
  pr2 (is-equiv-Prop f) = is-subtype-is-equiv f

  is-emb-map-equiv :
    is-emb (map-equiv {A = A} {B = B})
  is-emb-map-equiv = is-emb-pr1 is-subtype-is-equiv

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  htpy-eq-equiv : {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
  htpy-eq-equiv {e = e} {.e} refl =
    refl-htpy-equiv e

  is-contr-total-htpy-equiv :
    (e : A ≃ B) → is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
  is-contr-total-htpy-equiv (pair f is-equiv-f) =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy f)
      ( is-subtype-is-equiv)
      ( f)
      ( refl-htpy)
      ( is-equiv-f)

  is-equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → is-equiv (htpy-eq-equiv {e = e} {e'})
  is-equiv-htpy-eq-equiv e =
    fundamental-theorem-id e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-eq-equiv {e = e} {e'})

  equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → Id e e' ≃ (htpy-equiv e e')
  pr1 (equiv-htpy-eq-equiv e e') = htpy-eq-equiv
  pr2 (equiv-htpy-eq-equiv e e') = is-equiv-htpy-eq-equiv e e'

  eq-htpy-equiv : {e e' : A ≃ B} → ( htpy-equiv e e') → Id e e'
  eq-htpy-equiv {e = e} {e'} = map-inv-is-equiv (is-equiv-htpy-eq-equiv e e')

  Ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B)
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    sec ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
          h e (refl-htpy-equiv e))
  Ind-htpy-equiv {l3 = l3} e =
    Ind-identity-system l3 e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
  
  ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (refl-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (Ind-htpy-equiv e P)
  
  comp-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (refl-htpy-equiv e)) →
    Id (ind-htpy-equiv e P p e (refl-htpy-equiv e)) p
  comp-htpy-equiv e P = pr2 (Ind-htpy-equiv e P)

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  pr1 (is-contr-equiv-is-contr is-contr-A is-contr-B) =
    equiv-is-contr is-contr-A is-contr-B
  pr2 (is-contr-equiv-is-contr is-contr-A is-contr-B) e =
    eq-htpy-equiv (λ x → eq-is-contr is-contr-B)

  is-trunc-equiv-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
  is-trunc-equiv-is-trunc neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-equiv-is-contr is-trunc-A is-trunc-B
  is-trunc-equiv-is-trunc (succ-𝕋 k) is-trunc-A is-trunc-B = 
    is-trunc-Σ (succ-𝕋 k)
      ( is-trunc-Π (succ-𝕋 k) (λ x → is-trunc-B))
      ( λ x → is-trunc-is-prop k (is-subtype-is-equiv x))

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop = is-trunc-equiv-is-trunc neg-one-𝕋

  is-set-equiv-is-set : is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

type-equiv-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (equiv-Prop P Q) = type-equiv-Prop P Q
pr2 (equiv-Prop P Q) =
  is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

type-equiv-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU (l1 ⊔ l2)
type-equiv-Set A B = type-Set A ≃ type-Set B

equiv-Set :
  { l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
pr1 (equiv-Set A B) = type-equiv-Set A B
pr2 (equiv-Set A B) =
  is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B)

inv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  Id (inv-equiv (inv-equiv e)) e
inv-inv-equiv (pair f (pair (pair g G) (pair h H))) = eq-htpy-equiv refl-htpy

is-equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → is-equiv (inv-equiv {A = A} {B = B})
is-equiv-inv-equiv =
  is-equiv-has-inverse
    ( inv-equiv)
    ( inv-inv-equiv)
    ( inv-inv-equiv)

equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) ≃ (B ≃ A)
pr1 equiv-inv-equiv = inv-equiv
pr2 equiv-inv-equiv = is-equiv-inv-equiv

compose-inv-equiv-compose-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) →
  Id (inv-equiv f ∘e (f ∘e e)) e
compose-inv-equiv-compose-equiv f e =
  eq-htpy-equiv (λ x → isretr-map-inv-equiv f (map-equiv e x))

compose-equiv-compose-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ C) →
  Id (f ∘e (inv-equiv f ∘e e)) e
compose-equiv-compose-inv-equiv f e =
  eq-htpy-equiv (λ x → issec-map-inv-equiv f (map-equiv e x))

is-equiv-comp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (A : UU l1) → is-equiv (λ (e : A ≃ B) → f ∘e e)
is-equiv-comp-equiv f A =
  is-equiv-has-inverse
    ( λ e → inv-equiv f ∘e e)
    ( compose-equiv-compose-inv-equiv f)
    ( compose-inv-equiv-compose-equiv f)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) e = f ∘e e
pr2 (equiv-postcomp-equiv f A) = is-equiv-comp-equiv f A

_⇔_ :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
P ⇔ Q = (pr1 P → pr1 Q) × (pr1 Q → pr1 P)

equiv-iff' :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) → (pr1 P ≃ pr1 Q)
pr1 (equiv-iff' P Q t) = pr1 t
pr2 (equiv-iff' P Q t) = is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t)

equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (type-hom-Prop P Q) → (type-hom-Prop Q P) → pr1 P ≃ pr1 Q
equiv-iff P Q f g = equiv-iff' P Q (pair f g)

iff-equiv :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (pr1 P ≃ pr1 Q) → (P ⇔ Q)
pr1 (iff-equiv P Q equiv-PQ) = pr1 equiv-PQ
pr2 (iff-equiv P Q equiv-PQ) = map-inv-is-equiv (pr2 equiv-PQ)

is-prop-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → is-prop (P ⇔ Q)
is-prop-iff P Q =
  is-prop-prod
    ( is-prop-function-type (pr2 Q))
    ( is-prop-function-type (pr2 P))

is-prop-equiv-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-prop ((pr1 P) ≃ (pr1 Q))
is-prop-equiv-Prop P Q =
  is-prop-equiv-is-prop (pr2 P) (pr2 Q)

is-equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-equiv (equiv-iff' P Q)
is-equiv-equiv-iff P Q =
  is-equiv-is-prop
    ( is-prop-iff P Q)
    ( is-prop-equiv-Prop P Q)
    ( iff-equiv P Q)

equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q

is-prop-is-contr-endomaps :
  {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
is-prop-is-contr-endomaps P H =
  is-prop-all-elements-equal (λ x → htpy-eq (eq-is-contr H))

is-contr-endomaps-is-prop :
  {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
is-contr-endomaps-is-prop P is-prop-P =
  is-proof-irrelevant-is-prop (is-prop-function-type is-prop-P) id

is-prop-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-prop (is-emb f)
is-prop-is-emb f =
  is-prop-Π (λ x → is-prop-Π (λ y → is-subtype-is-equiv (ap f)))

is-emb-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
pr1 (is-emb-Prop f) = is-emb f
pr2 (is-emb-Prop f) = is-prop-is-emb f

is-subtype-is-contr :
  {l : Level} → is-subtype {lsuc l} {A = UU l} is-contr
is-subtype-is-contr A =
  is-prop-is-proof-irrelevant
    ( λ is-contr-A →
      is-contr-Σ
        ( is-contr-A)
        ( λ x → is-contr-Π (is-prop-is-contr is-contr-A x)))

is-contr-Prop : {l : Level} → UU l → UU-Prop l
pr1 (is-contr-Prop A) = is-contr A
pr2 (is-contr-Prop A) = is-subtype-is-contr A

is-prop-is-trunc :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
is-prop-is-trunc neg-two-𝕋 = is-subtype-is-contr
is-prop-is-trunc (succ-𝕋 k) A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-trunc k (Id x y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → UU-Prop l
pr1 (is-trunc-Prop k A) = is-trunc k A
pr2 (is-trunc-Prop k A) = is-prop-is-trunc k A

is-prop-is-prop :
  {l : Level} (A : UU l) → is-prop (is-prop A)
is-prop-is-prop = is-prop-is-trunc neg-one-𝕋

is-prop-Prop : {l : Level} (A : UU l) → UU-Prop l
pr1 (is-prop-Prop A) = is-prop A
pr2 (is-prop-Prop A) = is-prop-is-prop A

is-prop-is-set :
  {l : Level} (A : UU l) → is-prop (is-set A)
is-prop-is-set = is-prop-is-trunc zero-𝕋

is-set-Prop : {l : Level} → UU l → UU-Prop l
pr1 (is-set-Prop A) = is-set A
pr2 (is-set-Prop A) = is-prop-is-set A

is-prop-is-trunc-map :
  (k : 𝕋) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-trunc-map k f)
is-prop-is-trunc-map k f = is-prop-Π (λ x → is-prop-is-trunc k (fib f x))

is-prop-is-contr-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-contr-map f)
is-prop-is-contr-map f = is-prop-is-trunc-map neg-two-𝕋 f

is-prop-is-prop-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-prop (is-prop-map f)
is-prop-is-prop-map f = is-prop-is-trunc-map neg-one-𝕋 f

is-trunc-map-Prop :
  (k : 𝕋) {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
pr1 (is-trunc-map-Prop k f) = is-trunc-map k f
pr2 (is-trunc-map-Prop k f) = is-prop-is-trunc-map k f

is-contr-map-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
pr1 (is-contr-map-Prop f) = is-contr-map f
pr2 (is-contr-map-Prop f) = is-prop-is-contr-map f

is-prop-map-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
pr1 (is-prop-map-Prop f) = is-prop-map f
pr2 (is-prop-map-Prop f) = is-prop-is-prop-map f

equiv-is-equiv-is-contr-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr-map f ≃ is-equiv f
equiv-is-equiv-is-contr-map f =
  equiv-iff
    ( is-contr-map-Prop f)
    ( is-equiv-Prop f)
    ( is-equiv-is-contr-map)
    ( is-contr-map-is-equiv)

equiv-is-contr-map-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f ≃ is-contr-map f
equiv-is-contr-map-is-equiv f =
  equiv-iff
    ( is-equiv-Prop f)
    ( is-contr-map-Prop f)
    ( is-contr-map-is-equiv)
    ( is-equiv-is-contr-map)

equiv-is-emb-is-prop-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop-map f ≃ is-emb f
equiv-is-emb-is-prop-map f =
  equiv-iff
    ( is-prop-map-Prop f)
    ( is-emb-Prop f)
    ( is-emb-is-prop-map)
    ( is-prop-map-is-emb)

equiv-is-prop-map-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-emb f ≃ is-prop-map f
equiv-is-prop-map-is-emb f =
  equiv-iff
    ( is-emb-Prop f)
    ( is-prop-map-Prop f)
    ( is-prop-map-is-emb)
    ( is-emb-is-prop-map)

equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  total-subtype C ≃ total-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff' (C x) (D (map-equiv e x)) (H x))

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
equiv-precomp-equiv e C =
  equiv-subtype-equiv
    ( equiv-precomp e C)
    ( is-equiv-Prop)
    ( is-equiv-Prop)
    ( λ g →
      pair
        ( is-equiv-comp' g (map-equiv e) (is-equiv-map-equiv e))
        ( λ is-equiv-eg →
          is-equiv-left-factor'
            g (map-equiv e) is-equiv-eg (is-equiv-map-equiv e)))

module _
  {l1 : Level} {A : UU l1}
  where

  ev-point : {l2 : Level} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
  ev-point a f = f a

  ev-point' : {l2 : Level} (a : A) {X : UU l2} → (A → X) → X
  ev-point' a f = f a

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a =
    (P : A → UU l) → is-equiv (ev-point a {P})

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a =
    (X : UU l) → is-equiv (ev-point' a {X})

  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X =
    dup-contr {l} (λ x → X)

  is-equiv-ev-point-universal-property-contr :
    (a : A) → ({l : Level} → universal-property-contr l a) →
    is-equiv (ev-point' a {A})
  is-equiv-ev-point-universal-property-contr a up-contr =
    up-contr A

  -- !! This definition seems to cause a slowdown
  is-contr-is-equiv-ev-point :
    (a : A) → is-equiv (ev-point' a) → is-contr A
  pr1 (is-contr-is-equiv-ev-point a H) = a
  pr2 (is-contr-is-equiv-ev-point a H) =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr'
          ( is-contr-map-is-equiv H a)
          ( pair (λ x → a) refl)
          ( pair id refl)))
  
  is-contr-universal-property-contr :
    (a : A) →
    ({l : Level} → universal-property-contr l a) → is-contr A
  is-contr-universal-property-contr a up-contr =
    is-contr-is-equiv-ev-point a
      ( is-equiv-ev-point-universal-property-contr a up-contr)

  is-contr-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) → is-contr A
  is-contr-dependent-universal-property-contr a dup-contr =
    is-contr-universal-property-contr a
      ( universal-property-dependent-universal-property-contr a dup-contr)

  dependent-universal-property-contr-is-contr :
    (a : A) → is-contr A →
    {l : Level} → dependent-universal-property-contr l a
  dependent-universal-property-contr-is-contr a H {l} P =
    is-equiv-has-inverse
      ( ind-singleton-is-contr a H P)
      ( comp-singleton-is-contr a H P)
      ( λ f →
        eq-htpy
          ( ind-singleton-is-contr a H
            ( λ x → Id (ind-singleton-is-contr a H P (f a) x) (f x))
            ( comp-singleton-is-contr a H P (f a))))

  universal-property-contr-is-contr :
    (a : A) → is-contr A → {l : Level} → universal-property-contr l a
  universal-property-contr-is-contr a H =
    universal-property-dependent-universal-property-contr a
      ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr a H X) = ev-point' a
  pr2 (equiv-universal-property-contr a H X) =
    universal-property-contr-is-contr a H X

  is-equiv-self-diagonal-is-equiv-diagonal :
    ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) →
    is-equiv (λ x → const A A x)
  is-equiv-self-diagonal-is-equiv-diagonal H = H A

  is-contr-is-equiv-self-diagonal :
    is-equiv (λ x → const A A x) → is-contr A
  is-contr-is-equiv-self-diagonal H =
    tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  is-contr-is-equiv-diagonal :
    ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) → is-contr A
  is-contr-is-equiv-diagonal H =
    is-contr-is-equiv-self-diagonal
      ( is-equiv-self-diagonal-is-equiv-diagonal H)

  is-equiv-diagonal-is-contr :
    is-contr A →
    {l : Level} (X : UU l) → is-equiv (λ x → const A X x)
  is-equiv-diagonal-is-contr H X =
    is-equiv-has-inverse
      ( ev-point' (center H))
      ( λ f → eq-htpy (λ x → ap f (contraction H x)))
      ( λ x → refl)

  equiv-diagonal-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-is-contr X H) = const A X
  pr2 (equiv-diagonal-is-contr X H) = is-equiv-diagonal-is-contr H X

ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ t → Y)

pt : {l1 : Level} {X : UU l1} (x : X) → unit → X
pt x y = x

dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
dependent-universal-property-unit =
  dependent-universal-property-contr-is-contr star is-contr-unit

equiv-dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
pr1 (equiv-dependent-universal-property-unit P) = ev-star P
pr2 (equiv-dependent-universal-property-unit P) =
  dependent-universal-property-unit P

equiv-ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
pr1 (equiv-ev-star P) = ev-star P
pr2 (equiv-ev-star P) = dependent-universal-property-unit P

universal-property-unit :
  {l : Level} (Y : UU l) → is-equiv (ev-star' Y)
universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

equiv-universal-property-unit :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
pr1 (equiv-universal-property-unit Y) = ev-star' Y
pr2 (equiv-universal-property-unit Y) = universal-property-unit Y

equiv-ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
pr1 (equiv-ev-star' Y) = ev-star' Y
pr2 (equiv-ev-star' Y) = universal-property-unit Y

is-equiv-pt-is-contr :
  {l1 : Level} {X : UU l1} (x : X) →
  is-contr X → is-equiv (pt x)
is-equiv-pt-is-contr x is-contr-X =
  is-equiv-is-contr (pt x) is-contr-unit is-contr-X

is-equiv-pt-universal-property-unit :
  {l1 : Level} (X : UU l1) (x : X) →
  ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
  is-equiv (pt x)
is-equiv-pt-universal-property-unit X x H =
  is-equiv-is-equiv-precomp
    ( pt x)
    ( λ l Y → is-equiv-right-factor'
      ( ev-star' Y)
      ( precomp (pt x) Y)
      ( universal-property-unit Y)
      ( H _ Y))

universal-property-unit-is-equiv-pt :
  {l1 : Level} {X : UU l1} (x : X) →
  is-equiv (pt x) →
  ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
universal-property-unit-is-equiv-pt x is-equiv-pt Y =
  is-equiv-comp
    ( λ f → f x)
    ( ev-star' Y)
    ( precomp (pt x) Y)
    ( λ f → refl)
    ( is-equiv-precomp-is-equiv (pt x) is-equiv-pt Y)
    ( universal-property-unit Y)

universal-property-unit-is-contr :
  {l1 : Level} {X : UU l1} (x : X) →
  is-contr X →
  ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
universal-property-unit-is-contr x is-contr-X =
  universal-property-unit-is-equiv-pt x
    ( is-equiv-pt-is-contr x is-contr-X)

is-equiv-diagonal-is-equiv-pt :
  {l1 : Level} {X : UU l1} (x : X) →
  is-equiv (pt x) →
  ({l2 : Level} (Y : UU l2) → is-equiv (λ y → const X Y y))
is-equiv-diagonal-is-equiv-pt {X = X} x is-equiv-pt Y =
  is-equiv-is-section-is-equiv
    ( universal-property-unit-is-equiv-pt x is-equiv-pt Y)
    ( refl-htpy)

module _
  {l1 : Level} (A : UU l1)
  where

  dependent-universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-empty l =
    (P : A → UU l) → is-contr ((x : A) → P x)

  universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  universal-property-empty l = (X : UU l) → is-contr (A → X)

  universal-property-dependent-universal-property-empty :
    ({l : Level} → dependent-universal-property-empty l) →
    ({l : Level} → universal-property-empty l)
  universal-property-dependent-universal-property-empty dup-empty {l} X =
    dup-empty {l} (λ a → X)

  is-empty-universal-property-empty :
    ({l : Level} → universal-property-empty l) → is-empty A
  is-empty-universal-property-empty up-empty = center (up-empty empty)

  dependent-universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → dependent-universal-property-empty l
  pr1 (dependent-universal-property-empty-is-empty {l} H P) x = ex-falso (H x)
  pr2 (dependent-universal-property-empty-is-empty {l} H P) f =
    eq-htpy (λ x → ex-falso (H x))

  universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → universal-property-empty l
  universal-property-empty-is-empty {l} H =
    universal-property-dependent-universal-property-empty
      ( dependent-universal-property-empty-is-empty H)

dependent-universal-property-empty' :
  {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
pr1 (dependent-universal-property-empty' P) ()
pr2 (dependent-universal-property-empty' P) f = eq-htpy ind-empty

all-elements-equal-coprod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
  all-elements-equal (coprod P Q)
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inl p') =
  ap inl (is-prop-P p p')
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inr q') =
  ex-falso (f p q')
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inl p') =
  ex-falso (f p' q)
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inr q') =
  ap inr (is-prop-Q q q')

is-prop-coprod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
is-prop-coprod f is-prop-P is-prop-Q =
  is-prop-all-elements-equal
    ( all-elements-equal-coprod f
      ( eq-is-prop' is-prop-P)
      ( eq-is-prop' is-prop-Q))

is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set' A B = (x : A) → type-Set (B x)

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' A B =
  is-set-Π (λ x → is-set-type-Set (B x))

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set' A B) = type-Π-Set' A B
pr2 (Π-Set' A B) = is-set-type-Π-Set' A B

type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set A B = type-Π-Set' (type-Set A) B

is-set-type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set A B =
  is-set-type-Π-Set' (type-Set A) B

Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) →
  (type-Set A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set A B) = type-Π-Set A B
pr2 (Π-Set A B) = is-set-type-Π-Set A B

type-hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU (l1 ⊔ l2)
type-hom-Set A B = type-Set A → type-Set B

is-set-type-hom-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  is-set (type-hom-Set A B)
is-set-type-hom-Set A B = is-set-function-type (is-set-type-Set B)

hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
pr1 (hom-Set A B) = type-hom-Set A B
pr2 (hom-Set A B) = is-set-type-hom-Set A B

is-equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
is-equiv-inv-htpy f g =
  is-equiv-has-inverse
    ( inv-htpy)
    ( λ H → eq-htpy (λ x → inv-inv (H x)))
    ( λ H → eq-htpy (λ x → inv-inv (H x)))

equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
pr1 (equiv-inv-htpy f g) = inv-htpy
pr2 (equiv-inv-htpy f g) = is-equiv-inv-htpy f g

is-equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) →
  (h : (x : A) → B x) → is-equiv (concat-htpy H h)
is-equiv-concat-htpy {A = A} {B = B} {f} =
  ind-htpy f
    ( λ g H → (h : (x : A) → B x) → is-equiv (concat-htpy H h))
    ( λ h → is-equiv-id)

equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
pr1 (equiv-concat-htpy H h) = concat-htpy H h
pr2 (equiv-concat-htpy H h) = is-equiv-concat-htpy H h

hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
hom-slice {A = A} {B} f g = Σ (A → B) (λ h → f ~ (g ∘ h))

map-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → A → B
map-hom-slice f g h = pr1 h

triangle-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  f ~ (g ∘ (map-hom-slice f g h))
triangle-hom-slice f g h = pr2 h

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice h h' =
    Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
      ( λ K →
        ( (triangle-hom-slice f g h) ∙h (g ·l K)) ~
        ( triangle-hom-slice f g h'))

  refl-htpy-hom-slice : (h : hom-slice f g) → htpy-hom-slice h h
  pr1 (refl-htpy-hom-slice h) = refl-htpy
  pr2 (refl-htpy-hom-slice h) = right-unit-htpy
  
  htpy-eq-hom-slice : (h h' : hom-slice f g) → Id h h' → htpy-hom-slice h h'
  htpy-eq-hom-slice h .h refl = refl-htpy-hom-slice h

  is-contr-total-htpy-hom-slice :
    (h : hom-slice f g) → is-contr (Σ (hom-slice f g) (htpy-hom-slice h))
  is-contr-total-htpy-hom-slice h =
    is-contr-total-Eq-structure
      ( λ h' H' K → ((triangle-hom-slice f g h) ∙h (g ·l K)) ~ H')
      ( is-contr-total-htpy (map-hom-slice f g h))
      ( pair (map-hom-slice f g h) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( f ~ (g ∘ (map-hom-slice f g h)))
            ( λ H' → (triangle-hom-slice f g h) ~ H'))
        ( equiv-tot (equiv-concat-htpy right-unit-htpy))
        ( is-contr-total-htpy (triangle-hom-slice f g h)))

  is-equiv-htpy-eq-hom-slice :
    (h h' : hom-slice f g) → is-equiv (htpy-eq-hom-slice h h')
  is-equiv-htpy-eq-hom-slice h =
    fundamental-theorem-id h
      ( refl-htpy-hom-slice h)
      ( is-contr-total-htpy-hom-slice h)
      ( htpy-eq-hom-slice h)

  equiv-htpy-eq-hom-slice :
    (h h' : hom-slice f g) → Id h h' ≃ htpy-hom-slice h h'
  pr1 (equiv-htpy-eq-hom-slice h h') = htpy-eq-hom-slice h h'
  pr2 (equiv-htpy-eq-hom-slice h h') = is-equiv-htpy-eq-hom-slice h h'

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → Id h h'
  eq-htpy-hom-slice h h' = map-inv-is-equiv (is-equiv-htpy-eq-hom-slice h h')

fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  (x : X) → (fib f x) → (fib g x)
pr1 (fib-triangle f g h H .(f a) (pair a refl)) = h a
pr2 (fib-triangle f g h H .(f a) (pair a refl)) = inv (H a)

fib-triangle' :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (g : B → X) (h : A → B) (x : X) → (fib (g ∘ h) x) → fib g x
fib-triangle' g h x = fib-triangle (g ∘ h) g h refl-htpy x

square-tot-fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (h ∘ (map-equiv-total-fib f)) ~
  ((map-equiv-total-fib g) ∘ (tot (fib-triangle f g h H)))
square-tot-fib-triangle f g h H (pair .(f a) (pair a refl)) = refl

is-equiv-top-is-equiv-bottom-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv i) → (is-equiv h)
is-equiv-top-is-equiv-bottom-square
  f g h i H is-equiv-f is-equiv-g is-equiv-i =
  is-equiv-right-factor (i ∘ f) g h H is-equiv-g
    ( is-equiv-comp' i f is-equiv-f is-equiv-i)

is-equiv-bottom-is-equiv-top-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv h) → (is-equiv i)
is-equiv-bottom-is-equiv-top-square
  f g h i H is-equiv-f is-equiv-g is-equiv-h = 
  is-equiv-left-factor' i f
    ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g) is-equiv-f

is-equiv-left-is-equiv-right-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv h) → (is-equiv i) → (is-equiv g) → (is-equiv f)
is-equiv-left-is-equiv-right-square
  f g h i H is-equiv-h is-equiv-i is-equiv-g =
  is-equiv-right-factor' i f is-equiv-i
    ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g)

is-equiv-right-is-equiv-left-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv h) → (is-equiv i) → (is-equiv f) → (is-equiv g)
is-equiv-right-is-equiv-left-square
  f g h i H is-equiv-h is-equiv-i is-equiv-f =
  is-equiv-left-factor (i ∘ f) g h H
    ( is-equiv-comp' i f is-equiv-f is-equiv-i)
    ( is-equiv-h)

is-fiberwise-equiv-is-equiv-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-equiv h) → is-fiberwise-equiv (fib-triangle f g h H)
is-fiberwise-equiv-is-equiv-triangle f g h H E =
  is-fiberwise-equiv-is-equiv-tot
    ( fib-triangle f g h H)
    ( is-equiv-top-is-equiv-bottom-square
      ( map-equiv-total-fib f)
      ( map-equiv-total-fib g)
      ( tot (fib-triangle f g h H))
      ( h)
      ( square-tot-fib-triangle f g h H)
      ( is-equiv-map-equiv-total-fib f)
      ( is-equiv-map-equiv-total-fib g)
      ( E))

is-equiv-triangle-is-fiberwise-equiv :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-fiberwise-equiv (fib-triangle f g h H)) → is-equiv h
is-equiv-triangle-is-fiberwise-equiv f g h H E =
  is-equiv-bottom-is-equiv-top-square
    ( map-equiv-total-fib f)
    ( map-equiv-total-fib g)
    ( tot (fib-triangle f g h H))
    ( h)
    ( square-tot-fib-triangle f g h H)
    ( is-equiv-map-equiv-total-fib f)
    ( is-equiv-map-equiv-total-fib g)
    ( is-equiv-tot-is-fiberwise-equiv E)
  
fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g → (x : X) → (fib f x) → (fib g x)
fiberwise-hom-hom-slice f g (pair h H) = fib-triangle f g h H

hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → (fib f x) → (fib g x)) → hom-slice f g
pr1 (hom-slice-fiberwise-hom f g α) a = pr1 (α (f a) (pair a refl))
pr2 (hom-slice-fiberwise-hom f g α) a = inv (pr2 (α (f a) (pair a refl)))

issec-hom-slice-fiberwise-hom-eq-htpy :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (α : (x : X) → (fib f x) → (fib g x)) (x : X) →
  (fiberwise-hom-hom-slice f g (hom-slice-fiberwise-hom f g α) x) ~ (α x)
issec-hom-slice-fiberwise-hom-eq-htpy f g α .(f a) (pair a refl) =
  eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

issec-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((fiberwise-hom-hom-slice f g) ∘ (hom-slice-fiberwise-hom f g)) ~ id
issec-hom-slice-fiberwise-hom f g α =
  eq-htpy (λ x → eq-htpy (issec-hom-slice-fiberwise-hom-eq-htpy f g α x))

isretr-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((hom-slice-fiberwise-hom f g) ∘ (fiberwise-hom-hom-slice f g)) ~ id
isretr-hom-slice-fiberwise-hom f g (pair h H) =
  eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

is-equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (fiberwise-hom-hom-slice f g)
is-equiv-fiberwise-hom-hom-slice f g =
  is-equiv-has-inverse
    ( hom-slice-fiberwise-hom f g)
    ( issec-hom-slice-fiberwise-hom f g)
    ( isretr-hom-slice-fiberwise-hom f g)

equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g ≃ ((x : X) → fib f x → fib g x)
pr1 (equiv-fiberwise-hom-hom-slice f g) = fiberwise-hom-hom-slice f g
pr2 (equiv-fiberwise-hom-hom-slice f g) = is-equiv-fiberwise-hom-hom-slice f g

is-equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (hom-slice-fiberwise-hom f g)
is-equiv-hom-slice-fiberwise-hom f g =
  is-equiv-has-inverse
    ( fiberwise-hom-hom-slice f g)
    ( isretr-hom-slice-fiberwise-hom f g)
    ( issec-hom-slice-fiberwise-hom f g)

equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → fib f x → fib g x) ≃ hom-slice f g
pr1 (equiv-hom-slice-fiberwise-hom f g) = hom-slice-fiberwise-hom f g
pr2 (equiv-hom-slice-fiberwise-hom f g) = is-equiv-hom-slice-fiberwise-hom f g

equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice {A = A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (map-equiv e)))

hom-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → hom-slice f g
pr1 (hom-equiv-slice f g e) = pr1 (pr1 e)
pr2 (hom-equiv-slice f g e) = pr2 e

is-equiv-subtype-is-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
  (f : A → B) (g : (x : A) → P x → Q (f x)) →
  is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
  is-equiv-map-Σ Q f g is-equiv-f
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

is-equiv-subtype-is-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
  (f : A → B) (g : (x : A) → P x → Q (f x)) →
  (is-equiv-f : is-equiv f) →
  ((y : B) → (Q y) → P (map-inv-is-equiv is-equiv-f y)) →
  is-equiv (map-Σ Q f g)
is-equiv-subtype-is-equiv' {P = P} {Q}
  is-subtype-P is-subtype-Q f g is-equiv-f h =
  is-equiv-map-Σ Q f g is-equiv-f
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x))
      ( (tr P (isretr-map-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))

is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  (t : hom-slice f g) → is-equiv (pr1 t) →
  is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g (pair h H) =
  is-fiberwise-equiv-is-equiv-triangle f g h H

left-factor-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH)) →
  Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
left-factor-fiberwise-equiv-equiv-slice f g =
  map-Σ
    ( is-fiberwise-equiv)
    ( fiberwise-hom-hom-slice f g)
    ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)

swap-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH))
swap-equiv-slice {A = A} {B} f g =
  map-equiv-double-structure is-equiv (λ h → f ~ (g ∘ h))

is-equiv-swap-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (swap-equiv-slice f g)
is-equiv-swap-equiv-slice f g =
  is-equiv-map-equiv (equiv-double-structure is-equiv (λ h → f ~ (g ∘ h)))

fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  ( left-factor-fiberwise-equiv-equiv-slice f g) ∘
  ( swap-equiv-slice f g)

is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  (t : hom-slice f g) →
  ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
  is-equiv (pr1 t)
is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
  f g (pair h H) =
  is-equiv-triangle-is-fiberwise-equiv f g h H

is-equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (fiberwise-equiv-equiv-slice f g)
is-equiv-fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  is-equiv-comp
    ( fiberwise-equiv-equiv-slice f g)
    ( left-factor-fiberwise-equiv-equiv-slice f g)
    ( swap-equiv-slice f g)
    ( refl-htpy)
    ( is-equiv-swap-equiv-slice f g)
    ( is-equiv-subtype-is-equiv
      ( λ t → is-subtype-is-equiv (pr1 t))
      ( λ α → is-prop-Π (λ x → is-subtype-is-equiv (α x)))
      ( fiberwise-hom-hom-slice f g)
      ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)
      ( is-equiv-fiberwise-hom-hom-slice f g)
      ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
        f g))

equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
pr1 (equiv-fiberwise-equiv-equiv-slice f g) = fiberwise-equiv-equiv-slice f g
pr2 (equiv-fiberwise-equiv-equiv-slice f g) =
  is-equiv-fiberwise-equiv-equiv-slice f g

equiv-fam-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ ((x : X) → (fib f x) ≃ (fib g x))
equiv-fam-equiv-equiv-slice f g =
  ( equiv-inv-choice-∞ (λ x → is-equiv)) ∘e
  ( equiv-fiberwise-equiv-equiv-slice f g)

map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) → ((x : A) → C (f x) (pair x refl))
map-reduce-Π-fib f C h x = h (f x) (pair x refl)

inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((x : A) → C (f x) (pair x refl)) → ((y : B) (z : fib f y) → C y z)
inv-map-reduce-Π-fib f C h .(f x) (pair x refl) = h x

issec-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((map-reduce-Π-fib f C) ∘ (inv-map-reduce-Π-fib f C)) ~ id
issec-inv-map-reduce-Π-fib f C h = refl

isretr-inv-map-reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  (h : (y : B) (z : fib f y) → C y z) (y : B) →
  (inv-map-reduce-Π-fib f C ((map-reduce-Π-fib f C) h) y) ~ (h y)
isretr-inv-map-reduce-Π-fib' f C h .(f z) (pair z refl) = refl

isretr-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((inv-map-reduce-Π-fib f C) ∘ (map-reduce-Π-fib f C)) ~ id
isretr-inv-map-reduce-Π-fib f C h =
  eq-htpy (λ y → eq-htpy (isretr-inv-map-reduce-Π-fib' f C h y))

is-equiv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  is-equiv (map-reduce-Π-fib f C)
is-equiv-map-reduce-Π-fib f C =
  is-equiv-has-inverse
    ( inv-map-reduce-Π-fib f C)
    ( issec-inv-map-reduce-Π-fib f C)
    ( isretr-inv-map-reduce-Π-fib f C)

reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) ≃ ((x : A) → C (f x) (pair x refl))
pr1 (reduce-Π-fib' f C) = map-reduce-Π-fib f C
pr2 (reduce-Π-fib' f C) = is-equiv-map-reduce-Π-fib f C

reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fib f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fib f C = reduce-Π-fib' f (λ y z → C y)

equiv-fib-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fib (f (α j)) (h j)) ≃ fib (map-Π' α f) h
equiv-fib-map-Π' α f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e equiv-choice-∞

is-trunc-map-map-Π-is-trunc-map' :
  (k : 𝕋) {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
is-trunc-map-map-Π-is-trunc-map' k {J = J} α f H h =
  is-trunc-equiv' k
    ( (j : J) → fib (f (α j)) (h j))
    ( equiv-fib-map-Π' α f h)
    ( is-trunc-Π k (λ j → H (α j) (h j)))

is-trunc-map-is-trunc-map-map-Π' :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
  (i : I) → is-trunc-map k (f i)
is-trunc-map-is-trunc-map-map-Π' k {A = A} {B} f H i b =
  is-trunc-equiv' k
    ( fib (map-Π (λ (x : unit) → f i)) (const unit (B i) b))
    ( equiv-Σ
      ( λ a → Id (f i a) b)
      ( equiv-universal-property-unit (A i))
      ( λ h → equiv-ap
        ( equiv-universal-property-unit (B i))
        ( map-Π (λ x → f i) h)
        ( const unit (B i) b)))
    ( H (λ x → i) (const unit (B i) b))

is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A {X} {Y} f is-trunc-f =
  is-trunc-map-map-Π-is-trunc-map' k
    ( const A unit star)
    ( const unit (X → Y) f)
    ( const unit (is-trunc-map k f) is-trunc-f)

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} {Y} f is-trunc-post-f =
  is-trunc-map-is-trunc-map-map-Π' k
    ( const unit (X → Y) f)
    ( λ {l} {J} α → is-trunc-post-f {l} J)
    ( star)

is-equiv-is-equiv-postcomp :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
  is-equiv-is-contr-map
    ( is-trunc-map-is-trunc-map-postcomp neg-two-𝕋 f
      ( λ {l} A → is-contr-map-is-equiv (post-comp-equiv-f A)))

is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp'
  {l} {X} {Y} f is-equiv-postcomp-f =
  let sec-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-has-inverse
    ( pr1 sec-f)
    ( htpy-eq (pr2 sec-f))
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
             ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
             ( pair id refl))))

is-equiv-postcomp-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
  ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
  is-equiv-has-inverse 
    ( postcomp A (map-inv-is-equiv is-equiv-f))
    ( λ g → eq-htpy (htpy-right-whisk (issec-map-inv-is-equiv is-equiv-f) g))
    ( λ h → eq-htpy (htpy-right-whisk (isretr-map-inv-is-equiv is-equiv-f) h))

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A

is-emb-postcomp-is-emb :
  {l1 l2 l3 : Level} (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-emb f → is-emb (postcomp A f)
is-emb-postcomp-is-emb A f is-emb-f =
  is-emb-is-prop-map
    ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 A f
      ( is-prop-map-is-emb is-emb-f))

is-emb-is-emb-postcomp :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  ({l : Level} (A : UU l) → is-emb (postcomp A f)) → is-emb f
is-emb-is-emb-postcomp f is-emb-post-f =
  is-emb-is-prop-map
    ( is-trunc-map-is-trunc-map-postcomp neg-one-𝕋 f
      ( λ A → is-prop-map-is-emb (is-emb-post-f A)))

is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → UU-Prop lzero
pr1 (leq-ℕ-Prop m n) = leq-ℕ m n
pr2 (leq-ℕ-Prop m n) = is-prop-leq-ℕ m n

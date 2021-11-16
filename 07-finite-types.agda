{-# OPTIONS --without-K --exact-split #-}

module 07-finite-types where

open import 06-propositional-truncation public

count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

module _
  {l : Level} {X : UU l} (e : count X)
  where
  
  number-of-elements-count : ℕ
  number-of-elements-count = pr1 e
  
  equiv-count : Fin number-of-elements-count ≃ X
  equiv-count = pr2 e
  
  map-equiv-count : Fin number-of-elements-count → X
  map-equiv-count = map-equiv equiv-count
  
  map-inv-equiv-count : X → Fin number-of-elements-count
  map-inv-equiv-count = map-inv-equiv equiv-count
  
  inv-equiv-count : X ≃ Fin number-of-elements-count
  inv-equiv-count = inv-equiv equiv-count
  
  is-set-count : is-set X
  is-set-count =
    is-set-equiv'
      ( Fin number-of-elements-count)
      ( equiv-count)
      ( is-set-Fin number-of-elements-count)

is-empty-is-zero-number-of-elements-count :
  {l : Level} {X : UU l} (e : count X) →
  is-zero-ℕ (number-of-elements-count e) → is-empty X
is-empty-is-zero-number-of-elements-count (pair .zero-ℕ e) refl x =
  map-inv-equiv e x

is-zero-number-of-elements-count-is-empty :
  {l : Level} {X : UU l} (e : count X) →
  is-empty X → is-zero-ℕ (number-of-elements-count e)
is-zero-number-of-elements-count-is-empty (pair zero-ℕ e) H = refl
is-zero-number-of-elements-count-is-empty (pair (succ-ℕ k) e) H =
  ex-falso (H (map-equiv e zero-Fin))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
count-is-empty H =
  pair zero-ℕ (inv-equiv (pair H (is-equiv-is-empty' H)))

count-Fin : (k : ℕ) → count (Fin k)
count-Fin k = pair k equiv-id

count-empty : count empty
count-empty = count-Fin zero-ℕ

count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
count-is-contr H = pair one-ℕ (equiv-is-contr is-contr-Fin-one-ℕ H)

is-contr-is-one-number-of-elements-count :
  {l : Level} {X : UU l} (e : count X) →
  is-one-ℕ (number-of-elements-count e) → is-contr X
is-contr-is-one-number-of-elements-count (pair .(succ-ℕ zero-ℕ) e) refl =
  is-contr-equiv' (Fin one-ℕ) e is-contr-Fin-one-ℕ

is-one-number-of-elements-count-is-contr :
  {l : Level} {X : UU l} (e : count X) →
  is-contr X → is-one-ℕ (number-of-elements-count e)
is-one-number-of-elements-count-is-contr (pair zero-ℕ e) H =
  ex-falso (map-inv-equiv e (center H))
is-one-number-of-elements-count-is-contr (pair (succ-ℕ zero-ℕ) e) H =
  refl
is-one-number-of-elements-count-is-contr (pair (succ-ℕ (succ-ℕ k)) e) H =
  ex-falso
    ( Eq-Fin-eq
      ( is-injective-map-equiv e
        ( eq-is-contr' H (map-equiv e zero-Fin) (map-equiv e neg-one-Fin))))

count-unit : count unit
count-unit = count-is-contr is-contr-unit

equiv-count-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (f : count X) →
  Fin (number-of-elements-count f) ≃ Y
equiv-count-equiv e f = e ∘e (equiv-count f)

count-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count X → count Y
count-equiv e f =
  pair (number-of-elements-count f) (equiv-count-equiv e f)

count-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count Y → count X
count-equiv' e = count-equiv (inv-equiv e)

count-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-equiv f → count X → count Y
count-is-equiv is-equiv-f = count-equiv (pair _ is-equiv-f)

count-is-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-equiv f → count Y → count X
count-is-equiv' is-equiv-f = count-equiv' (pair _ is-equiv-f)

has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (pair k e) =
  has-decidable-equality-equiv' e has-decidable-equality-Fin

cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) → count (Id x y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (Id x y)
count-eq d x y = cases-count-eq d (d x y)

count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
count-coprod (pair k e) (pair l f) =
  pair
    ( add-ℕ k l)
    ( ( equiv-coprod e f) ∘e
      ( inv-equiv (coprod-Fin k l)))

number-of-elements-count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
  Id ( number-of-elements-count (count-coprod e f))
     ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
number-of-elements-count-coprod (pair k e) (pair l f) = refl

count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' zero-ℕ e f =
  count-is-empty
    ( λ x →
      is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl (pr1 x))
count-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e f =
  count-equiv
    ( ( equiv-Σ-equiv-base B e) ∘e
      ( ( inv-equiv
          ( right-distributive-Σ-coprod (Fin k) unit (B ∘ map-equiv e))) ∘e
        ( equiv-coprod
          ( equiv-id)
          ( inv-equiv
            ( left-unit-law-Σ (B ∘ (map-equiv e ∘ inr)))))))
    ( count-coprod
      ( count-Σ' k equiv-id (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star))))

equiv-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
  Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
count-Σ (pair k e) f =
  pair (number-of-elements-count (count-Σ' k e f)) (equiv-count-Σ' k e f)

is-finite-Prop :
  {l : Level} → UU l → UU-Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

is-prop-is-finite :
  {l : Level} (X : UU l) → is-prop (is-finite X)
is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

is-finite-count :
  {l : Level} {X : UU l} → count X → is-finite X
is-finite-count = unit-trunc-Prop

mere-equiv-Prop :
  {l1 l2 : Level} → UU l1 → UU l2 → UU-Prop (l1 ⊔ l2)
mere-equiv-Prop X Y = trunc-Prop (X ≃ Y)

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-Prop (mere-equiv-Prop X Y)

is-prop-mere-equiv :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-equiv X Y)
is-prop-mere-equiv X Y = is-prop-type-Prop (mere-equiv-Prop X Y)

refl-mere-equiv :
  {l1 : Level} (X : UU l1) → mere-equiv X X
refl-mere-equiv X = unit-trunc-Prop equiv-id

symmetric-mere-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → mere-equiv X Y → mere-equiv Y X
symmetric-mere-equiv {l1} {l2} {X} {Y} =
  map-universal-property-trunc-Prop
    ( mere-equiv-Prop Y X)
    ( λ e → unit-trunc-Prop (inv-equiv e))

transitive-mere-equiv :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} →
  mere-equiv X Y → mere-equiv Y Z → mere-equiv X Z
transitive-mere-equiv {X = X} {Y} {Z} e f =
  apply-universal-property-trunc-Prop e
    ( mere-equiv-Prop X Z)
    ( λ e' →
      apply-universal-property-trunc-Prop f
        ( mere-equiv-Prop X Z)
        ( λ f' → unit-trunc-Prop (f' ∘e e')))

has-cardinality-Prop :
  {l : Level} → UU l → ℕ → UU-Prop l
has-cardinality-Prop X k = mere-equiv-Prop (Fin k) X

has-cardinality :
  {l : Level} → UU l → ℕ → UU l
has-cardinality X k = mere-equiv (Fin k) X

finite-choice-Fin :
  {l1 : Level} {k : ℕ} {Y : Fin k → UU l1} →
  ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
finite-choice-Fin {l1} {zero-ℕ} {Y} H = unit-trunc-Prop ind-empty
finite-choice-Fin {l1} {succ-ℕ k} {Y} H =
  map-inv-equiv-trunc-Prop
    ( equiv-dependent-universal-property-coprod Y)
    ( map-inv-distributive-trunc-prod-Prop
      ( pair
        ( finite-choice-Fin (λ x → H (inl x)))
        ( map-inv-equiv-trunc-Prop
          ( equiv-ev-star (Y ∘ inr))
          ( H (inr star)))))

finite-choice-count :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → count X →
  ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
finite-choice-count {l1} {l2} {X} {Y} (pair k e) H =
  map-inv-equiv-trunc-Prop
    ( equiv-precomp-Π e Y)
    ( finite-choice-Fin (λ x → H (map-equiv e x)))

finite-choice :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → is-finite X →
  ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
finite-choice {l1} {l2} {X} {Y} is-finite-X H =
  apply-universal-property-trunc-Prop is-finite-X
    ( trunc-Prop ((x : X) → Y x))
    ( λ e → finite-choice-count e H)

is-finite-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-finite X → ((x : X) → is-finite (Y x)) → is-finite (Σ X Y)
is-finite-Σ {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (Σ X Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop
        ( finite-choice is-finite-X is-finite-Y)
        ( is-finite-Prop (Σ X Y))
        ( is-finite-count ∘ (count-Σ e)))

count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
count-prod (pair k e) (pair l f) =
  pair
    ( mul-ℕ k l)
    ( ( equiv-prod e f) ∘e
      ( inv-equiv (prod-Fin k l)))

number-of-elements-count-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
  (count-B : count B) →
  Id ( number-of-elements-count
       ( count-prod count-A count-B))
     ( mul-ℕ
       ( number-of-elements-count count-A)
       ( number-of-elements-count count-B))
number-of-elements-count-prod (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-prod) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-contr-total-path' y) is-contr-unit))) ∘e
  ( assoc-Σ X (λ x → Y) (λ t → Id (pr2 t) y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x

Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = one-ℕ
Π-ℕ (succ-ℕ k) x = mul-ℕ (Π-ℕ k (λ i → x (inl i))) (x (inr star))

count-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} {zero-ℕ} {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} {succ-ℕ k} {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coprod B)
    ( count-prod
      ( count-Π-Fin (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-ev-star (B ∘ inr))
        ( e (inr star))))

count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))

count-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  count A → count B → count (A → B)
count-function-type e f =
  count-Π e (λ x → f)

is-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
is-finite-Π {l1} {l2} {A} {B} f g =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop ((x : A) → B x))
    ( λ e →
      apply-universal-property-trunc-Prop
        ( finite-choice f g)
        ( is-finite-Prop ((x : A) → B x))
        ( λ h → unit-trunc-Prop (count-Π e h)))

𝔽 : UU (lsuc lzero)
𝔽 = Σ (UU lzero) is-finite

type-𝔽 : 𝔽 → UU lzero
type-𝔽 X = pr1 X

is-finite-type-𝔽 : (X : 𝔽) → is-finite (type-𝔽 X)
is-finite-type-𝔽 X = pr2 X

is-set-is-finite :
  {l : Level} {X : UU l} → is-finite X → is-set X
is-set-is-finite {l} {X} H =
  apply-universal-property-trunc-Prop H
    ( is-set-Prop X)
    ( λ e → is-set-count e)

is-prop-is-inhabited :
  {l1 : Level} {X : UU l1} → (X → is-prop X) → is-prop X
is-prop-is-inhabited f x y = f x x y

is-prop-has-decidable-equality :
  {l1 : Level} {X : UU l1} → is-prop (has-decidable-equality X)
is-prop-has-decidable-equality {l1} {X} =
  is-prop-is-inhabited
    ( λ d →
      is-prop-Π
      ( λ x →
        is-prop-Π
        ( λ y →
          is-prop-coprod
          ( intro-dn)
          ( is-set-has-decidable-equality d x y)
          ( is-prop-neg))))

has-decidable-equality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
has-decidable-equality-Prop X =
  pair (has-decidable-equality X) is-prop-has-decidable-equality

has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv' (equiv-count e) has-decidable-equality-Fin)

has-decidable-equality-has-cardinality :
  {l1 : Level} {X : UU l1} {k : ℕ} →
  has-cardinality X k → has-decidable-equality X
has-decidable-equality-has-cardinality {l1} {X} {k} H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e has-decidable-equality-Fin)

is-finite-eq :
  {l1 : Level} {X : UU l1} →
  has-decidable-equality X → {x y : X} → is-finite (Id x y)
is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : (X : 𝔽) (x y : type-𝔽 X) → 𝔽
Id-𝔽 X x y =
  pair ( Id x y)
       ( is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X)))

is-finite-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (X × Y)
is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (X × Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop is-finite-Y
        ( is-finite-Prop (X × Y))
        ( is-finite-count ∘ (count-prod e)))

prod-𝔽 : 𝔽 → 𝔽 → 𝔽
prod-𝔽 X Y =
  pair ( prod (type-𝔽 X) (type-𝔽 Y))
       ( is-finite-prod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y))

is-finite-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite (X × Y) → Y → is-finite X
is-finite-left-factor f y =
  functor-trunc-Prop (λ e → count-left-factor e y) f

is-finite-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite (X × Y) → X → is-finite Y
is-finite-right-factor f x =
  functor-trunc-Prop (λ e → count-right-factor e x) f

Π-𝔽 : (A : 𝔽) (B : type-𝔽 A → 𝔽) → 𝔽
Π-𝔽 A B =
  pair ( (x : type-𝔽 A) → type-𝔽 (B x))
       ( is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x)))

is-finite-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-finite A → is-finite B → is-finite (A → B)
is-finite-function-type f g = is-finite-Π f (λ x → g)

_→-𝔽_ : 𝔽 → 𝔽 → 𝔽
A →-𝔽 B =
  pair ( type-𝔽 A → type-𝔽 B)
       ( is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))

is-finite-≃ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-finite A → is-finite B → is-finite (A ≃ B)
is-finite-≃ f g =
  is-finite-Σ
    ( is-finite-function-type f g)
    ( λ h →
      is-finite-prod
        ( is-finite-Σ
          ( is-finite-function-type g f)
          ( λ k →
            is-finite-Π g
              ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
        ( is-finite-Σ
          ( is-finite-function-type g f)
          ( λ k →
            is-finite-Π f
              ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

_≃-𝔽_ : 𝔽 → 𝔽 → 𝔽
A ≃-𝔽 B =
  pair ( type-𝔽 A ≃ type-𝔽 B)
       ( is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))

Aut-𝔽 : 𝔽 → 𝔽
Aut-𝔽 A = A ≃-𝔽 A

UU-Fin-Level : (l : Level) → ℕ → UU (lsuc l)
UU-Fin-Level l k = Σ (UU l) (mere-equiv (Fin k))

type-UU-Fin-Level : {l : Level} {k : ℕ} → UU-Fin-Level l k → UU l
type-UU-Fin-Level X = pr1 X

mere-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → mere-equiv (Fin k) (type-UU-Fin-Level X)
mere-equiv-UU-Fin-Level X = pr2 X

UU-Fin : ℕ → UU (lsuc lzero)
UU-Fin k = UU-Fin-Level lzero k

type-UU-Fin : {k : ℕ} → UU-Fin k → UU lzero
type-UU-Fin X = pr1 X

Maybe : {l : Level} → UU l → UU l
Maybe X = coprod X unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
is-emb-unit-Maybe {l} {X} = is-emb-inl X unit

is-injective-unit-Maybe :
  {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
is-injective-unit-Maybe = is-injective-inl

exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = inr star

is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = Id x exception-Maybe

is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

is-not-exception-unit-Maybe :
  {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
is-not-exception-unit-Maybe {l} {X} x = neq-inl-inr x star

is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe {l} {X} (inl x) =
  inr
    (λ p → ex-falso (map-inv-raise (Eq-eq-coprod X unit (inl x) (inr star) p)))
is-decidable-is-exception-Maybe (inr star) = inl refl

is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe x =
  is-decidable-neg (is-decidable-is-exception-Maybe x)

is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → Id (inl y) x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  Id (inl (value-is-value-Maybe x H)) x
eq-is-value-Maybe x H = pr2 H

decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) →
  coprod (is-value-Maybe x) (is-exception-Maybe x)
decide-Maybe (inl x) = inl (pair x refl)
decide-Maybe (inr star) = inr refl

is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coprod-is-empty (is-value-Maybe x) (is-exception-Maybe x) H (decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  Id (inl (value-is-not-exception-Maybe x H)) x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

is-not-exception-is-value-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-value-Maybe x → is-not-exception-Maybe x
is-not-exception-is-value-Maybe {l1} {X} .(inl x) (pair x refl) =
  is-not-exception-unit-Maybe x

is-not-exception-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-not-exception-Maybe (f exception-Maybe)
is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
  is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

is-not-exception-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-not-exception-Maybe (map-equiv e exception-Maybe)
is-not-exception-map-equiv-exception-Maybe e =
  is-not-exception-injective-map-exception-Maybe (is-injective-map-equiv e)

is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  Id ( inl (value-injective-map-exception-Maybe is-inj-f x H))
     ( f exception-Maybe)
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

is-not-exception-emb-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
  (x : X) → is-exception-Maybe (map-emb e (inl x)) →
  is-not-exception-Maybe (map-emb e exception-Maybe)
is-not-exception-emb-exception-Maybe e =
  is-not-exception-injective-map-exception-Maybe (is-injective-emb e)

is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe e x H =
  is-value-is-not-exception-Maybe
    ( map-equiv e exception-Maybe)
    ( is-not-exception-map-equiv-exception-Maybe e x H)

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe e x H =
  value-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

comp-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  Id ( inl (value-map-equiv-exception-Maybe e x H))
     ( map-equiv e exception-Maybe)
comp-map-equiv-exception-Maybe e x H =
  eq-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

comp-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inl y) p H =
  inv p
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inr star) p H =
  ex-falso (H p)

comp-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-map-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe' e =
  comp-restrict-injective-map-is-exception-Maybe' (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe e x =
  comp-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

comp-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

comp-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe e x =
  comp-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl

map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e exception-Maybe)
comp-map-inv-equiv-equiv-is-exception-Maybe e =
  comp-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e (inl y))
comp-map-inv-equiv-equiv-is-not-exception-Maybe e =
  comp-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)

issec-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
issec-map-inv-equiv-equiv-Maybe e y with
  is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
... | inl p =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-equiv-is-exception-Maybe e
        ( map-inv-equiv-equiv-Maybe e y)
        ( ( ap
            ( map-equiv e)
            ( comp-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
          ( issec-map-inv-equiv e exception-Maybe))) ∙
      ( ( ap (map-equiv e) (inv p)) ∙
        ( issec-map-inv-equiv e (inl y))))
... | inr f =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-equiv-is-not-exception-Maybe e
        ( map-inv-equiv-equiv-Maybe e y)
        ( is-not-exception-is-value-Maybe
          ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
          ( pair y
            ( inv
              ( ( ap
                  ( map-equiv e)
                  ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
                ( issec-map-inv-equiv e (inl y))))))) ∙
      ( ( ap
          ( map-equiv e)
          ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
        ( issec-map-inv-equiv e (inl y))))

isretr-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
isretr-map-inv-equiv-equiv-Maybe e x with
  is-decidable-is-exception-Maybe (map-equiv e (inl x))
... | inl p =
  is-injective-unit-Maybe
    ( ( comp-map-inv-equiv-equiv-is-exception-Maybe e
        ( map-equiv-equiv-Maybe e x)
        ( ( ap ( map-inv-equiv e)
               ( comp-map-equiv-equiv-is-exception-Maybe e x p)) ∙
          ( isretr-map-inv-equiv e exception-Maybe))) ∙
      ( ( ap (map-inv-equiv e) (inv p)) ∙
        ( isretr-map-inv-equiv e (inl x))))
... | inr f =
  is-injective-unit-Maybe
    ( ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e
        ( map-equiv-equiv-Maybe e x)
        ( is-not-exception-is-value-Maybe
          ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
          ( pair x
            ( inv
              ( ( ap (map-inv-equiv e)
                     ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
                ( isretr-map-inv-equiv e (inl x))))))) ∙
      ( ( ap ( map-inv-equiv e)
             ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
        ( isretr-map-inv-equiv e (inl x))))

is-equiv-map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  is-equiv (map-equiv-equiv-Maybe e)
is-equiv-map-equiv-equiv-Maybe e =
  is-equiv-has-inverse
    ( map-inv-equiv-equiv-Maybe e)
    ( issec-map-inv-equiv-equiv-Maybe e)
    ( isretr-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
equiv-equiv-Maybe e =
  pair (map-equiv-equiv-Maybe e) (is-equiv-map-equiv-equiv-Maybe e)

is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → Id k l
is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
is-injective-Fin {zero-ℕ} {succ-ℕ l} e = ex-falso (map-inv-equiv e zero-Fin)
is-injective-Fin {succ-ℕ k} {zero-ℕ} e = ex-falso (map-equiv e zero-Fin)
is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
  ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))

double-counting-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
  (count-B : count B) (e : A ≃ B) →
  Id (number-of-elements-count count-A) (number-of-elements-count count-B)
double-counting-equiv (pair k f) (pair l g) e =
  is-injective-Fin ((inv-equiv g ∘e e) ∘e f)

double-counting :
  {l : Level} {A : UU l} (count-A count-A' : count A) →
  Id (number-of-elements-count count-A) (number-of-elements-count count-A')
double-counting count-A count-A' =
  double-counting-equiv count-A count-A' equiv-id

count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coprod e count-unit

is-nonzero-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-nonzero-ℕ (number-of-elements-count e)
is-nonzero-number-of-elements-count-Maybe e p =
  is-empty-is-zero-number-of-elements-count e p exception-Maybe

is-successor-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements-count e)
is-successor-number-of-elements-count-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-count-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-count-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)

sum-Fin-ℕ : {k : ℕ} → (Fin k → ℕ) → ℕ
sum-Fin-ℕ {zero-ℕ} f = zero-ℕ
sum-Fin-ℕ {succ-ℕ k} f = add-ℕ (sum-Fin-ℕ (λ x → f (inl x))) (f (inr star))

htpy-sum-Fin-ℕ :
  {k : ℕ} {f g : Fin k → ℕ} (H : f ~ g) → Id (sum-Fin-ℕ f) (sum-Fin-ℕ g)
htpy-sum-Fin-ℕ {zero-ℕ} H = refl
htpy-sum-Fin-ℕ {succ-ℕ k} H =
  ap-add-ℕ
    ( htpy-sum-Fin-ℕ (λ x → H (inl x)))
    ( H (inr star))

constant-sum-Fin-ℕ :
  (m n : ℕ) → Id (sum-Fin-ℕ (const (Fin m) ℕ n)) (mul-ℕ m n)
constant-sum-Fin-ℕ zero-ℕ n = refl
constant-sum-Fin-ℕ (succ-ℕ m) n = ap (add-ℕ' n) (constant-sum-Fin-ℕ m n)

sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ (f ∘ (map-equiv e))

ap-sum-count-ℕ :
  {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
  Id (sum-count-ℕ e f) (sum-count-ℕ e g)
ap-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ (H ·r (map-equiv e))

constant-sum-count-ℕ :
  {l : Level} {A : UU l} (e : count A) (n : ℕ) →
  Id (sum-count-ℕ e (const A ℕ n)) (mul-ℕ (number-of-elements-count e) n)
constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n

number-of-elements-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
  (f : (x : A) → count (B x)) →
  Id ( number-of-elements-count (count-Σ' k e f))
     ( sum-Fin-ℕ (λ x → number-of-elements-count (f (map-equiv e x)))) 
number-of-elements-count-Σ' zero-ℕ e f = refl
number-of-elements-count-Σ' (succ-ℕ k) e f =
  ( number-of-elements-count-coprod
    ( count-Σ' k equiv-id (λ x → f (map-equiv e (inl x))))
    ( f (map-equiv e (inr star)))) ∙
  ( ap
    ( add-ℕ' (number-of-elements-count (f (map-equiv e (inr star)))))
    ( number-of-elements-count-Σ' k equiv-id (λ x → f (map-equiv e (inl x)))))

number-of-elements-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
  (f : (x : A) → count (B x)) →
  Id ( number-of-elements-count (count-Σ e f))
     ( sum-count-ℕ e (λ x → number-of-elements-count (f x)))
number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f

double-counting-coprod :
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  ( count-A : count A) (count-B : count B) (count-C : count (coprod A B)) →
  Id ( number-of-elements-count count-C)
     ( add-ℕ
       ( number-of-elements-count count-A)
       ( number-of-elements-count count-B))
double-counting-coprod count-A count-B count-C =
  ( double-counting count-C (count-coprod count-A count-B)) ∙
  ( number-of-elements-count-coprod count-A count-B)

double-counting-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
  Id ( number-of-elements-count count-C)
     ( sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x)))
double-counting-Σ count-A count-B count-C =
  ( double-counting count-C (count-Σ count-A count-B)) ∙
  ( number-of-elements-count-Σ count-A count-B)

count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} e f x =
  count-equiv
    ( equiv-fib-pr1 x)
    ( count-Σ f
      ( λ z → count-eq (has-decidable-equality-count e) (pr1 z) x))

count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fib f y)
count-fib f count-A count-B =
  count-fiber-count-Σ count-B (count-equiv' (equiv-total-fib f) count-A)

sum-number-of-elements-count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
  (f : count (Σ A B)) →
  Id ( sum-count-ℕ e
       ( λ x → number-of-elements-count (count-fiber-count-Σ e f x)))
     ( number-of-elements-count f)
sum-number-of-elements-count-fiber-count-Σ e f =
  ( inv (number-of-elements-count-Σ e (λ x → count-fiber-count-Σ e f x))) ∙
  ( double-counting (count-Σ e (λ x → count-fiber-count-Σ e f x)) f)

double-counting-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
  Id ( number-of-elements-count (count-B x))
     ( number-of-elements-count (count-fiber-count-Σ count-A count-C x))
double-counting-fiber-count-Σ count-A count-B count-C x =
  double-counting (count-B x) (count-fiber-count-Σ count-A count-C x)

sum-number-of-elements-count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (count-A : count A) (count-B : count B) →
  Id ( sum-count-ℕ count-B
       ( λ x → number-of-elements-count (count-fib f count-A count-B x)))
     ( number-of-elements-count count-A)
sum-number-of-elements-count-fib f count-A count-B =
  sum-number-of-elements-count-fiber-count-Σ count-B
    ( count-equiv' (equiv-total-fib f) count-A)

double-counting-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (count-A : count A) →
  (count-B : count B) (count-fib-f : (y : B) → count (fib f y)) (y : B) →
  Id ( number-of-elements-count (count-fib-f y))
     ( number-of-elements-count (count-fib f count-A count-B y))
double-counting-fib f count-A count-B count-fib-f y =
  double-counting (count-fib-f y) (count-fib f count-A count-B y)

equiv-total-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-total-fib-map-section b = equiv-total-fib (map-section b)

count-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fib (map-section b) t)
count-fib-map-section {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
        ( inv-assoc-Σ A
          ( λ x → Id x y)
          ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fib-map-section b)
    ( count-Σ e (count-fib-map-section b e f))

sum-number-of-elements-count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
  Id ( sum-count-ℕ
       ( count-base-count-Σ b count-ΣAB count-B)
       ( λ x → number-of-elements-count (count-B x)))
     ( number-of-elements-count count-ΣAB)
sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
  ( inv
    ( number-of-elements-count-Σ
      ( count-base-count-Σ b count-ΣAB count-B)
      ( count-B))) ∙
  ( double-counting
    ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
    ( count-ΣAB))

double-counting-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (count-A : count A) (count-B : (x : A) → count (B x))
  (count-ΣAB : count (Σ A B)) →
  Id ( number-of-elements-count (count-base-count-Σ b count-ΣAB count-B))
     ( number-of-elements-count count-A)
double-counting-base-count-Σ b count-A count-B count-ΣAB =
  double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) zero-Fin))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coprod A B
        ( λ x → is-zero-ℕ (number-of-elements-count (f x))))
      ( count-coprod e g))
    ( λ x →
      count-coprod
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))

sum-number-of-elements-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
  ( count-B : (x : A) → count (B x)) →
  ( count-nB :
    count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
  Id ( sum-count-ℕ
       ( count-base-count-Σ' count-ΣAB count-B count-nB)
       ( λ x → number-of-elements-count (count-B x)))
     ( number-of-elements-count count-ΣAB)
sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
  ( inv
    ( number-of-elements-count-Σ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( count-B))) ∙
  ( double-counting
    ( count-Σ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( count-B))
    ( count-ΣAB))

double-counting-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
  ( count-nB :
    count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
  Id ( number-of-elements-count
       ( count-base-count-Σ' count-ΣAB count-B count-nB))
     ( number-of-elements-count count-A)
double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
  double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A

is-left : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-left (inl x) = unit
is-left (inr x) = empty

equiv-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-left) ≃ X
equiv-left-summand {l1} {l2} {X} {Y} =
  ( ( right-unit-law-coprod X) ∘e
    ( equiv-coprod right-unit-law-prod (right-absorption-prod Y))) ∘e
  ( right-distributive-Σ-coprod X Y is-left)

count-is-left :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-left t)
count-is-left (inl x) = count-unit
count-is-left (inr x) = count-empty

count-left-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-coprod e = count-equiv equiv-left-summand (count-Σ e count-is-left)

is-right : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-right (inl x) = empty
is-right (inr x) = unit

equiv-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-right) ≃ Y
equiv-right-summand {l1} {l2} {X} {Y} =
  ( ( left-unit-law-coprod Y) ∘e
    ( equiv-coprod (right-absorption-prod X) right-unit-law-prod)) ∘e
    ( right-distributive-Σ-coprod X Y is-right)

count-is-right :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-right t)
count-is-right (inl x) = count-empty
count-is-right (inr x) = count-unit

count-right-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-coprod e =
  count-equiv equiv-right-summand (count-Σ e count-is-right)

sum-number-of-elements-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (coprod A B)) →
  Id ( add-ℕ ( number-of-elements-count (count-left-coprod e))
             ( number-of-elements-count (count-right-coprod e)))
     ( number-of-elements-count e)
sum-number-of-elements-coprod e =
  ( inv
    ( number-of-elements-count-coprod
      ( count-left-coprod e)
      ( count-right-coprod e))) ∙
  ( inv
    ( double-counting-coprod (count-left-coprod e) (count-right-coprod e) e))

product-number-of-elements-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
  (a : A) (b : B) →
  Id ( mul-ℕ ( number-of-elements-count (count-left-factor count-AB b))
             ( number-of-elements-count (count-right-factor count-AB a)))
     ( number-of-elements-count count-AB)
product-number-of-elements-prod count-AB a b =
  ( inv
    ( number-of-elements-count-prod
      ( count-left-factor count-AB b)
      ( count-right-factor count-AB a))) ∙
  ( double-counting
    ( count-prod (count-left-factor count-AB b) (count-right-factor count-AB a))
    ( count-AB))

ev-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  ((x : Maybe A) → B x) → ((x : A) → B (unit-Maybe x)) × B exception-Maybe
ev-Maybe h = pair (λ x → h (unit-Maybe x)) (h exception-Maybe)

ind-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  ((x : A) → B (unit-Maybe x)) × (B exception-Maybe) → (x : Maybe A) → B x
ind-Maybe (pair h b) (inl x) = h x
ind-Maybe (pair h b) (inr star) = b

issec-ind-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  (ev-Maybe {B = B} ∘ ind-Maybe {B = B}) ~ id
issec-ind-Maybe (pair h b) = refl

isretr-ind-Maybe' :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} (h : (x : Maybe A) → B x) →
  (ind-Maybe (ev-Maybe h)) ~ h
isretr-ind-Maybe' h (inl x) = refl
isretr-ind-Maybe' h (inr star) = refl

isretr-ind-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  (ind-Maybe {B = B} ∘ ev-Maybe {B = B}) ~ id
isretr-ind-Maybe h = eq-htpy (isretr-ind-Maybe' h)

dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-equiv (ev-Maybe {B = B})
dependent-universal-property-Maybe =
  is-equiv-has-inverse
    ind-Maybe
    issec-ind-Maybe
    isretr-ind-Maybe

equiv-dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} (B : Maybe A → UU l2) →
  ((x : Maybe A) → B x) ≃ (((x : A) → B (unit-Maybe x)) × B exception-Maybe)
equiv-dependent-universal-property-Maybe B =
  pair ev-Maybe dependent-universal-property-Maybe

equiv-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (Maybe A → B) ≃ ((A → B) × B)
equiv-universal-property-Maybe {l1} {l2} {A} {B} =
  equiv-dependent-universal-property-Maybe (λ x → B)

mere-equiv-UU-Fin : {k : ℕ} (X : UU-Fin k) → mere-equiv (Fin k) (type-UU-Fin X)
mere-equiv-UU-Fin X = pr2 X

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (has-cardinality X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

mere-equiv-has-finite-cardinality :
  {l : Level} {X : UU l} (c : has-finite-cardinality X) →
  type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
mere-equiv-has-finite-cardinality = pr2

all-elements-equal-has-finite-cardinality :
  {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) =
  eq-subtype
    ( λ k → is-prop-type-trunc-Prop)
    ( apply-universal-property-trunc-Prop K
      ( pair (Id k l) (is-set-ℕ k l))
      ( λ (e : Fin k ≃ X) →
        apply-universal-property-trunc-Prop L
          ( pair (Id k l) (is-set-ℕ k l))
          ( λ (f : Fin l ≃ X) → is-injective-Fin ((inv-equiv f) ∘e e))))

is-prop-has-finite-cardinality :
  {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
is-prop-has-finite-cardinality =
  is-prop-all-elements-equal all-elements-equal-has-finite-cardinality

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
has-finite-cardinality-Prop X =
  pair (has-finite-cardinality X) (is-prop-has-finite-cardinality)

is-finite-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → is-finite X
is-finite-has-finite-cardinality {l} {X} (pair k K) =
  apply-universal-property-trunc-Prop K
    ( is-finite-Prop X)
    ( is-finite-count ∘ (pair k))

is-finite-has-cardinality :
  {l : Level} {X : UU l} {k : ℕ} → has-cardinality X k → is-finite X
is-finite-has-cardinality {k = k} H =
  is-finite-has-finite-cardinality (pair k H)

has-finite-cardinality-count :
  {l1  : Level} {X : UU l1} → count X → has-finite-cardinality X
has-finite-cardinality-count e =
  pair (number-of-elements-count e) (unit-trunc-Prop (equiv-count e))

has-finite-cardinality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-finite-cardinality X
has-finite-cardinality-is-finite =
  map-universal-property-trunc-Prop
    ( has-finite-cardinality-Prop _)
    ( has-finite-cardinality-count)

number-of-elements-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → ℕ
number-of-elements-is-finite =
  number-of-elements-has-finite-cardinality ∘ has-finite-cardinality-is-finite

mere-equiv-is-finite :
  {l1 : Level} {X : UU l1} (f : is-finite X) →
  mere-equiv (Fin (number-of-elements-is-finite f)) X
mere-equiv-is-finite f =
  mere-equiv-has-finite-cardinality (has-finite-cardinality-is-finite f)

compute-number-of-elements-is-finite :
  {l1 : Level} {X : UU l1} (e : count X) (f : is-finite X) →
  Id (number-of-elements-count e) (number-of-elements-is-finite f)
compute-number-of-elements-is-finite e f =
  ind-trunc-Prop
    ( λ g → Id-Prop ℕ-Set ( number-of-elements-count e)
                          ( number-of-elements-is-finite g))
    ( λ g →
      ( is-injective-Fin ((inv-equiv (equiv-count g)) ∘e (equiv-count e))) ∙
      ( ap pr1
        ( eq-is-prop' is-prop-has-finite-cardinality
          ( has-finite-cardinality-count g)
          ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
    ( f)

is-finite-empty : is-finite empty
is-finite-empty = is-finite-count count-empty

is-finite-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → is-finite X
is-finite-is-empty H = is-finite-count (count-is-empty H)

empty-𝔽 : 𝔽
empty-𝔽 = pair empty (is-finite-is-empty id)

empty-UU-Fin : UU-Fin zero-ℕ
empty-UU-Fin = pair empty (unit-trunc-Prop equiv-id)

is-finite-unit : is-finite unit
is-finite-unit = is-finite-count count-unit

unit-𝔽 : 𝔽
unit-𝔽 = pair unit is-finite-unit

unit-UU-Fin : UU-Fin one-ℕ
unit-UU-Fin = pair unit (unit-trunc-Prop (left-unit-law-coprod unit))

is-finite-is-contr :
  {l1 : Level} {X : UU l1} → is-contr X → is-finite X
is-finite-is-contr H = is-finite-count (count-is-contr H)

is-finite-is-decidable-Prop :
  {l : Level} (P : UU-Prop l) →
  is-decidable (type-Prop P) → is-finite (type-Prop P)
is-finite-is-decidable-Prop P (inl x) =
  is-finite-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) x)
is-finite-is-decidable-Prop P (inr x) =
  is-finite-is-empty x

is-finite-Fin : {k : ℕ} → is-finite (Fin k)
is-finite-Fin {k} = is-finite-count (count-Fin k)

Fin-𝔽 : ℕ → 𝔽
Fin-𝔽 k = pair (Fin k) (is-finite-Fin)

Fin-UU-Fin : (k : ℕ) → UU-Fin k
Fin-UU-Fin k = pair (Fin k) (unit-trunc-Prop equiv-id)

raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

equiv-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
equiv-raise-Fin l k = equiv-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise

Fin-UU-Fin-Level : (l : Level) (k : ℕ) → UU-Fin-Level l k
Fin-UU-Fin-Level l k =
  pair (raise-Fin l k) (unit-trunc-Prop (equiv-raise-Fin l k))

is-inhabited-or-empty : {l1 : Level} → UU l1 → UU l1
is-inhabited-or-empty A = coprod (type-trunc-Prop A) (is-empty A)

is-prop-is-inhabited-or-empty :
  {l1 : Level} (A : UU l1) → is-prop (is-inhabited-or-empty A)
is-prop-is-inhabited-or-empty A =
  is-prop-coprod
    ( λ t → apply-universal-property-trunc-Prop t empty-Prop)
    ( is-prop-type-trunc-Prop)
    ( is-prop-neg)

is-inhabited-or-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
is-inhabited-or-empty-Prop A =
  pair (is-inhabited-or-empty A) (is-prop-is-inhabited-or-empty A)

is-inhabited-or-empty-count :
  {l1 : Level} {A : UU l1} → count A → is-inhabited-or-empty A
is-inhabited-or-empty-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-inhabited-or-empty-count (pair (succ-ℕ k) e) =
  inl (unit-trunc-Prop (map-equiv e zero-Fin))

is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f =
  apply-universal-property-trunc-Prop f
    ( is-inhabited-or-empty-Prop A)
    ( is-inhabited-or-empty-count)

is-decidable-type-trunc-Prop-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-finite H =
  map-coprod
    ( id)
    ( map-universal-property-trunc-Prop empty-Prop)
    ( is-inhabited-or-empty-is-finite H)

is-finite-base-is-finite-Σ-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop A)
    ( λ e →
      is-finite-count
        ( count-equiv
          ( ( equiv-total-fib-map-section b) ∘e
            ( equiv-tot
              ( λ t →
                ( equiv-tot (λ x → equiv-eq-pair-Σ (map-section b x) t)) ∘e
                ( ( assoc-Σ A
                    ( λ (x : A) → Id x (pr1 t))
                    ( λ s → Id (tr B (pr2 s) (b (pr1 s))) (pr2 t))) ∘e
                  ( inv-left-unit-law-Σ-is-contr
                    ( is-contr-total-path' (pr1 t))
                    ( pair (pr1 t) refl))))))
          ( count-Σ e
            ( λ t →
              count-eq
                ( has-decidable-equality-is-finite (g (pr1 t)))
                ( b (pr1 t))
                ( pr2 t)))))

is-finite-base-is-finite-Σ-mere-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-trunc-Prop ((x : A) → B x) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
  apply-universal-property-trunc-Prop H
    ( is-finite-Prop A)
    ( λ b → is-finite-base-is-finite-Σ-section b f g)

global-choice-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice X → global-choice Y
global-choice-equiv e f =
  (map-equiv e ∘ f) ∘ (functor-trunc-Prop (map-inv-equiv e))

global-choice-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice Y → global-choice X
global-choice-equiv' e f =
  (map-inv-equiv e ∘ f) ∘ (functor-trunc-Prop (map-equiv e))

global-choice-count :
  {l : Level} {A : UU l} → count A → global-choice A
global-choice-count (pair zero-ℕ e) t =
  ex-falso
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
      ( t))
global-choice-count (pair (succ-ℕ k) e) t = map-equiv e zero-Fin

global-choice-decidable-subtype-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → ((x : Fin k) → is-prop (P x)) →
  ((x : Fin k) → is-decidable (P x)) → global-choice (Σ (Fin k) P)
global-choice-decidable-subtype-Fin {l} {zero-ℕ} P H d t =
  ex-falso (apply-universal-property-trunc-Prop t empty-Prop pr1)
global-choice-decidable-subtype-Fin {l} {succ-ℕ k} P H d t =
  map-Σ P
    ( mod-succ-ℕ k)
    ( λ x → id)
    ( global-choice-total-Q
      ( functor-trunc-Prop
        ( map-Σ Q
          ( nat-Fin)
          ( λ x → tr P (inv (issec-nat-Fin x))))
        ( t)))
  where
  Q : ℕ → UU l
  Q n = P (mod-succ-ℕ k n)
  is-prop-Q : (n : ℕ) → is-prop (Q n)
  is-prop-Q n = H (mod-succ-ℕ k n)
  is-decidable-Q : (n : ℕ) → is-decidable (Q n)
  is-decidable-Q n = d (mod-succ-ℕ k n)
  global-choice-total-Q : global-choice (Σ ℕ Q)
  global-choice-total-Q =
    global-choice-decidable-subtype-ℕ is-prop-Q is-decidable-Q

global-choice-decidable-subtype-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {P : A → UU l2} →
  ((x : A) → is-decidable (P x)) → ((x : A) → is-prop (P x)) →
  global-choice (Σ A P)
global-choice-decidable-subtype-count e {P} d H =
  global-choice-equiv
    ( equiv-Σ-equiv-base P (equiv-count e))
    ( global-choice-decidable-subtype-Fin
      ( λ x → P (map-equiv-count e x))
      ( λ x → H (map-equiv-count e x))
      ( λ x → d (map-equiv-count e x)))

global-choice-emb-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  ((x : A) → is-decidable (fib (map-emb f) x)) → global-choice B
global-choice-emb-count e f d t =
  map-equiv-total-fib
    ( map-emb f)
    ( global-choice-decidable-subtype-count e d
      ( is-prop-map-emb f)
      ( functor-trunc-Prop
        ( map-inv-equiv-total-fib (map-emb f))
        ( t)))

is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e zero-Fin)

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-decidable-Prop :
  {l1 : Level} (P : UU-Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-decidable-Prop P (inr f) = count-is-empty f

is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ e f x)

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  count X → count (Σ X (λ x → type-Prop (P x)))
count-decidable-subtype P d e =
  count-Σ e (λ x → count-decidable-Prop (P x) (d x))

count-total-subtype-is-finite-total-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : A → UU-Prop l2) →
  is-finite (Σ A (λ x → type-Prop (P x))) → count (Σ A (λ x → type-Prop (P x)))
count-total-subtype-is-finite-total-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype P d e
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-Σ e g x)

is-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-finite A → is-finite B
is-finite-equiv e =
  map-universal-property-trunc-Prop
    ( is-finite-Prop _)
    ( is-finite-count ∘ (count-equiv e))

is-finite-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-finite A → is-finite B
is-finite-is-equiv is-equiv-f =
  map-universal-property-trunc-Prop
    ( is-finite-Prop _)
    ( is-finite-count ∘ (count-equiv (pair _ is-equiv-f)))

is-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-finite B → is-finite A
is-finite-equiv' e = is-finite-equiv (inv-equiv e)

count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fib (map-emb f))
    ( count-total-subtype-is-finite-total-subtype e
      ( λ x → pair (fib (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fib (map-emb f))
        ( H)))

choice-count-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
  global-choice-count
    ( count-domain-emb-is-finite-domain-emb e
      ( emb-fiber-inclusion B K x)
      ( g x))
    ( H x)

choice-is-finite-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H =
  apply-universal-property-trunc-Prop f
    ( trunc-Prop ((x : A) → B x))
    ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))

is-finite-base-is-finite-Σ-merely-inhabited :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → (b : (x : A) → type-trunc-Prop (B x)) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
  is-finite-base-is-finite-Σ-mere-section
    ( choice-is-finite-Σ-is-finite-fiber K f g b)
    ( f)
    ( g)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (K : is-finite A)
  where

  is-finite-codomain-has-decidable-equality :
    is-surjective f → has-decidable-equality B → is-finite B
  is-finite-codomain-has-decidable-equality H d =
    is-finite-base-is-finite-Σ-merely-inhabited
      ( is-set-has-decidable-equality d)
      ( H)
      ( is-finite-equiv' (equiv-total-fib f) K)
      ( λ b → is-finite-Σ K (λ a → is-finite-eq d))

is-finite-im-has-decidable-equality :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (K : is-finite A) →
  has-decidable-equality B → is-finite (im f)
is-finite-im-has-decidable-equality {f = f} K d =
  is-finite-codomain-has-decidable-equality K
    ( is-surjective-map-unit-im f)
    ( λ x y →
      is-decidable-equiv
        ( equiv-Eq-total-subtype-eq (λ u → is-prop-type-trunc-Prop) x y)
        ( d (pr1 x) (pr1 y)))

is-finite-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (coprod X Y)
is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (coprod X Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop is-finite-Y
        ( is-finite-Prop (coprod X Y))
        ( is-finite-count ∘ (count-coprod e)))

is-finite-mere-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
  is-finite A → is-finite B
is-finite-mere-equiv e H =
  apply-universal-property-trunc-Prop e
    ( is-finite-Prop _)
    ( λ e' → is-finite-equiv e' H)

is-finite-type-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → is-finite (type-UU-Fin-Level X)
is-finite-type-UU-Fin-Level X =
  is-finite-mere-equiv
    ( mere-equiv-UU-Fin-Level X)
    ( is-finite-Fin)

is-finite-type-UU-Fin :
  {k : ℕ} (X : UU-Fin k) → is-finite (type-UU-Fin X)
is-finite-type-UU-Fin X = is-finite-type-UU-Fin-Level X

is-decidable-Σ-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  is-decidable (Σ A (C ∘ inl)) → is-decidable (Σ B (C ∘ inr)) →
  is-decidable (Σ (coprod A B) C)
is-decidable-Σ-coprod {l1} {l2} {l3} {A} {B} C dA dB =
  is-decidable-equiv
    ( right-distributive-Σ-coprod A B C)
    ( is-decidable-coprod dA dB)

is-decidable-Σ-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable (Σ A (B ∘ unit-Maybe)) → is-decidable (B exception-Maybe) →
  is-decidable (Σ (Maybe A) B)
is-decidable-Σ-Maybe {l1} {l2} {A} {B} dA de =
  is-decidable-Σ-coprod B dA
    ( is-decidable-equiv
      ( left-unit-law-Σ (B ∘ inr))
      ( de))

is-decidable-Σ-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ A C) → is-decidable (Σ B D)
is-decidable-Σ-equiv {D = D} e f =
  is-decidable-equiv' (equiv-Σ D e f)

is-decidable-Σ-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ B D) → is-decidable (Σ A C)
is-decidable-Σ-equiv' {D = D} e f =
  is-decidable-equiv (equiv-Σ D e f) 

is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → equiv-id)
    ( is-decidable-Σ-Fin (λ x → d (map-equiv-count e x)))

is-decidable-Π-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : coprod A B → UU l3} →
  is-decidable ((a : A) → C (inl a)) → is-decidable ((b : B) → C (inr b)) →
  is-decidable ((x : coprod A B) → C x)
is-decidable-Π-coprod {C = C} dA dB =
  is-decidable-equiv
    ( equiv-dependent-universal-property-coprod C)
    ( is-decidable-prod dA dB)

is-decidable-Π-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable ((x : A) → B (unit-Maybe x)) → is-decidable (B exception-Maybe) →
  is-decidable ((x : Maybe A) → B x)
is-decidable-Π-Maybe {B = B} du de =
  is-decidable-equiv
    ( equiv-dependent-universal-property-Maybe B)
    ( is-decidable-prod du de)

is-decidable-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
is-decidable-Π-Fin {l1} {zero-ℕ} {B} d = inl ind-empty
is-decidable-Π-Fin {l1} {succ-ℕ k} {B} d =
  is-decidable-Π-Maybe
    ( is-decidable-Π-Fin (λ x → d (inl x)))
    ( d (inr star))

is-decidable-Π-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((x : A) → C x) → is-decidable ((y : B) → D y)
is-decidable-Π-equiv {D = D} e f = is-decidable-equiv' (equiv-Π D e f)

is-decidable-Π-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((y : B) → D y) → is-decidable ((x : A) → C x)
is-decidable-Π-equiv' {D = D} e f = is-decidable-equiv (equiv-Π D e f)

is-decidable-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-count e d =
  is-decidable-Π-equiv
    ( equiv-count e)
    ( λ x → equiv-id)
    ( is-decidable-Π-Fin (λ x → d (map-equiv-count e x)))

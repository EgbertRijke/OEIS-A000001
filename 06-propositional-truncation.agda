{-# OPTIONS --without-K --exact-split #-}

module 06-propositional-truncation where

open import 05-function-extensionality public

precomp-Prop :
  { l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) →
  (A → type-Prop P) → (Q : UU-Prop l3) →
  (type-hom-Prop P Q) → (A → type-Prop Q)
precomp-Prop P f Q g = g ∘ f

is-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
is-propositional-truncation l P f =
  (Q : UU-Prop l) → is-equiv (precomp-Prop P f Q)

postulate type-trunc-Prop : {l : Level} → UU l → UU l

postulate unit-trunc-Prop : {l : Level} {A : UU l} → A → type-trunc-Prop A

postulate
  all-elements-equal-type-trunc-Prop :
    {l : Level} {A : UU l} → all-elements-equal (type-trunc-Prop A)

is-prop-type-trunc-Prop : {l : Level} {A : UU l} → is-prop (type-trunc-Prop A)
is-prop-type-trunc-Prop {l} {A} =
  is-prop-all-elements-equal all-elements-equal-type-trunc-Prop

trunc-Prop : {l : Level} → UU l → UU-Prop l
pr1 (trunc-Prop A) = type-trunc-Prop A
pr2 (trunc-Prop A) = is-prop-type-trunc-Prop

extension-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
extension-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) → (A → type-Prop Q) → (type-hom-Prop P Q)

is-propositional-truncation-extension-property :
  { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2)
  ( f : A → type-Prop P) →
  ( {l : Level} → extension-property-propositional-truncation l P f) →
  ( {l : Level} → is-propositional-truncation l P f)
is-propositional-truncation-extension-property P f up-P {l} Q =
  is-equiv-is-prop
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( up-P Q)

postulate
  ind-trunc-Prop' :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU l)
    (f : (x : A) → P (unit-trunc-Prop x))
    (g : (x y : type-trunc-Prop A) (u : P x) (v : P y) →
         Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
    (x : type-trunc-Prop A) → P x

is-prop-condition-ind-trunc-Prop' :
  {l1 l2 : Level} {A : UU l1} {P : type-trunc-Prop A → UU l2} →
  ( (x y : type-trunc-Prop A) (u : P x) (v : P y) →
    Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
  (x : type-trunc-Prop A) → is-prop (P x)
is-prop-condition-ind-trunc-Prop' {P = P} H x =
  is-prop-all-elements-equal
    ( λ u v →
      ( ap ( λ γ → tr P γ u)
           ( eq-is-contr (is-prop-type-trunc-Prop x x))) ∙
      ( H x x u v))

ind-trunc-Prop :
  {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l) →
  ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
  (( y : type-trunc-Prop A) → type-Prop (P y))
ind-trunc-Prop P f =
  ind-trunc-Prop' (type-Prop ∘ P) f
    ( λ x y u v → eq-is-prop (is-prop-type-Prop (P y))) 

is-propositional-truncation-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) →
  is-propositional-truncation l2 (trunc-Prop A) unit-trunc-Prop
is-propositional-truncation-trunc-Prop A =
  is-propositional-truncation-extension-property
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( λ {l} Q → ind-trunc-Prop (λ x → Q))

universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) (g : A → type-Prop Q) →
  is-contr (Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~  g))

universal-property-is-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) →
  is-propositional-truncation l P f →
  universal-property-propositional-truncation l P f
universal-property-is-propositional-truncation l P f is-ptr-f Q g =
  is-contr-equiv'
    ( Σ (type-hom-Prop P Q) (λ h → Id (h ∘ f) g))
    ( equiv-tot (λ h → equiv-funext))
    ( is-contr-map-is-equiv (is-ptr-f Q) g)

map-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  ({l : Level} → is-propositional-truncation l P f) →
  (Q : UU-Prop l3) (g : A → type-Prop Q) → type-hom-Prop P Q
map-is-propositional-truncation P f is-ptr-f Q g =
  pr1
    ( center
      ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

htpy-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  (is-ptr-f : {l : Level} → is-propositional-truncation l P f) →
  (Q : UU-Prop l3) (g : A → type-Prop Q) →
  ((map-is-propositional-truncation P f is-ptr-f Q g) ∘ f) ~ g
htpy-is-propositional-truncation P f is-ptr-f Q g =
  pr2
    ( center
      ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

is-propositional-truncation-universal-property :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) →
  universal-property-propositional-truncation l P f →
  is-propositional-truncation l P f
is-propositional-truncation-universal-property l P f up-f Q =
  is-equiv-is-contr-map
    ( λ g → is-contr-equiv
      ( Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~ g))
      ( equiv-tot (λ h → equiv-funext))
      ( up-f Q g))

universal-property-trunc-Prop : {l1 l2 : Level} (A : UU l1) →
  universal-property-propositional-truncation l2
    ( trunc-Prop A)
    ( unit-trunc-Prop)
universal-property-trunc-Prop A =
  universal-property-is-propositional-truncation _
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)

map-universal-property-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  (A → type-Prop P) → type-hom-Prop (trunc-Prop A) P
map-universal-property-trunc-Prop {A = A} P f =
  map-is-propositional-truncation
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)
    ( P)
    ( f)

apply-universal-property-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Prop A) (P : UU-Prop l2) →
  (A → type-Prop P) → type-Prop P
apply-universal-property-trunc-Prop t P f =
  map-universal-property-trunc-Prop P f t

unique-functor-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr
    ( Σ ( type-hom-Prop (trunc-Prop A) (trunc-Prop B))
        ( λ h → (h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)))
unique-functor-trunc-Prop {l1} {l2} {A} {B} f =
  universal-property-trunc-Prop A (trunc-Prop B) (unit-trunc-Prop ∘ f)

functor-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → type-hom-Prop (trunc-Prop A) (trunc-Prop B)
functor-trunc-Prop f =
  pr1 (center (unique-functor-trunc-Prop f))

htpy-functor-trunc-Prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( (functor-trunc-Prop f) ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)
htpy-functor-trunc-Prop f =
  pr2 (center (unique-functor-trunc-Prop f))

htpy-uniqueness-functor-trunc-Prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( h : type-hom-Prop (trunc-Prop A) (trunc-Prop B)) →
  ( ( h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)) →
  (functor-trunc-Prop f) ~ h
htpy-uniqueness-functor-trunc-Prop f h H =
  htpy-eq (ap pr1 (contraction (unique-functor-trunc-Prop f) (pair h H)))

id-functor-trunc-Prop :
  { l1 : Level} {A : UU l1} → functor-trunc-Prop (id {A = A}) ~ id
id-functor-trunc-Prop {l1} {A} =
  htpy-uniqueness-functor-trunc-Prop id id refl-htpy

comp-functor-trunc-Prop :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  ( g : B → C) (f : A → B) →
  ( functor-trunc-Prop (g ∘ f)) ~
  ( (functor-trunc-Prop g) ∘ (functor-trunc-Prop f))
comp-functor-trunc-Prop g f =
  htpy-uniqueness-functor-trunc-Prop
    ( g ∘ f)
    ( (functor-trunc-Prop g) ∘ (functor-trunc-Prop f))
    ( ( (functor-trunc-Prop g) ·l (htpy-functor-trunc-Prop f)) ∙h
      ( ( htpy-functor-trunc-Prop g) ·r f))

map-equiv-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Prop A → type-trunc-Prop B
map-equiv-trunc-Prop e = functor-trunc-Prop (map-equiv e)

map-inv-equiv-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Prop B → type-trunc-Prop A
map-inv-equiv-trunc-Prop e = map-equiv-trunc-Prop (inv-equiv e)

equiv-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (type-trunc-Prop A ≃ type-trunc-Prop B)
pr1 (equiv-trunc-Prop e) = map-equiv-trunc-Prop e
pr2 (equiv-trunc-Prop e) =
  is-equiv-is-prop
    ( is-prop-type-trunc-Prop)
    ( is-prop-type-trunc-Prop)
    ( map-inv-equiv-trunc-Prop e)

is-propositional-truncation-prod :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P)
  {A' : UU l3} (P' : UU-Prop l4) (f' : A' → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  {l : Level} → is-propositional-truncation l (prod-Prop P P') (map-prod f f')
is-propositional-truncation-prod P f P' f' is-ptr-f is-ptr-f' Q =
  is-equiv-top-is-equiv-bottom-square
    ( ev-pair)
    ( ev-pair)
    ( precomp (map-prod f f') (type-Prop Q))
    ( λ h a a' → h (f a) (f' a'))
    ( refl-htpy)
    ( is-equiv-ev-pair)
    ( is-equiv-ev-pair)
    ( is-equiv-comp'
      ( λ h a a' → h a (f' a'))
      ( λ h a p' → h (f a) p')
      ( is-ptr-f (pair (type-hom-Prop P' Q) (is-prop-type-hom-Prop P' Q)))
      ( is-equiv-map-Π
        ( λ a g a' → g (f' a'))
        ( λ a → is-ptr-f' Q)))

is-equiv-is-ptruncation-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  is-equiv h
is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' =
  is-equiv-is-prop
    ( is-prop-type-Prop P)
    ( is-prop-type-Prop P')
    ( map-inv-is-equiv (is-ptr-P' P) f)

is-ptruncation-is-ptruncation-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
  is-equiv h → ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f')
is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f =
  is-propositional-truncation-extension-property P' f'
    ( λ R g →
      ( map-is-propositional-truncation P f is-ptr-f R g) ∘
      ( map-inv-is-equiv is-equiv-h))

is-ptruncation-is-equiv-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
  ({l : Level} → is-propositional-truncation l P' f') → is-equiv h →
  ({l : Level} → is-propositional-truncation l P f)
is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h =
  is-propositional-truncation-extension-property P f
    ( λ R g → (map-is-propositional-truncation P' f' is-ptr-f' R g) ∘ h)

is-uniquely-unique-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  is-contr (Σ (type-equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' =
  is-contr-total-Eq-substructure
    ( universal-property-is-propositional-truncation _ P f is-ptr-f P' f')
    ( is-subtype-is-equiv)
    ( map-is-propositional-truncation P f is-ptr-f P' f')
    ( htpy-is-propositional-truncation P f is-ptr-f P' f')
    ( is-equiv-is-ptruncation-is-ptruncation  P P' f f'
      ( map-is-propositional-truncation P f is-ptr-f P' f')
      ( htpy-is-propositional-truncation P f is-ptr-f P' f')
      ( λ {l} → is-ptr-f)
      ( λ {l} → is-ptr-f'))

equiv-prod-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-prod-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-prod unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) → type-trunc-Prop A × type-trunc-Prop B
map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( type-trunc-Prop A × type-trunc-Prop B)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-prod unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop A × type-trunc-Prop B → type-trunc-Prop (A × B)
map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

is-equiv-map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-equiv (map-distributive-trunc-prod-Prop {A = A} {B = B})
is-equiv-map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  is-equiv-is-prop
    ( is-prop-type-trunc-Prop)
    ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
    ( map-inv-distributive-trunc-prod-Prop)

distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) ≃ (type-trunc-Prop A × type-trunc-Prop B)
pr1 distributive-trunc-prod-Prop = map-distributive-trunc-prod-Prop
pr2 distributive-trunc-prod-Prop = is-equiv-map-distributive-trunc-prod-Prop

is-equiv-map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-equiv (map-inv-distributive-trunc-prod-Prop {A = A} {B = B})
is-equiv-map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  is-equiv-is-prop
    ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
    ( is-prop-type-trunc-Prop)
    ( map-distributive-trunc-prod-Prop)

inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( type-trunc-Prop A × type-trunc-Prop B) ≃ type-trunc-Prop (A × B)
pr1 inv-distributive-trunc-prod-Prop =
  map-inv-distributive-trunc-prod-Prop
pr2 inv-distributive-trunc-prod-Prop =
  is-equiv-map-inv-distributive-trunc-prod-Prop

mere-eq-Prop :
  {l : Level} {A : UU l} → A → A → UU-Prop l
mere-eq-Prop x y = trunc-Prop (Id x y)

mere-eq : {l : Level} {A : UU l} → A → A → UU l
mere-eq x y = type-trunc-Prop (Id x y)

refl-mere-eq :
  {l : Level} {A : UU l} {x : A} → mere-eq x x
refl-mere-eq = unit-trunc-Prop refl

symm-mere-eq :
  {l : Level} {A : UU l} {x y : A} → mere-eq x y → mere-eq y x
symm-mere-eq {x = x} {y} =
  functor-trunc-Prop inv

trans-mere-eq :
  {l : Level} {A : UU l} {x y z : A} →
  mere-eq x y → mere-eq y z → mere-eq x z
trans-mere-eq {x = x} {y} {z} p q =
  apply-universal-property-trunc-Prop p
    ( mere-eq-Prop x z)
    ( λ p' → functor-trunc-Prop (λ q' → p' ∙ q') q)

exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
exists-Prop {l1} {l2} {A} P = trunc-Prop (Σ A (λ x → type-Prop (P x)))

exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
exists P = type-Prop (exists-Prop P)

is-prop-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → is-prop (exists P)
is-prop-exists P = is-prop-type-Prop (exists-Prop P)

intro-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  (x : A) → type-Prop (P x) → exists P
intro-exists {A = A} P x p = unit-trunc-Prop (pair x p)

∃-Prop :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU-Prop (l1 ⊔ l2)
∃-Prop {A = A} B = trunc-Prop (Σ A B)

∃ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
∃ B = type-Prop (∃-Prop B)

is-prop-∃ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-prop (∃ B)
is-prop-∃ B = is-prop-type-Prop (∃-Prop B)

intro-∃ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a) →
  ∃ B
intro-∃ a b = unit-trunc-Prop (pair a b)

is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → UU-Prop l → UU-Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)

is-empty-type-trunc-Prop :
  {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
is-empty-type-trunc-Prop f =
  map-universal-property-trunc-Prop empty-Prop f

global-choice : {l : Level} → UU l → UU l
global-choice X = type-trunc-Prop X → X

is-prop-is-lower-bound-ℕ :
  {l1 : Level} {P : ℕ → UU l1} (x : ℕ) → is-prop (is-lower-bound-ℕ P x)
is-prop-is-lower-bound-ℕ x =
  is-prop-Π (λ y → is-prop-function-type (is-prop-leq-ℕ x y))

all-elements-equal-minimal-element-ℕ :
  {l1 : Level} {P : ℕ → UU l1} →
  ((x : ℕ) → is-prop (P x)) → all-elements-equal (minimal-element-ℕ P)
all-elements-equal-minimal-element-ℕ {l1} {P} H (pair x (pair p l)) (pair y (pair q k)) =
  eq-subtype
    ( λ n → is-prop-prod (H n) (is-prop-is-lower-bound-ℕ n))
    ( antisymmetric-leq-ℕ x y (l y q) (k x p))

is-prop-minimal-element-ℕ :
  {l1 : Level} {P : ℕ → UU l1} →
  ((x : ℕ) → is-prop (P x)) → is-prop (minimal-element-ℕ P)
is-prop-minimal-element-ℕ H =
  is-prop-all-elements-equal (all-elements-equal-minimal-element-ℕ H)

minimal-element-ℕ-Prop :
  {l1 : Level} {P : ℕ → UU l1} → ((x : ℕ) → is-prop (P x)) → UU-Prop l1
pr1 (minimal-element-ℕ-Prop {l1} {P} H) = minimal-element-ℕ P
pr2 (minimal-element-ℕ-Prop {l1} {P} H) = is-prop-minimal-element-ℕ H

global-choice-decidable-subtype-ℕ :
  {l1 : Level} {P : ℕ → UU l1} (H : (x : ℕ) → is-prop (P x))
  (d : (x : ℕ) → is-decidable (P x)) → global-choice (Σ ℕ P)
global-choice-decidable-subtype-ℕ {l1} {P} H d t =
  tot ( λ x → pr1)
      ( apply-universal-property-trunc-Prop t
        ( minimal-element-ℕ-Prop H)
        ( well-ordering-principle-ℕ P d))

dependent-universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
dependent-universal-property-propositional-truncation l {l1} {l2} {A} P f =
  ( Q : type-Prop P → UU-Prop l) → is-equiv (precomp-Π f (type-Prop ∘ Q))

dependent-universal-property-is-propositional-truncation :
  { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  ( {l : Level} → is-propositional-truncation l P f) →
  ( {l : Level} → dependent-universal-property-propositional-truncation l P f)
dependent-universal-property-is-propositional-truncation
  {l1} {l2} {A} P f is-ptr-f Q =
  is-fiberwise-equiv-is-equiv-map-Σ
    ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
    ( precomp f (type-Prop P))
    ( λ h → precomp-Π f (λ p → type-Prop (Q (h p))))
    ( is-ptr-f P)
    ( is-equiv-top-is-equiv-bottom-square
      ( inv-choice-∞
        { C = λ (x : type-Prop P) (p : type-Prop P) → type-Prop (Q p)})
      ( inv-choice-∞
        { C = λ (x : A) (p : type-Prop P) → type-Prop (Q p)})
      ( map-Σ
        ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
        ( precomp f (type-Prop P))
        ( λ h → precomp-Π f (λ p → type-Prop (Q (h p)))))
      ( precomp f (Σ (type-Prop P) (λ p → type-Prop (Q p))))
      ( ind-Σ (λ h h' → refl))
      ( is-equiv-inv-choice-∞)
      ( is-equiv-inv-choice-∞)
      ( is-ptr-f (Σ-Prop P Q)))
    ( id {A = type-Prop P})

dependent-universal-property-trunc-Prop :
  {l1 : Level} {A : UU l1} {l : Level} →
    dependent-universal-property-propositional-truncation l
    ( trunc-Prop A)
    ( unit-trunc-Prop)
dependent-universal-property-trunc-Prop {A = A} =
  dependent-universal-property-is-propositional-truncation
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)

module _
  {l1 l2 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l2)
  where
  
  equiv-dependent-universal-property-trunc-Prop :
    ((y : type-trunc-Prop A) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (unit-trunc-Prop x)))
  pr1 equiv-dependent-universal-property-trunc-Prop =
    precomp-Π unit-trunc-Prop (type-Prop ∘ P)
  pr2 equiv-dependent-universal-property-trunc-Prop =
    dependent-universal-property-trunc-Prop P
  
  apply-dependent-universal-property-trunc-Prop :
    (y : type-trunc-Prop A) → ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    type-Prop (P y)
  apply-dependent-universal-property-trunc-Prop y f =
    map-inv-equiv equiv-dependent-universal-property-trunc-Prop f y    

--------------------------------------------------------------------------------

-- Image and surjective maps

precomp-emb :
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} ( i : B ↪ X) (q : hom-slice f (map-emb i)) →
  {C : UU l4} ( j : C ↪ X) →
  hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
pr1 (precomp-emb f i q j r) =
  ( map-hom-slice (map-emb i) (map-emb j) r) ∘ (map-hom-slice f (map-emb i) q)
pr2 (precomp-emb f i q j r) =
  ( triangle-hom-slice f (map-emb i) q) ∙h
  ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
    ( map-hom-slice f (map-emb i) q))

is-image :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) → is-equiv (precomp-emb f i q j)

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective {B = B} f = (y : B) → type-trunc-Prop (fib f y)

module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where
    
  im : UU (l1 ⊔ l2)
  im = Σ X (λ x → type-trunc-Prop (fib f x))

  inclusion-im : im → X
  inclusion-im = pr1

  map-unit-im : A → im
  pr1 (map-unit-im a) = f a
  pr2 (map-unit-im a) = unit-trunc-Prop (pair a refl)

  triangle-unit-im : f ~ (inclusion-im ∘ map-unit-im)
  triangle-unit-im a = refl

  unit-im : hom-slice f inclusion-im
  pr1 unit-im = map-unit-im
  pr2 unit-im = triangle-unit-im

  hom-slice-im : hom-slice f inclusion-im
  pr1 hom-slice-im = map-unit-im
  pr2 hom-slice-im = triangle-unit-im

  Eq-im : im → im → UU l1
  Eq-im x y = Id (pr1 x) (pr1 y)

  refl-Eq-im : (x : im) → Eq-im x x
  refl-Eq-im x = refl

  Eq-eq-im : (x y : im) → Id x y → Eq-im x y
  Eq-eq-im x .x refl = refl-Eq-im x

  is-contr-total-Eq-im :
    (x : im) → is-contr (Σ im (Eq-im x))
  is-contr-total-Eq-im x =
    is-contr-total-Eq-substructure
      ( is-contr-total-path (pr1 x))
      ( λ x → is-prop-type-trunc-Prop)
      ( pr1 x)
      ( refl)
      ( pr2 x)

  is-equiv-Eq-eq-im : (x y : im) → is-equiv (Eq-eq-im x y)
  is-equiv-Eq-eq-im x =
    fundamental-theorem-id x
      ( refl-Eq-im x)
      ( is-contr-total-Eq-im x)
      ( Eq-eq-im x)

  equiv-Eq-eq-im : (x y : im) → Id x y ≃ Eq-im x y
  pr1 (equiv-Eq-eq-im x y) = Eq-eq-im x y
  pr2 (equiv-Eq-eq-im x y) = is-equiv-Eq-eq-im x y

  eq-Eq-im : (x y : im) → Eq-im x y → Id x y
  eq-Eq-im x y = map-inv-is-equiv (is-equiv-Eq-eq-im x y)

is-emb-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-emb (inclusion-im f)
is-emb-inclusion-im f =
  is-emb-pr1 (λ x → is-prop-type-trunc-Prop)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
pr1 (emb-im f) = inclusion-im f
pr2 (emb-im f) = is-emb-inclusion-im f

is-injective-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-injective (inclusion-im f)
is-injective-inclusion-im f =
  is-injective-is-emb (is-emb-inclusion-im f)

is-trunc-im :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
  is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
is-trunc-im k f = is-trunc-emb k (emb-im f) 

is-prop-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-prop X → is-prop (im f)
is-prop-im = is-trunc-im neg-two-𝕋

is-set-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-set X → is-set (im f)
is-set-im = is-trunc-im neg-one-𝕋

is-surjective-is-image :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  ({l : Level} → is-image l f i q) →
  is-surjective (map-hom-slice f (map-emb i) q)
is-surjective-is-image {A = A} {B} {X} f i q up-i b =
  apply-universal-property-trunc-Prop β
    ( trunc-Prop (fib (map-hom-slice f (map-emb i) q) b))
    ( γ)
  where
  g : Σ B (λ b → type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)) → X
  g = map-emb i ∘ pr1
  is-emb-g : is-emb g
  is-emb-g = is-emb-comp' (map-emb i) pr1
    ( is-emb-map-emb i)
    ( is-emb-pr1 (λ x → is-prop-type-trunc-Prop))
  α : hom-slice (map-emb i) g
  α = map-inv-is-equiv
        ( up-i
          ( Σ B ( λ b →
                  type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)))
          ( pair g is-emb-g))
        ( pair (map-unit-im (pr1 q)) (pr2 q))
  β : type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)))
  β = pr2 (pr1 α b)
  γ : fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)) →
      type-Prop (trunc-Prop (fib (pr1 q) b))
  γ (pair a p) =
    unit-trunc-Prop
      ( pair a (p ∙ inv (is-injective-is-emb (is-emb-map-emb i) (pr2 α b))))

is-surjective-map-unit-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective (map-unit-im f)
is-surjective-map-unit-im f (pair y z) =
  apply-universal-property-trunc-Prop z
    ( trunc-Prop (fib (map-unit-im f) (pair y z)))
    ( α)
  where
  α : fib f y → type-Prop (trunc-Prop (fib (map-unit-im f) (pair y z)))
  α (pair x p) =
    unit-trunc-Prop (pair x (eq-subtype (λ z → is-prop-type-trunc-Prop) p))

is-prop-hom-slice :
  { l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
is-prop-hom-slice {X = X} f i =
  is-prop-is-equiv
    ( (x : X) → fib f x → fib (map-emb i) x)
    ( fiberwise-hom-hom-slice f (map-emb i))
    ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
    ( is-prop-Π
      ( λ x → is-prop-Π
        ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))

is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image' l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)

is-image-is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-image' l f i q → is-image l f i q
is-image-is-image' l f i q up' C j =
  is-equiv-is-prop
    ( is-prop-hom-slice (map-emb i) j)
    ( is-prop-hom-slice f j)
    ( up' C j)

dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → UU-Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

is-surjective-dependent-universal-property-surj :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ({l : Level} → dependent-universal-property-surj l f) →
  is-surjective f
is-surjective-dependent-universal-property-surj f dup-surj-f =
  map-inv-is-equiv
    ( dup-surj-f (λ b → trunc-Prop (fib f b)))
    ( λ x → unit-trunc-Prop (pair x refl))

square-dependent-universal-property-surj :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (P : B → UU-Prop l3) →
  ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
  ( ( λ h x → h (f x) (pair x refl)) ∘
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
square-dependent-universal-property-surj f P = refl-htpy

dependent-universal-property-surj-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f →
  ({l : Level} → dependent-universal-property-surj l f)
dependent-universal-property-surj-is-surjective f is-surj-f P =
  is-equiv-comp'
    ( λ h x → h (f x) (pair x refl))
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
    ( is-equiv-comp'
      ( λ h y → (h y) ∘ unit-trunc-Prop)
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
      ( is-equiv-map-Π
        ( λ y p z → p)
        ( λ y →
          is-equiv-diagonal-is-contr
            ( is-proof-irrelevant-is-prop
              ( is-prop-type-trunc-Prop)
              ( is-surj-f y))
            ( type-Prop (P y))))
      ( is-equiv-map-Π
        ( λ b g → g ∘ unit-trunc-Prop)
        ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
    ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

equiv-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → UU-Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
pr1 (equiv-dependent-universal-property-surj-is-surjective f H C) h x = h (f x)
pr2 (equiv-dependent-universal-property-surj-is-surjective f H C) =
  dependent-universal-property-surj-is-surjective f H C

is-image-is-surjective' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-surjective (map-hom-slice f (map-emb i) q) →
  ({l : Level} → is-image' l f i q)
is-image-is-surjective' f i q H B' m =
  map-equiv
    ( ( equiv-hom-slice-fiberwise-hom (map-emb i) (map-emb m)) ∘e
      ( ( inv-equiv (reduce-Π-fib (map-emb i) (fib (map-emb m)))) ∘e
        ( inv-equiv
          ( equiv-dependent-universal-property-surj-is-surjective
            ( pr1 q)
            ( H)
            ( λ b →
              pair ( fib (map-emb m) (pr1 i b))
                   ( is-prop-map-emb m (pr1 i b)))) ∘e
          ( ( equiv-map-Π (λ a → equiv-tr (fib (map-emb m)) (pr2 q a))) ∘e
            ( ( reduce-Π-fib f (fib (map-emb m))) ∘e
              ( equiv-fiberwise-hom-hom-slice f (map-emb m)))))))

is-image-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-surjective (map-hom-slice f (map-emb i) q) →
  ({l : Level} → is-image l f i q)
is-image-is-surjective f i q H {l} =
  is-image-is-image' l f i q
    ( is-image-is-surjective' f i q H)

comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
pr1 (comp-hom-slice f g h j i) =
  ( map-hom-slice g h j) ∘ (map-hom-slice f g i)
pr2 (comp-hom-slice f g h j i) =
  ( triangle-hom-slice f g i) ∙h
  ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  {C : UU l4} (j : C ↪ X) (r : hom-slice f (map-emb j))
  where
  
  universal-property-image :
    is-contr
      ( Σ ( hom-slice (map-emb i) (map-emb j))
          ( λ h →
            htpy-hom-slice f
              ( map-emb j)
              ( comp-hom-slice f (map-emb i) (map-emb j) h q)
              ( r)))
  universal-property-image =
    is-contr-equiv'
      ( fib (precomp-emb f i q j) r)
      ( equiv-tot
        ( λ h →
          equiv-htpy-eq-hom-slice f (map-emb j) (precomp-emb f i q j h) r))
      ( is-contr-map-is-equiv (H C j) r)

  hom-slice-universal-property-image : hom-slice (map-emb i) (map-emb j)
  hom-slice-universal-property-image =
    pr1 (center universal-property-image)

  map-hom-slice-universal-property-image : B → C
  map-hom-slice-universal-property-image =
    map-hom-slice (map-emb i) (map-emb j) hom-slice-universal-property-image

  triangle-hom-slice-universal-property-image :
    (map-emb i) ~ (map-emb j ∘ map-hom-slice-universal-property-image)
  triangle-hom-slice-universal-property-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb j)
      ( hom-slice-universal-property-image)

  htpy-hom-slice-universal-property-image :
    htpy-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q))
      ( r)
  htpy-hom-slice-universal-property-image =
    pr2 (center universal-property-image)

  htpy-map-hom-slice-universal-property-image :
    map-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q)) ~
    map-hom-slice f (map-emb j) r
  htpy-map-hom-slice-universal-property-image =
    pr1 htpy-hom-slice-universal-property-image

  tetrahedron-hom-slice-universal-property-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-slice-universal-property-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb j ·l htpy-map-hom-slice-universal-property-image)) ~
    ( triangle-hom-slice f (map-emb j) r)
  tetrahedron-hom-slice-universal-property-image =
    pr2 htpy-hom-slice-universal-property-image

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)

is-equiv-hom-slice-emb :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
  hom-slice (map-emb g) (map-emb f) →
  is-equiv-hom-slice (map-emb f) (map-emb g) h
is-equiv-hom-slice-emb f g h i =
  is-equiv-has-inverse
    ( map-hom-slice (map-emb g) (map-emb f) i)
    ( λ y →
      is-injective-emb g
      ( inv
        ( ( triangle-hom-slice
            ( map-emb g)
            ( map-emb f)
            ( i)
            ( y)) ∙
          ( triangle-hom-slice
            ( map-emb f)
            ( map-emb g)
            ( h)
            ( map-hom-slice (map-emb g) (map-emb f) i y)))))
    ( λ x →
      is-injective-emb f
      ( inv
        ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
          ( triangle-hom-slice (map-emb g) (map-emb f) i
            ( map-hom-slice
              ( map-emb f)
              ( map-emb g)
              ( h)
              ( x))))))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  where
  
  is-equiv-is-image-is-image :
    ({l : Level} → is-image l f i q) →
    ({l : Level} → is-image l f i' q') →
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
  is-equiv-is-image-is-image up-i up-i' =
    is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' B i) q)

  is-image-is-image-is-equiv :
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
    ({l : Level} → is-image l f i q) →
    ({l : Level} → is-image l f i' q')
  is-image-is-image-is-equiv is-equiv-h up-i {l} =
    is-image-is-image' l f i' q'
      ( λ C j r →
        comp-hom-slice
          ( map-emb i')
          ( map-emb i)
          ( map-emb j)
          ( map-inv-is-equiv (up-i C j) r)
          ( pair
            ( map-inv-is-equiv is-equiv-h)
            ( triangle-section
              ( map-emb i)
              ( map-emb i')
              ( map-hom-slice (map-emb i) (map-emb i') h)
              ( triangle-hom-slice (map-emb i) (map-emb i') h)
              ( pair ( map-inv-is-equiv is-equiv-h)
                     ( issec-map-inv-is-equiv is-equiv-h)))))

  is-image-is-equiv-is-image :
    ({l : Level} → is-image l f i' q') →
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
    ({l : Level} → is-image l f i q)
  is-image-is-equiv-is-image up-i' is-equiv-h {l} =
    is-image-is-image' l f i q
      ( λ C j r →
        comp-hom-slice
          ( map-emb i)
          ( map-emb i')
          ( map-emb j)
          ( map-inv-is-equiv (up-i' C j) r)
          ( h))
          
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (Hi : {l : Level} → is-image l f i q)
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (Hi' : {l : Level} → is-image l f i' q')
  where

  uniqueness-image :
    is-contr
      ( Σ ( equiv-slice (map-emb i) (map-emb i'))
          ( λ e →
            htpy-hom-slice f
              ( map-emb i')
              ( comp-hom-slice f
                ( map-emb i)
                ( map-emb i')
                ( hom-equiv-slice (map-emb i) (map-emb i') e)
                ( q))
              ( q')))
  uniqueness-image =
    is-contr-equiv
      ( Σ ( Σ ( hom-slice (map-emb i) (map-emb i'))
              ( λ h →
                htpy-hom-slice f
                  ( map-emb i')
                  ( comp-hom-slice f (map-emb i) (map-emb i') h q)
                  ( q')))
          ( λ h → is-equiv (pr1 (pr1 h))))
      ( ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ
          ( λ h →
            htpy-hom-slice f
              ( map-emb i')
              ( comp-hom-slice f (map-emb i) (map-emb i') (pr1 h) q)
              ( q'))
          ( equiv-right-swap-Σ)
          ( λ { (pair (pair e E) H) → equiv-id})))
      ( is-contr-equiv
        ( is-equiv
          ( map-hom-slice-universal-property-image f i q Hi i' q'))
        ( left-unit-law-Σ-is-contr
          ( universal-property-image f i q Hi i' q')
          ( center (universal-property-image f i q Hi i' q')))
        ( is-proof-irrelevant-is-prop
          ( is-subtype-is-equiv
            ( map-hom-slice-universal-property-image f i q Hi i' q'))
          ( is-equiv-is-image-is-image f i q i' q'
            ( hom-slice-universal-property-image f i q Hi i' q')
            ( Hi)
            ( Hi'))))

  equiv-slice-uniqueness-image : equiv-slice (map-emb i) (map-emb i')
  equiv-slice-uniqueness-image =
    pr1 (center uniqueness-image)

  hom-equiv-slice-uniqueness-image : hom-slice (map-emb i) (map-emb i')
  hom-equiv-slice-uniqueness-image =
    hom-equiv-slice (map-emb i) (map-emb i') (equiv-slice-uniqueness-image)

  map-hom-equiv-slice-uniqueness-image : B → B'
  map-hom-equiv-slice-uniqueness-image =
    map-hom-slice (map-emb i) (map-emb i') (hom-equiv-slice-uniqueness-image)

  is-equiv-map-hom-equiv-slice-uniqueness-image :
    is-equiv map-hom-equiv-slice-uniqueness-image
  is-equiv-map-hom-equiv-slice-uniqueness-image =
    is-equiv-map-equiv (pr1 equiv-slice-uniqueness-image)

  equiv-equiv-slice-uniqueness-image : B ≃ B'
  pr1 equiv-equiv-slice-uniqueness-image = map-hom-equiv-slice-uniqueness-image
  pr2 equiv-equiv-slice-uniqueness-image =
    is-equiv-map-hom-equiv-slice-uniqueness-image

  triangle-hom-equiv-slice-uniqueness-image :
    (map-emb i) ~ (map-emb i' ∘ map-hom-equiv-slice-uniqueness-image)
  triangle-hom-equiv-slice-uniqueness-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb i')
      ( hom-equiv-slice-uniqueness-image)

  htpy-equiv-slice-uniqueness-image :
    htpy-hom-slice f
      ( map-emb i')
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb i')
        ( hom-equiv-slice-uniqueness-image)
        ( q))
      ( q')
  htpy-equiv-slice-uniqueness-image =
    pr2 (center uniqueness-image)

  htpy-map-hom-equiv-slice-uniqueness-image :
    ( map-hom-equiv-slice-uniqueness-image ∘ map-hom-slice f (map-emb i) q) ~
    ( map-hom-slice f (map-emb i') q')
  htpy-map-hom-equiv-slice-uniqueness-image =
    pr1 htpy-equiv-slice-uniqueness-image

  tetrahedron-hom-equiv-slice-uniqueness-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb i' ·l htpy-map-hom-equiv-slice-uniqueness-image)) ~
    ( triangle-hom-slice f (map-emb i') q')
  tetrahedron-hom-equiv-slice-uniqueness-image =
    pr2 htpy-equiv-slice-uniqueness-image

fiberwise-map-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  (x : X) → type-trunc-Prop (fib f x) → fib (map-emb m) x
fiberwise-map-is-image-im f m h x =
  map-universal-property-trunc-Prop
    { A = (fib f x)}
    ( fib-emb-Prop m x)
    ( λ t →
      pair ( map-hom-slice f (map-emb m) h (pr1 t))
           ( ( inv (triangle-hom-slice f (map-emb m) h (pr1 t))) ∙
             ( pr2 t)))

map-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) → im f → B
map-is-image-im f m h (pair x t) =
  pr1 (fiberwise-map-is-image-im f m h x t)

triangle-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  inclusion-im f ~ ((map-emb m) ∘ (map-is-image-im f m h))
triangle-is-image-im f m h (pair x t) =
  inv (pr2 (fiberwise-map-is-image-im f m h x t))

is-image-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  {l : Level} → is-image l f (emb-im f) (hom-slice-im f)
is-image-im f {l} =
  is-image-is-image'
    l f (emb-im f) (hom-slice-im f)
    ( λ B m h →
      pair ( map-is-image-im f m h)
           ( triangle-is-image-im f m h))

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  where

  uniqueness-im :
    is-contr
      ( Σ ( equiv-slice (inclusion-im f) (map-emb i))
          ( λ e →
            htpy-hom-slice f
              ( map-emb i)
              ( comp-hom-slice f
                ( inclusion-im f)
                ( map-emb i)
                ( hom-equiv-slice (inclusion-im f) (map-emb i) e)
                ( hom-slice-im f))
              ( q)))
  uniqueness-im =
    uniqueness-image f (emb-im f) (hom-slice-im f) (is-image-im f) i q H

  equiv-slice-uniqueness-im : equiv-slice (inclusion-im f) (map-emb i)
  equiv-slice-uniqueness-im =
    pr1 (center uniqueness-im)

  hom-equiv-slice-uniqueness-im : hom-slice (inclusion-im f) (map-emb i)
  hom-equiv-slice-uniqueness-im =
    hom-equiv-slice (inclusion-im f) (map-emb i) equiv-slice-uniqueness-im

  map-hom-equiv-slice-uniqueness-im : im f → B
  map-hom-equiv-slice-uniqueness-im =
    map-hom-slice (inclusion-im f) (map-emb i) hom-equiv-slice-uniqueness-im

  is-equiv-map-hom-equiv-slice-uniqueness-im :
    is-equiv map-hom-equiv-slice-uniqueness-im
  is-equiv-map-hom-equiv-slice-uniqueness-im =
    is-equiv-map-equiv (pr1 equiv-slice-uniqueness-im)

  equiv-equiv-slice-uniqueness-im : im f ≃ B
  pr1 equiv-equiv-slice-uniqueness-im = map-hom-equiv-slice-uniqueness-im
  pr2 equiv-equiv-slice-uniqueness-im =
    is-equiv-map-hom-equiv-slice-uniqueness-im

  triangle-hom-equiv-slice-uniqueness-im :
    (inclusion-im f) ~ (map-emb i ∘ map-hom-equiv-slice-uniqueness-im)
  triangle-hom-equiv-slice-uniqueness-im =
    triangle-hom-slice
      ( inclusion-im f)
      ( map-emb i)
      ( hom-equiv-slice-uniqueness-im)

  htpy-equiv-slice-uniqueness-im :
    htpy-hom-slice f
      ( map-emb i)
      ( comp-hom-slice f
        ( inclusion-im f)
        ( map-emb i)
        ( hom-equiv-slice-uniqueness-im)
        ( hom-slice-im f))
      ( q)
  htpy-equiv-slice-uniqueness-im =
    pr2 (center uniqueness-im)

  htpy-map-hom-equiv-slice-uniqueness-im :
    ( ( map-hom-equiv-slice-uniqueness-im) ∘
      ( map-hom-slice f (inclusion-im f) (hom-slice-im f))) ~
    ( map-hom-slice f (map-emb i) q)
  htpy-map-hom-equiv-slice-uniqueness-im =
    pr1 htpy-equiv-slice-uniqueness-im

  tetrahedron-hom-equiv-slice-uniqueness-im :
    ( ( ( triangle-hom-slice f (inclusion-im f) (hom-slice-im f)) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-im) ·r
          ( map-hom-slice f (inclusion-im f) (hom-slice-im f)))) ∙h
      ( map-emb i ·l htpy-map-hom-equiv-slice-uniqueness-im)) ~
    ( triangle-hom-slice f (map-emb i) q)
  tetrahedron-hom-equiv-slice-uniqueness-im =
    pr2 htpy-equiv-slice-uniqueness-im

is-equiv-is-emb-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-emb f → is-equiv f
is-equiv-is-emb-is-surjective {f = f} H K =
  is-equiv-is-contr-map
    ( λ y →
      is-proof-irrelevant-is-prop
        ( is-prop-map-is-emb K y)
        ( apply-universal-property-trunc-Prop
          ( H y)
          ( fib-emb-Prop (pair f K) y)
          ( id)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-surjective-comp :
    is-surjective g → is-surjective h → is-surjective f
  is-surjective-comp Sg Sh x =
    apply-universal-property-trunc-Prop
      ( Sg x)
      ( trunc-Prop (fib f x))
      ( λ { (pair b refl) →
            apply-universal-property-trunc-Prop
              ( Sh b)
              ( trunc-Prop (fib f (g b)))
              ( λ { (pair a refl) →
                unit-trunc-Prop (pair a (H a))})})

  is-surjective-left-factor :
    is-surjective f → is-surjective g
  is-surjective-left-factor Sf x =
    apply-universal-property-trunc-Prop
      ( Sf x)
      ( trunc-Prop (fib g x))
      ( λ { (pair a refl) →
            unit-trunc-Prop (pair (h a) (inv (H a)))})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  is-surjective-comp' :
    {h : A → B} → is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp' {h} =
    is-surjective-comp (g ∘ h) g h refl-htpy

  is-surjective-left-factor' :
    (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor' h =
    is-surjective-left-factor (g ∘ h) g h refl-htpy

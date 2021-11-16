{-# OPTIONS --without-K --exact-split #-}

module 08-univalence where

open import 07-finite-types

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq refl = equiv-id

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  fundamental-theorem-id' A equiv-id (λ B → equiv-eq) UA

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  fundamental-theorem-id A equiv-id c (λ B → equiv-eq)

ev-id : {i j : Level} {A : UU i} (P : (B : UU i) → (A ≃ B) → UU j) →
  ((B : UU i) (e : A ≃ B) → P B e) → P A equiv-id
ev-id {A = A} P f = f A equiv-id

IND-EQUIV : {i j : Level} {A : UU i} → ((B : UU i) (e : A ≃ B) → UU j) → UU _
IND-EQUIV P = sec (ev-id P)

triangle-ev-id : {i j : Level} {A : UU i}
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
  (ev-pt (pair A equiv-id) P)
  ~ ((ev-id (λ X e → P (pair X e))) ∘ (ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P}))
triangle-ev-id P f = refl

IND-EQUIV-is-contr-total-equiv : {i j : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) →
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) → IND-EQUIV (λ B e → P (pair B e))
IND-EQUIV-is-contr-total-equiv {i} {j} A c P =
  section-comp
    ( ev-pt (pair A equiv-id) P)
    ( ev-id (λ X e → P (pair X e)))
    ( ev-pair)
    ( triangle-ev-id P)
    ( pair ind-Σ refl-htpy)
    ( is-singleton-is-contr
      ( pair A equiv-id)
      ( pair
        ( pair A equiv-id)
        ( λ t →  ( inv (contraction c (pair A equiv-id))) ∙
                 ( contraction c t)))
      ( P))

is-contr-total-equiv-IND-EQUIV : {i : Level} (A : UU i) →
  ( {j : Level} (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
    IND-EQUIV (λ B e → P (pair B e))) →
  is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-IND-EQUIV {i} A ind =
  is-contr-is-singleton
    ( Σ (UU i) (λ X → A ≃ X))
    ( pair A equiv-id)
    ( λ P → section-comp'
      ( ev-pt (pair A equiv-id) P)
      ( ev-id (λ X e → P (pair X e)))
      ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
      ( triangle-ev-id P)
      ( pair ind-Σ refl-htpy)
      ( ind P))

postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = map-inv-is-equiv (univalence A B)

equiv-univalence :
  {i : Level} {A B : UU i} → Id A B ≃ (A ≃ B)
equiv-univalence = pair equiv-eq (univalence _ _)

is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

is-contr-total-equiv' : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → X ≃ A))
is-contr-total-equiv' A =
  is-contr-equiv
    ( Σ (UU _) (λ X → A ≃ X))
    ( equiv-tot (λ X → equiv-inv-equiv))
    ( is-contr-total-equiv A)

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = UU l1 → UU-Prop l2

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (λ X → type-Prop (P X))

equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (X Y : total-subuniverse P) → UU l1
equiv-subuniverse P X Y = (pr1 X) ≃ (pr1 Y)

equiv-eq-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → equiv-subuniverse P s t
equiv-eq-subuniverse P (pair X p) .(pair X p) refl = equiv-id

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (type-Prop (P X))
is-subtype-subuniverse P X = is-prop-type-Prop (P X)

is-contr-total-equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (s : total-subuniverse P) →
  is-contr (Σ (total-subuniverse P) (λ t → equiv-subuniverse P s t))
is-contr-total-equiv-subuniverse P (pair X p) =
  is-contr-total-Eq-substructure
    ( is-contr-total-equiv X)
    ( is-subtype-subuniverse P)
    ( X)
    ( equiv-id)
    ( p)

is-equiv-equiv-eq-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (s t : total-subuniverse P) → is-equiv (equiv-eq-subuniverse P s t)
is-equiv-equiv-eq-subuniverse P (pair X p) =
  fundamental-theorem-id
    ( pair X p)
    ( equiv-id)
    ( is-contr-total-equiv-subuniverse P (pair X p))
    ( equiv-eq-subuniverse P (pair X p))

eq-equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → equiv-subuniverse P s t → Id s t
eq-equiv-subuniverse P {s} {t} =
  map-inv-is-equiv (is-equiv-equiv-eq-subuniverse P s t)

UU-Contr : (l : Level) → UU (lsuc l)
UU-Contr l = total-subuniverse is-contr-Prop

type-UU-Contr : {l : Level} → UU-Contr l → UU l
type-UU-Contr A = pr1 A

is-contr-type-UU-Contr :
  {l : Level} (A : UU-Contr l) → is-contr (type-UU-Contr A)
is-contr-type-UU-Contr A = pr2 A

equiv-UU-Contr :
  {l1 l2 : Level} (X : UU-Contr l1) (Y : UU-Contr l2) → UU (l1 ⊔ l2)
equiv-UU-Contr X Y = type-UU-Contr X ≃ type-UU-Contr Y

equiv-eq-UU-Contr :
  {l1 : Level} (X Y : UU-Contr l1) → Id X Y → equiv-UU-Contr X Y
equiv-eq-UU-Contr X Y = equiv-eq-subuniverse is-contr-Prop X Y

is-equiv-equiv-eq-UU-Contr :
  {l1 : Level} (X Y : UU-Contr l1) → is-equiv (equiv-eq-UU-Contr X Y)
is-equiv-equiv-eq-UU-Contr X Y =
  is-equiv-equiv-eq-subuniverse is-contr-Prop X Y

eq-equiv-UU-Contr :
  {l1 : Level} {X Y : UU-Contr l1} → equiv-UU-Contr X Y → Id X Y
eq-equiv-UU-Contr = eq-equiv-subuniverse is-contr-Prop

center-UU-contr : (l : Level) → UU-Contr l
center-UU-contr l = pair (raise-unit l) is-contr-raise-unit

contraction-UU-contr :
  {l : Level} (A : UU-Contr l) → Id (center-UU-contr l) A
contraction-UU-contr A =
  eq-equiv-UU-Contr
    ( equiv-is-contr is-contr-raise-unit (is-contr-type-UU-Contr A))

is-contr-UU-Contr : (l : Level) → is-contr (UU-Contr l)
is-contr-UU-Contr l = pair (center-UU-contr l) contraction-UU-contr

UU-Trunc : (k : 𝕋) (l : Level) → UU (lsuc l)
UU-Trunc k l = Σ (UU l) (is-trunc k)

type-UU-Trunc : {k : 𝕋} {l : Level} → UU-Trunc k l → UU l
type-UU-Trunc A = pr1 A

is-trunc-type-UU-Trunc :
  {k : 𝕋} {l : Level} (A : UU-Trunc k l) → is-trunc k (type-UU-Trunc A)
is-trunc-type-UU-Trunc A = pr2 A

is-trunc-UU-Trunc :
  (k : 𝕋) (l : Level) → is-trunc (succ-𝕋 k) (UU-Trunc k l)
is-trunc-UU-Trunc k l X Y =
  is-trunc-is-equiv k
    ( Id (pr1 X) (pr1 Y))
    ( ap pr1)
    ( is-emb-pr1
      ( is-prop-is-trunc k) X Y)
    ( is-trunc-is-equiv k
      ( (pr1 X) ≃ (pr1 Y))
      ( equiv-eq)
      ( univalence (pr1 X) (pr1 Y))
      ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))

is-set-UU-Prop : (l : Level) → is-set (UU-Prop l)
is-set-UU-Prop l = is-trunc-UU-Trunc (neg-one-𝕋) l

UU-Prop-Set : (l : Level) → UU-Set (lsuc l)
UU-Prop-Set l = pair (UU-Prop l) (is-set-UU-Prop l)

is-contr-total-iff :
  {l1 : Level} (P : UU-Prop l1) → is-contr (Σ (UU-Prop l1) (λ Q → P ⇔ Q))
is-contr-total-iff {l1} P =
  is-contr-equiv
    ( Σ (UU-Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
    ( equiv-tot (equiv-equiv-iff P))
    ( is-contr-total-Eq-substructure
      ( is-contr-total-equiv (type-Prop P))
      ( is-prop-is-prop)
      ( type-Prop P)
      ( equiv-id)
      ( is-prop-type-Prop P))

iff-eq :
  {l1 : Level} {P Q : UU-Prop l1} → Id P Q → P ⇔ Q
iff-eq refl = pair id id

is-equiv-iff-eq :
  {l1 : Level} (P Q : UU-Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
is-equiv-iff-eq P =
  fundamental-theorem-id P
    ( pair id id)
    ( is-contr-total-iff P)
    ( λ Q → iff-eq {P = P} {Q})

eq-iff' :
  {l1 : Level} (P Q : UU-Prop l1) → P ⇔ Q → Id P Q
eq-iff' P Q = map-inv-is-equiv (is-equiv-iff-eq P Q)

eq-iff :
  {l1 : Level} {P Q : UU-Prop l1} →
  (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → Id P Q
eq-iff {l1} {P} {Q} f g = eq-iff' P Q (pair f g)

eq-equiv-Prop :
  {l1 : Level} {P Q : UU-Prop l1} → (type-Prop P ≃ type-Prop Q) → Id P Q
eq-equiv-Prop e =
  eq-iff (map-equiv e) (map-inv-equiv e)

precomp-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU-Set l3) →
  (B → type-Set C) → (A → type-Set C)
precomp-Set f C = precomp f (type-Set C)

square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → Id (g y) (h y)) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl

is-emb-precomp-Set-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → (C : UU-Set l3) → is-emb (precomp-Set f C)
is-emb-precomp-Set-is-surjective H C =
  is-emb-is-injective
    ( is-set-function-type (is-set-type-Set C))
    ( λ {g} {h} p →
      eq-htpy (λ b →
         apply-universal-property-trunc-Prop
           ( H b)
           ( Id-Prop C (g b) (h b))
           ( λ u →
             ( inv (ap g (pr2 u))) ∙
             ( ( htpy-eq p (pr1 u))  ∙
               ( ap h (pr2 u))))))

is-emb-precomp-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → (C : UU-Set l3) → is-emb (precomp f (type-Set C))
is-emb-precomp-is-surjective {f = f} is-surj-f C g h =
  is-equiv-top-is-equiv-bottom-square
    ( htpy-eq)
    ( htpy-eq)
    ( ap (precomp f (type-Set C)))
    ( λ p a → p (f a))
    ( square-htpy-eq f g h)
    ( funext g h)
    ( funext (g ∘ f) (h ∘ f))
    ( dependent-universal-property-surj-is-surjective f is-surj-f
      ( λ a → Id-Prop C (g a) (h a)))

component-UU-Level :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
component-UU-Level l1 A = Σ (UU l1) (mere-equiv A)

type-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} → component-UU-Level l1 A → UU l1
type-component-UU-Level X = pr1 X

mere-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  mere-equiv A (type-component-UU-Level X)
mere-equiv-component-UU-Level X = pr2 X

component-UU :
  {l1 : Level} (A : UU l1) → UU (lsuc l1)
component-UU {l1} A = component-UU-Level l1 A

type-component-UU : {l1 : Level} {A : UU l1} (X : component-UU A) → UU l1
type-component-UU X = type-component-UU-Level X

mere-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) →
  mere-equiv A (type-component-UU X)
mere-equiv-component-UU X = mere-equiv-component-UU-Level X

equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) → UU l1
equiv-component-UU-Level X Y =
  type-component-UU-Level X ≃ type-component-UU-Level Y

id-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  equiv-component-UU-Level X X
id-equiv-component-UU-Level X = equiv-id

equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} {X Y : component-UU-Level l1 A} →
  Id X Y → equiv-component-UU-Level X Y
equiv-eq-component-UU-Level {X = X} refl =
  id-equiv-component-UU-Level X

is-contr-total-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  is-contr (Σ (component-UU-Level l1 A) (equiv-component-UU-Level X))
is-contr-total-equiv-component-UU-Level X =
  is-contr-total-Eq-substructure
    ( is-contr-total-equiv (type-component-UU-Level X))
    ( λ Y → is-prop-mere-equiv _ Y)
    ( type-component-UU-Level X)
    ( equiv-id)
    ( mere-equiv-component-UU-Level X)

is-equiv-equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  is-equiv (equiv-eq-component-UU-Level {X = X} {Y})
is-equiv-equiv-eq-component-UU-Level X =
  fundamental-theorem-id X
    ( id-equiv-component-UU-Level X)
    ( is-contr-total-equiv-component-UU-Level X)
    ( λ Y → equiv-eq-component-UU-Level {X = X} {Y})

eq-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  equiv-component-UU-Level X Y → Id X Y
eq-equiv-component-UU-Level X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-component-UU-Level X Y)

equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) → UU l1
equiv-component-UU X Y = equiv-component-UU-Level X Y

id-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) → equiv-component-UU X X
id-equiv-component-UU X = id-equiv-component-UU-Level X

equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} {X Y : component-UU A} →
  Id X Y → equiv-component-UU X Y
equiv-eq-component-UU p = equiv-eq-component-UU-Level p

is-contr-total-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) →
  is-contr (Σ (component-UU A) (equiv-component-UU X))
is-contr-total-equiv-component-UU X =
  is-contr-total-equiv-component-UU-Level X

is-equiv-equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  is-equiv (equiv-eq-component-UU {X = X} {Y})
is-equiv-equiv-eq-component-UU X Y =
  is-equiv-equiv-eq-component-UU-Level X Y

eq-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  equiv-component-UU X Y → Id X Y
eq-equiv-component-UU X Y =
  eq-equiv-component-UU-Level X Y

equiv-UU-Fin-Level : {l : Level} {k : ℕ} → (X Y : UU-Fin-Level l k) → UU l
equiv-UU-Fin-Level X Y = equiv-component-UU-Level X Y

equiv-UU-Fin : {k : ℕ} (X Y : UU-Fin k) → UU lzero
equiv-UU-Fin X Y = equiv-component-UU X Y

id-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → equiv-UU-Fin-Level X X
id-equiv-UU-Fin-Level X = id-equiv-component-UU-Level X

id-equiv-UU-Fin :
  {k : ℕ} (X : UU-Fin k) → equiv-UU-Fin X X
id-equiv-UU-Fin X = id-equiv-component-UU X

equiv-eq-UU-Fin-Level :
  {l : Level} {k : ℕ} {X Y : UU-Fin-Level l k} → Id X Y → equiv-UU-Fin-Level X Y
equiv-eq-UU-Fin-Level p = equiv-eq-component-UU-Level p

equiv-eq-UU-Fin :
  {k : ℕ} {X Y : UU-Fin k} → Id X Y → equiv-UU-Fin X Y
equiv-eq-UU-Fin p = equiv-eq-component-UU p

is-contr-total-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) →
  is-contr (Σ (UU-Fin-Level l k) (equiv-UU-Fin-Level X))
is-contr-total-equiv-UU-Fin-Level {l} {k} X =
  is-contr-total-equiv-component-UU-Level X

is-contr-total-equiv-UU-Fin :
  {k : ℕ} (X : UU-Fin k) → is-contr (Σ (UU-Fin k) (equiv-UU-Fin X))
is-contr-total-equiv-UU-Fin X =
  is-contr-total-equiv-component-UU X

is-equiv-equiv-eq-UU-Fin-Level :
  {l : Level} {k : ℕ} (X Y : UU-Fin-Level l k) →
  is-equiv (equiv-eq-UU-Fin-Level {X = X} {Y})
is-equiv-equiv-eq-UU-Fin-Level X =
  is-equiv-equiv-eq-component-UU-Level X

is-equiv-equiv-eq-UU-Fin :
  {k : ℕ} (X Y : UU-Fin k) → is-equiv (equiv-eq-UU-Fin {X = X} {Y})
is-equiv-equiv-eq-UU-Fin X =
  is-equiv-equiv-eq-component-UU X

eq-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X Y : UU-Fin-Level l k) →
  equiv-UU-Fin-Level X Y → Id X Y
eq-equiv-UU-Fin-Level X Y =
  eq-equiv-component-UU-Level X Y

eq-equiv-UU-Fin :
  {k : ℕ} (X Y : UU-Fin k) → equiv-UU-Fin X Y → Id X Y
eq-equiv-UU-Fin X Y = eq-equiv-component-UU X Y

equiv-equiv-eq-UU-Fin-Level :
  {l : Level} {k : ℕ} (X Y : UU-Fin-Level l k) →
  Id X Y ≃ equiv-UU-Fin-Level X Y
equiv-equiv-eq-UU-Fin-Level X Y =
  pair equiv-eq-UU-Fin-Level (is-equiv-equiv-eq-UU-Fin-Level X Y)

equiv-equiv-eq-UU-Fin :
  {k : ℕ} (X Y : UU-Fin k) → Id X Y ≃ equiv-UU-Fin X Y
equiv-equiv-eq-UU-Fin X Y =
  pair equiv-eq-UU-Fin (is-equiv-equiv-eq-UU-Fin X Y)

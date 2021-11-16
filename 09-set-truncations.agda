{-# OPTIONS --without-K --exact-split #-}

module 09-set-truncations where

open import 08-univalence public

is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

type-is-small :
  {l l1 : Level} {A : UU l1} → is-small l A → UU l
type-is-small = pr1

equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A ≃ type-is-small H
equiv-is-small = pr2

map-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A → type-is-small H
map-equiv-is-small H = map-equiv (equiv-is-small H)

map-inv-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → type-is-small H → A
map-inv-equiv-is-small H = map-inv-equiv (equiv-is-small H)

is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (Id x y)

is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A =
  is-prop-is-proof-irrelevant
    ( λ Xe →
      is-contr-equiv'
        ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
        ( equiv-tot ((λ Y → equiv-precomp-equiv (pr2 Xe) Y)))
        ( is-contr-total-equiv (pr1 Xe)))

is-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU-Prop (lsuc l ⊔ l1)
is-small-Prop l A = pair (is-small l A) (is-prop-is-small l A)

Rel-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Rel-Prop l A = A → (A → UU-Prop l)

type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → A → A → UU l2
type-Rel-Prop R x y = pr1 (R x y)

is-prop-type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  (x y : A) → is-prop (type-Rel-Prop R x y)
is-prop-type-Rel-Prop R x y = pr2 (R x y)

is-reflexive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-reflexive-Rel-Prop {A = A} R =
  {x : A} → type-Rel-Prop R x x

is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-symmetric-Rel-Prop {A = A} R =
  {x y : A} → type-Rel-Prop R x y → type-Rel-Prop R y x

is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-transitive-Rel-Prop {A = A} R =
  {x y z : A} → type-Rel-Prop R x y → type-Rel-Prop R y z → type-Rel-Prop R x z

is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive-Rel-Prop R ×
    ( is-symmetric-Rel-Prop R × is-transitive-Rel-Prop R)

Eq-Rel :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Eq-Rel l A = Σ (Rel-Prop l A) is-equivalence-relation

prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → Rel-Prop l2 A
prop-Eq-Rel = pr1

type-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → A → A → UU l2
type-Eq-Rel R = type-Rel-Prop (prop-Eq-Rel R)

is-prop-type-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x y : A) →
  is-prop (type-Eq-Rel R x y)
is-prop-type-Eq-Rel R = is-prop-type-Rel-Prop (prop-Eq-Rel R)

is-equivalence-relation-prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-equivalence-relation (prop-Eq-Rel R)
is-equivalence-relation-prop-Eq-Rel R = pr2 R

refl-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-reflexive-Rel-Prop (prop-Eq-Rel R)
refl-Eq-Rel R = pr1 (is-equivalence-relation-prop-Eq-Rel R)

symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-symmetric-Rel-Prop (prop-Eq-Rel R)
symm-Eq-Rel R = pr1 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

equiv-symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x y : A) →
  type-Eq-Rel R x y ≃ type-Eq-Rel R y x
equiv-symm-Eq-Rel R x y =
  equiv-prop
    ( is-prop-type-Eq-Rel R x y)
    ( is-prop-type-Eq-Rel R y x)
    ( symm-Eq-Rel R)
    ( symm-Eq-Rel R)

trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-transitive-Rel-Prop (prop-Eq-Rel R)
trans-Eq-Rel R = pr2 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) → A → UU l2
class-Eq-Rel = type-Eq-Rel

is-equivalence-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  (A → UU-Prop l2) → UU (l1 ⊔ lsuc l2)
is-equivalence-class-Eq-Rel {A = A} R P =
  ∃ (λ x → Id (type-Prop ∘ P) (class-Eq-Rel R x))

set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → UU (l1 ⊔ lsuc l2)
set-quotient R = im (prop-Eq-Rel R)

map-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  A → set-quotient R
map-set-quotient R = map-unit-im (prop-Eq-Rel R)

class-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  set-quotient R → (A → UU-Prop l2)
class-set-quotient R P = pr1 P

type-class-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  set-quotient R → (A → UU l2)
type-class-set-quotient R P x = type-Prop (class-set-quotient R P x)

is-prop-type-class-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  (x : set-quotient R) (a : A) → is-prop (type-class-set-quotient R x a)
is-prop-type-class-set-quotient R P x =
  is-prop-type-Prop (class-set-quotient R P x)

is-set-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → is-set (set-quotient R)
is-set-set-quotient {l1} {l2} R =
  is-set-im (prop-Eq-Rel R) (is-set-function-type (is-set-UU-Prop l2))

quotient-Set :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → UU-Set (l1 ⊔ lsuc l2)
quotient-Set R = pair (set-quotient R) (is-set-set-quotient R)

center-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) →
  Σ (set-quotient R) (λ P → type-class-set-quotient R P x)
center-total-class-Eq-Rel R x =
  pair
    ( map-set-quotient R x)
    ( refl-Eq-Rel R)

contraction-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A) →
  ( t : Σ (set-quotient R) (λ P → type-class-set-quotient R P a)) →
  Id (center-total-class-Eq-Rel R a) t
contraction-total-class-Eq-Rel {l1} {l2} {A} R a (pair (pair P p) H) =
  eq-subtype
    ( λ Q → is-prop-type-class-set-quotient R Q a)
    ( apply-universal-property-trunc-Prop
      ( p)
      ( Id-Prop (quotient-Set R) (map-set-quotient R a) (pair P p))
      ( α))
  where
  α : fib (pr1 R) P → Id (map-set-quotient R a) (pair P p)
  α (pair x refl) =
    eq-subtype
      ( λ z → is-prop-type-trunc-Prop)
      ( eq-htpy
        ( λ y →
          eq-iff
            ( trans-Eq-Rel R H)
            ( trans-Eq-Rel R (symm-Eq-Rel R H))))

is-contr-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A) →
  is-contr
    ( Σ (set-quotient R) (λ P → type-class-set-quotient R P a))
is-contr-total-class-Eq-Rel R a =
  pair
    ( center-total-class-Eq-Rel R a)
    ( contraction-total-class-Eq-Rel R a)

related-eq-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) → Id (map-set-quotient R a) q →
  type-class-set-quotient R q a
related-eq-quotient R a .(map-set-quotient R a) refl = refl-Eq-Rel R

is-equiv-related-eq-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) → is-equiv (related-eq-quotient R a q)
is-equiv-related-eq-quotient R a =
  fundamental-theorem-id
    ( map-set-quotient R a)
    ( refl-Eq-Rel R)
    ( is-contr-total-class-Eq-Rel R a)
    ( related-eq-quotient R a)

effective-quotient' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) →
  Id (map-set-quotient R a) q ≃ type-class-set-quotient R q a
effective-quotient' R a q =
  pair (related-eq-quotient R a q) (is-equiv-related-eq-quotient R a q)

eq-effective-quotient' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) → type-class-set-quotient R q a →
  Id (map-set-quotient R a) q
eq-effective-quotient' R a q =
  map-inv-is-equiv (is-equiv-related-eq-quotient R a q)

is-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-effective {A = A} R f =
  (x y : A) → (Id (f x) (f y) ≃ type-Eq-Rel R x y)

is-effective-map-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-effective R (map-set-quotient R)
is-effective-map-set-quotient R x y =
  ( equiv-symm-Eq-Rel R y x) ∘e
  ( effective-quotient' R x (map-set-quotient R y))

apply-effectiveness-map-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y : A} →
  Id (map-set-quotient R x) (map-set-quotient R y) → type-Eq-Rel R x y
apply-effectiveness-map-set-quotient R {x} {y} =
  map-equiv (is-effective-map-set-quotient R x y)

apply-effectiveness-map-set-quotient' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y : A} →
  type-Eq-Rel R x y → Id (map-set-quotient R x) (map-set-quotient R y)
apply-effectiveness-map-set-quotient' R {x} {y} =
  map-inv-equiv (is-effective-map-set-quotient R x y)

reflects-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
reflects-Eq-Rel {A = A} R f =
  {x y : A} → type-Eq-Rel R x y → Id (f x) (f y)

reflecting-map-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
reflecting-map-Eq-Rel {A = A} R B =
  Σ (A → B) (reflects-Eq-Rel R)

is-prop-reflects-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) → is-prop (reflects-Eq-Rel R f)
is-prop-reflects-Eq-Rel R B f =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-function-type (is-set-type-Set B (f x) (f y))))

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) → UU _
  htpy-reflecting-map-Eq-Rel g =
    pr1 f ~ pr1 g
  
  refl-htpy-reflecting-map-Eq-Rel :
    htpy-reflecting-map-Eq-Rel f
  refl-htpy-reflecting-map-Eq-Rel = refl-htpy
  
  htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    Id f g → htpy-reflecting-map-Eq-Rel g
  htpy-eq-reflecting-map-Eq-Rel .f refl =
    refl-htpy-reflecting-map-Eq-Rel
  
  is-contr-total-htpy-reflecting-map-Eq-Rel :
    is-contr
      ( Σ (reflecting-map-Eq-Rel R (type-Set B)) htpy-reflecting-map-Eq-Rel)
  is-contr-total-htpy-reflecting-map-Eq-Rel =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy (pr1 f))
      ( is-prop-reflects-Eq-Rel R B)
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    is-equiv (htpy-eq-reflecting-map-Eq-Rel g)
  is-equiv-htpy-eq-reflecting-map-Eq-Rel =
    fundamental-theorem-id f
      refl-htpy-reflecting-map-Eq-Rel
      is-contr-total-htpy-reflecting-map-Eq-Rel
      htpy-eq-reflecting-map-Eq-Rel

  eq-htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    htpy-reflecting-map-Eq-Rel g → Id f g
  eq-htpy-reflecting-map-Eq-Rel g =
    map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-Eq-Rel g)

  equiv-htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    Id f g ≃ htpy-reflecting-map-Eq-Rel g
  equiv-htpy-eq-reflecting-map-Eq-Rel g =
    pair
      ( htpy-eq-reflecting-map-Eq-Rel g)
      ( is-equiv-htpy-eq-reflecting-map-Eq-Rel g)

precomp-Set-Quotient :
  {l l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) →
  (X : UU-Set l) → (type-hom-Set B X) → reflecting-map-Eq-Rel R (type-Set X)
precomp-Set-Quotient R B f X g =
  pair (g ∘ (pr1 f)) (λ r → ap g (pr2 f r))

precomp-id-Set-Quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  Id (precomp-Set-Quotient R B f B id) f
precomp-id-Set-Quotient R B f =
  eq-htpy-reflecting-map-Eq-Rel R B
    ( precomp-Set-Quotient R B f B id)
    ( f)
    ( refl-htpy)

precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : type-hom-Set B C)
  (D : UU-Set l5) (h : type-hom-Set C D) →
  Id ( precomp-Set-Quotient R B f D (h ∘ g))
     ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-Eq-Rel R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

is-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) → UU _
is-set-quotient l R B f =
  (X : UU-Set l) →
  is-equiv (precomp-Set-Quotient R B f X)

universal-property-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  ({l : Level} → is-set-quotient l R B f) → {l : Level}
  (X : UU-Set l) (g : reflecting-map-Eq-Rel R (type-Set X)) →
  is-contr (Σ (type-hom-Set B X) (λ h → (h ∘ pr1 f) ~ pr1 g))
universal-property-set-quotient R B f Q X g =
   is-contr-equiv'
     ( fib (precomp-Set-Quotient R B f X) g)
     ( equiv-tot
       ( λ h →
         equiv-htpy-eq-reflecting-map-Eq-Rel R X
           ( precomp-Set-Quotient R B f X h)
           ( g)))
     ( is-contr-map-is-equiv (Q X) g)

map-universal-property-set-quotient :
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  (Uf : {l : Level} → is-set-quotient l R B f) (C : UU-Set l4)
  (g : reflecting-map-Eq-Rel R (type-Set C)) →
  type-Set B → type-Set C
map-universal-property-set-quotient R B f Uf C g =
  pr1 (center (universal-property-set-quotient R B f Uf C g))

triangle-universal-property-set-quotient :
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  (Uf : {l : Level} → is-set-quotient l R B f) (C : UU-Set l4)
  (g : reflecting-map-Eq-Rel R (type-Set C)) →
  (map-universal-property-set-quotient R B f Uf C g ∘ pr1 f) ~ pr1 g
triangle-universal-property-set-quotient R B f Uf C g =
  ( pr2 (center (universal-property-set-quotient R B f Uf C g)))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  {h : type-Set B → type-Set C} (H : (h ∘ pr1 f) ~ pr1 g)
  where

  is-equiv-is-set-quotient-is-set-quotient :
    ({l : Level} → is-set-quotient l R B f) →
    ({l : Level} → is-set-quotient l R C g) →
    is-equiv h
  is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    is-equiv-has-inverse
      ( pr1 (center K))
      ( htpy-eq
        ( is-injective-is-equiv
          ( Ug C)
          { h ∘ k}
          { id}
          ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
            ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
              ( ( eq-htpy-reflecting-map-Eq-Rel R C
                  ( precomp-Set-Quotient R B f C h) g H) ∙
                ( inv (precomp-id-Set-Quotient R C g)))))))
      ( htpy-eq
        ( is-injective-is-equiv
          ( Uf B)
          { k ∘ h}
          { id}
          ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
            ( ( ap
                ( λ t → precomp-Set-Quotient R C t B k)
                ( eq-htpy-reflecting-map-Eq-Rel R C
                  ( precomp-Set-Quotient R B f C h) g H)) ∙
              ( ( α) ∙
                ( inv (precomp-id-Set-Quotient R B f)))))))
    where
    K = universal-property-set-quotient R C g Ug B f
    k : type-Set C → type-Set B
    k = pr1 (center K)
    α : Id (precomp-Set-Quotient R C g B k) f
    α = eq-htpy-reflecting-map-Eq-Rel R B
          ( precomp-Set-Quotient R C g B k)
          ( f)
          ( pr2 (center K))

  is-set-quotient-is-set-quotient-is-equiv :
    is-equiv h → ({l : Level} → is-set-quotient l R B f) →
    {l : Level} → is-set-quotient l R C g
  is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
    is-equiv-comp
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-Eq-Rel R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( is-equiv-precomp-is-equiv h E (type-Set X))
      ( Uf X)

  is-set-quotient-is-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R C g) → is-equiv h →
    {l : Level} → is-set-quotient l R B f
  is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
    is-equiv-left-factor
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-Eq-Rel R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( Ug X)
      ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) 
  (Uf : {l : Level} → is-set-quotient l R B f)
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  (Ug : {l : Level} → is-set-quotient l R C g)
  where
  
  uniqueness-set-quotient :
    is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ pr1 f) ~ pr1 g))
  uniqueness-set-quotient =
    is-contr-total-Eq-substructure
      ( universal-property-set-quotient R B f Uf C g)
      ( is-subtype-is-equiv)
      ( map-universal-property-set-quotient R B f Uf C g)
      ( triangle-universal-property-set-quotient R B f Uf C g)
      ( is-equiv-is-set-quotient-is-set-quotient R B f C g
        ( triangle-universal-property-set-quotient R B f Uf C g)
        ( Uf)
        ( Ug))

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient =
    pr1 (center uniqueness-set-quotient)

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient =  map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘ pr1 f) ~ pr1 g
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)

is-surjective-and-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-surjective-and-effective {A = A} R f =
  is-surjective f × is-effective R f

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (q : A → type-Set B)
  where

  is-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) →
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → is-image l (prop-Eq-Rel R) i (pair q T)) →
    is-effective R q
  is-effective-is-image i T H x y =
    ( is-effective-map-set-quotient R x y) ∘e
    ( ( inv-equiv (equiv-ap-emb (emb-im (prop-Eq-Rel R)))) ∘e
      ( ( inv-equiv (convert-eq-values-htpy T x y)) ∘e
        ( equiv-ap-emb i)))

  is-surjective-and-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) → 
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → is-image l (prop-Eq-Rel R) i (pair q T)) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-image i T H =
    pair
      ( is-surjective-is-image (prop-Eq-Rel R) i (pair q T) H)
      ( is-effective-is-image i T H)

  is-locally-small-is-surjective-and-effective :
    is-surjective-and-effective R q → is-locally-small l2 (type-Set B)
  is-locally-small-is-surjective-and-effective e x y =
    apply-universal-property-trunc-Prop
      ( pr1 e x)
      ( is-small-Prop l2 (Id x y))
      ( λ u →
        apply-universal-property-trunc-Prop
          ( pr1 e y)
          ( is-small-Prop l2 (Id x y))
          ( α u))
    where
    α : fib q x → fib q y → is-small l2 (Id x y)
    α (pair a refl) (pair b refl) =
      pair (type-Eq-Rel R a b) (pr2 e a b)

  large-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → UU-Prop l3
  large-map-emb-is-surjective-and-effective H b a = Id-Prop B b (q a)

  small-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A →
    Σ (UU-Prop l3) (λ P → is-small l2 (type-Prop P))
  small-map-emb-is-surjective-and-effective H b a =
    pair ( large-map-emb-is-surjective-and-effective H b a)
         ( is-locally-small-is-surjective-and-effective H b (q a))

  map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → UU-Prop l2
  map-emb-is-surjective-and-effective H b a =
    pair ( pr1 (pr2 (small-map-emb-is-surjective-and-effective H b a)))
         ( is-prop-equiv'
           ( type-Prop (large-map-emb-is-surjective-and-effective H b a))
           ( pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a)))
           ( is-prop-type-Prop
             ( large-map-emb-is-surjective-and-effective H b a)))
  
  compute-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) (b : type-Set B) (a : A) →
    type-Prop (large-map-emb-is-surjective-and-effective H b a) ≃
    type-Prop (map-emb-is-surjective-and-effective H b a) 
  compute-map-emb-is-surjective-and-effective H b a =
    pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a))
  
  triangle-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    prop-Eq-Rel R ~ (map-emb-is-surjective-and-effective H ∘ q)
  triangle-emb-is-surjective-and-effective H a =
    eq-htpy
      ( λ x →
        eq-equiv-Prop
          ( ( compute-map-emb-is-surjective-and-effective H (q a) x) ∘e
            ( inv-equiv (pr2 H a x))))
  
  is-emb-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    is-emb (map-emb-is-surjective-and-effective H)
  is-emb-map-emb-is-surjective-and-effective H =
    is-emb-is-injective
      ( is-set-function-type (is-set-UU-Prop l2))
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 H y)
          ( Id-Prop B x y)
          ( α p))
    where
    α : {x y : type-Set B}
        (p : Id ( map-emb-is-surjective-and-effective H x)
                ( map-emb-is-surjective-and-effective H y)) →
        fib q y → type-Prop (Id-Prop B x y)
    α {x} p (pair a refl) =
      map-inv-equiv
        ( ( inv-equiv
            ( pr2
              ( is-locally-small-is-surjective-and-effective
                H (q a) (q a)))) ∘e
          ( ( equiv-eq (ap pr1 (htpy-eq p a))) ∘e
            ( pr2
              ( is-locally-small-is-surjective-and-effective H x (q a)))))
        ( refl)

  emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    type-Set B ↪ (A → UU-Prop l2)
  emb-is-surjective-and-effective H =
    pair ( map-emb-is-surjective-and-effective H)
         ( is-emb-map-emb-is-surjective-and-effective H)

  is-emb-large-map-emb-is-surjective-and-effective :
    (e : is-surjective-and-effective R q) →
    is-emb (large-map-emb-is-surjective-and-effective e)
  is-emb-large-map-emb-is-surjective-and-effective e =
    is-emb-is-injective
      ( is-set-function-type (is-set-UU-Prop l3))
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 e y)
          ( Id-Prop B x y)
          ( α p))
    where
    α : {x y : type-Set B}
        (p : Id ( large-map-emb-is-surjective-and-effective e x)
                ( large-map-emb-is-surjective-and-effective e y)) →
        fib q y → type-Prop (Id-Prop B x y)
    α p (pair a refl) = map-inv-equiv (equiv-eq (ap pr1 (htpy-eq p a))) refl
  
  large-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B ↪ (A → UU-Prop l3)
  large-emb-is-surjective-and-effective e =
    pair ( large-map-emb-is-surjective-and-effective e)
         ( is-emb-large-map-emb-is-surjective-and-effective e)

  is-image-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    ( {l : Level} →
      is-image l
        ( prop-Eq-Rel R)
        ( emb-is-surjective-and-effective H)
        ( pair q (triangle-emb-is-surjective-and-effective H)))
  is-image-is-surjective-and-effective H =
    is-image-is-surjective
      ( prop-Eq-Rel R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
      ( pr1 H)

  is-surjective-is-set-quotient :
    (H : reflects-Eq-Rel R q) →
    ({l : Level} → is-set-quotient l R B (pair q H)) →
    is-surjective q
  is-surjective-is-set-quotient H Q b =
    tr ( λ y → type-trunc-Prop (fib q y))
       ( htpy-eq
         ( ap pr1
           ( eq-is-contr
             ( universal-property-set-quotient R B (pair q H) Q B (pair q H))
             { pair (inclusion-im q ∘ β) δ}
             { pair id refl-htpy}))
         ( b))
       ( pr2 (β b))
    where
    α : reflects-Eq-Rel R (map-unit-im q)
    α {x} {y} r =
      is-injective-is-emb
        ( is-emb-inclusion-im q)
        ( map-equiv (convert-eq-values-htpy (triangle-unit-im q) x y) (H r))
    β : type-Set B → im q
    β = map-inv-is-equiv
          ( Q ( pair (im q) (is-set-im q (is-set-type-Set B))))
          ( pair (map-unit-im q) α)
    γ : (β ∘ q) ~ map-unit-im q
    γ = htpy-eq
          ( ap pr1
            ( issec-map-inv-is-equiv
              ( Q (pair (im q) (is-set-im q (is-set-type-Set B))))
              ( pair (map-unit-im q) α)))
    δ : ((inclusion-im q ∘ β) ∘ q) ~ q
    δ = (inclusion-im q ·l γ) ∙h (triangle-unit-im q)

  is-effective-is-set-quotient :
    (H : reflects-Eq-Rel R q) →
    ({l : Level} → is-set-quotient l R B (pair q H)) →
    is-effective R q
  is-effective-is-set-quotient H Q x y =
    inv-equiv (compute-P y) ∘e δ (q y)
    where
    α : Σ (A → UU-Prop l2) (reflects-Eq-Rel R)
    α = pair
          ( prop-Eq-Rel R x)
          ( λ r →
            eq-iff
              ( λ s → trans-Eq-Rel R s r)
              ( λ s → trans-Eq-Rel R s (symm-Eq-Rel R r)))
    P : type-Set B → UU-Prop l2
    P = map-inv-is-equiv (Q (UU-Prop-Set l2)) α
    compute-P : (a : A) → type-Eq-Rel R x a ≃ type-Prop (P (q a))
    compute-P a =
      equiv-eq
        ( ap pr1
          ( htpy-eq
            ( ap pr1
              ( inv (issec-map-inv-is-equiv (Q (UU-Prop-Set l2)) α)))
            ( a)))
    point-P : type-Prop (P (q x))
    point-P = map-equiv (compute-P x) (refl-Eq-Rel R)
    center-total-P : Σ (type-Set B) (λ b → type-Prop (P b))
    center-total-P = pair (q x) point-P
    contraction-total-P :
      (u : Σ (type-Set B) (λ b → type-Prop (P b))) → Id center-total-P u
    contraction-total-P (pair b p) =
      eq-subtype
        ( λ z → is-prop-type-Prop (P z))
        ( apply-universal-property-trunc-Prop
          ( is-surjective-is-set-quotient H Q b)
          ( Id-Prop B (q x) b)
          ( λ v →
            ( H ( map-inv-equiv
                  ( compute-P (pr1 v))
                  ( inv-tr (λ b → type-Prop (P b)) (pr2 v) p))) ∙
            ( pr2 v)))
    is-contr-total-P : is-contr (Σ (type-Set B) (λ b → type-Prop (P b)))
    is-contr-total-P = pair center-total-P contraction-total-P
    β : (b : type-Set B) → Id (q x) b → type-Prop (P b)
    β .(q x) refl = point-P
    γ : (b : type-Set B) → is-equiv (β b)
    γ = fundamental-theorem-id (q x) point-P is-contr-total-P β
    δ : (b : type-Set B) → Id (q x) b ≃ type-Prop (P b)
    δ b = pair (β b) (γ b)

  is-surjective-and-effective-is-set-quotient :
    (H : reflects-Eq-Rel R q) →
    ({l : Level} → is-set-quotient l R B (pair q H)) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-set-quotient H Q =
    pair (is-surjective-is-set-quotient H Q) (is-effective-is-set-quotient H Q)

  reflects-Eq-Rel-is-surjective-and-effective :
    is-surjective-and-effective R q → reflects-Eq-Rel R q
  reflects-Eq-Rel-is-surjective-and-effective E {x} {y} =
    map-inv-equiv (pr2 E x y)

  universal-property-set-quotient-is-surjective-and-effective :
    {l : Level} (E : is-surjective-and-effective R q) (X : UU-Set l) →
    is-contr-map
      ( precomp-Set-Quotient R B
        ( pair q (reflects-Eq-Rel-is-surjective-and-effective E))
        ( X))
  universal-property-set-quotient-is-surjective-and-effective
    {l} E X (pair f H) =
    is-proof-irrelevant-is-prop
      ( is-prop-equiv
        ( fib (precomp q (type-Set X)) f)
        ( equiv-tot
          ( λ h → equiv-ap-pr1 (is-prop-reflects-Eq-Rel R X)))
        ( is-prop-map-is-emb (is-emb-precomp-is-surjective (pr1 E) X) f))
      ( pair
        ( λ b → pr1 (α b))
        ( eq-subtype
          ( is-prop-reflects-Eq-Rel R X)
          ( eq-htpy (λ a → ap pr1 (β a)))))
    where
    P-Prop : (b : type-Set B) (x : type-Set X) → UU-Prop (l1 ⊔ l3 ⊔ l)
    P-Prop b x = ∃-Prop (λ a → (Id (f a) x) × (Id (q a) b))
    P : (b : type-Set B) (x : type-Set X) → UU (l1 ⊔ l3 ⊔ l)
    P b x = type-Prop (P-Prop b x)
    Q' : (b : type-Set B) → all-elements-equal (Σ (type-Set X) (P b))
    Q' b x y =
      eq-subtype
        ( λ x → is-prop-type-Prop (P-Prop b x))
        ( apply-universal-property-trunc-Prop
          ( pr2 x)
          ( Id-Prop X (pr1 x) (pr1 y))
          ( λ u →
            apply-universal-property-trunc-Prop
              ( pr2 y)
              ( Id-Prop X (pr1 x) (pr1 y))
              ( λ v →
                ( inv (pr1 (pr2 u))) ∙
                ( ( H ( map-equiv
                        ( pr2 E (pr1 u) (pr1 v))
                        ( (pr2 (pr2 u)) ∙ (inv (pr2 (pr2 v)))))) ∙
                  ( pr1 (pr2 v))))))
    Q : (b : type-Set B) → is-prop (Σ (type-Set X) (P b))
    Q b = is-prop-all-elements-equal (Q' b)
    α : (b : type-Set B) → Σ (type-Set X) (P b)
    α =
      map-inv-is-equiv
        ( dependent-universal-property-surj-is-surjective q
          ( pr1 E)
          ( λ b → pair (Σ (type-Set X) (P b)) (Q b)))
        ( λ a → pair (f a) (unit-trunc-Prop (pair a (pair refl refl))))
    β : (a : A) →
        Id (α (q a)) (pair (f a) (unit-trunc-Prop (pair a (pair refl refl))))
    β = htpy-eq
          ( issec-map-inv-is-equiv
            ( dependent-universal-property-surj-is-surjective q
              ( pr1 E)
              ( λ b → pair (Σ (type-Set X) (P b)) (Q b)))
            ( λ a → pair (f a) (unit-trunc-Prop (pair a (pair refl refl)))))

  is-set-quotient-is-surjective-and-effective :
    {l : Level} (E : is-surjective-and-effective R q) →
    is-set-quotient l R B
      ( pair q (reflects-Eq-Rel-is-surjective-and-effective E))
  is-set-quotient-is-surjective-and-effective E X =
    is-equiv-is-contr-map
      ( universal-property-set-quotient-is-surjective-and-effective E X)

is-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  ( A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-set-truncation l B f =
  (C : UU-Set l) → is-equiv (precomp-Set f C)

universal-property-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (B : UU-Set l2) (f : A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-set-truncation l {A = A} B f =
  (C : UU-Set l) (g : A → type-Set C) →
  is-contr (Σ (type-hom-Set B C) (λ h → (h ∘ f) ~  g))

is-set-truncation-universal-property :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (B : UU-Set l2) (f : A → type-Set B) →
  universal-property-set-truncation l B f →
  is-set-truncation l B f
is-set-truncation-universal-property l B f up-f C =
  is-equiv-is-contr-map
    ( λ g → is-contr-equiv
      ( Σ (type-hom-Set B C) (λ h → (h ∘ f) ~ g))
      ( equiv-tot (λ h → equiv-funext))
      ( up-f C g))

universal-property-is-set-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-set-truncation l B f → universal-property-set-truncation l B f
universal-property-is-set-truncation l B f is-settr-f C g =
  is-contr-equiv'
    ( Σ (type-hom-Set B C) (λ h → Id (h ∘ f) g))
    ( equiv-tot (λ h → equiv-funext))
    ( is-contr-map-is-equiv (is-settr-f C) g)

map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) → type-hom-Set B C
map-is-set-truncation B f is-settr-f C g =
  pr1
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

triangle-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  (is-settr-f : {l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) →
  ((map-is-set-truncation B f is-settr-f C g) ∘ f) ~ g
triangle-is-set-truncation B f is-settr-f C g =
  pr2
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

is-set-truncation-id :
  {l1 : Level} {A : UU l1} (H : is-set A) →
  {l2 : Level} → is-set-truncation l2 (pair A H) id
is-set-truncation-id H B = is-equiv-precomp-is-equiv id is-equiv-id (type-Set B)

is-set-truncation-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (e : A ≃ type-Set B) →
  {l : Level} → is-set-truncation l2 B (map-equiv e)
is-set-truncation-equiv B e C =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Set C)

precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU-Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
dependent-universal-property-set-truncation l {A} B f =
  (X : type-Set B → UU-Set l) → is-equiv (precomp-Π-Set f X)

mere-eq-Eq-Rel : {l1 : Level} (A : UU l1) → Eq-Rel l1 A
mere-eq-Eq-Rel A =
  pair
    mere-eq-Prop
    ( pair refl-mere-eq (pair symm-mere-eq trans-mere-eq))
  
dependent-universal-property-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → is-set-truncation l B f) →
  dependent-universal-property-set-truncation l3 B f
dependent-universal-property-is-set-truncation {A = A} B f H X =
  is-fiberwise-equiv-is-equiv-map-Σ
    ( λ (h : A → type-Set B) → (a : A) → type-Set (X (h a)))
    ( λ (g : type-Set B → type-Set B) → g ∘ f)
    ( λ g (s : (b : type-Set B) → type-Set (X (g b))) (a : A) → s (f a))
    ( H B)
    ( is-equiv-equiv
      ( equiv-inv-choice-∞ (λ x y → type-Set (X y)))
      ( equiv-inv-choice-∞ (λ x y → type-Set (X y)))
      ( ind-Σ (λ g s → refl))
      ( H (Σ-Set B X)))
    ( id)

is-set-truncation-dependent-universal-property :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → dependent-universal-property-set-truncation l B f) →
  is-set-truncation l3 B f
is-set-truncation-dependent-universal-property B f H X =
  H (λ b → X)

reflects-mere-eq :
  {l1 l2 : Level} {A : UU l1} (X : UU-Set l2) (f : A → type-Set X) →
  reflects-Eq-Rel (mere-eq-Eq-Rel A) f
reflects-mere-eq X f {x} {y} r =
  apply-universal-property-trunc-Prop r
    ( Id-Prop X (f x) (f y))
    ( ap f)

reflecting-map-mere-eq :
  {l1 l2 : Level} {A : UU l1} (X : UU-Set l2) (f : A → type-Set X) →
  reflecting-map-Eq-Rel (mere-eq-Eq-Rel A) (type-Set X)
reflecting-map-mere-eq X f = pair f (reflects-mere-eq X f)

is-set-truncation-is-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ( {l : Level} →
    is-set-quotient l (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f)) →
  is-set-truncation l3 B f
is-set-truncation-is-set-quotient {A = A} B f H X =
  is-equiv-comp
    ( precomp-Set f X)
    ( pr1)
    ( precomp-Set-Quotient (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f) X)
    ( refl-htpy)
    ( H X)
    ( is-equiv-pr1-is-contr
      ( λ h →
        is-proof-irrelevant-is-prop
          ( is-prop-reflects-Eq-Rel (mere-eq-Eq-Rel A) X h)
          ( reflects-mere-eq X h)))

is-set-quotient-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ( {l : Level} → is-set-truncation l B f) →
  is-set-quotient l3 (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f)
is-set-quotient-is-set-truncation {A = A} B f H X =
  is-equiv-right-factor
    ( precomp-Set f X)
    ( pr1)
    ( precomp-Set-Quotient (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f) X)
    ( refl-htpy)
    ( is-equiv-pr1-is-contr
      ( λ h →
        is-proof-irrelevant-is-prop
          ( is-prop-reflects-Eq-Rel (mere-eq-Eq-Rel A) X h)
          ( reflects-mere-eq X h)))
    ( H X)

module _
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (C : UU-Set l3) (g : A → type-Set C) {h : type-hom-Set B C}
  (H : (h ∘ f) ~ g)
  where

  is-equiv-is-set-truncation-is-set-truncation :
    ({l : Level} → is-set-truncation l B f) →
    ({l : Level} → is-set-truncation l C g) →
    is-equiv h
  is-equiv-is-set-truncation-is-set-truncation Sf Sg =
    is-equiv-is-set-quotient-is-set-quotient
      ( mere-eq-Eq-Rel A)
      ( B)
      ( reflecting-map-mere-eq B f)
      ( C)
      ( reflecting-map-mere-eq C g)
      ( H)
      ( λ {l} → is-set-quotient-is-set-truncation B f Sf)
      ( λ {l} → is-set-quotient-is-set-truncation C g Sg)

  is-set-truncation-is-equiv-is-set-truncation :
    ({l : Level} → is-set-truncation l C g) → is-equiv h → 
    {l : Level} → is-set-truncation l B f
  is-set-truncation-is-equiv-is-set-truncation Sg Eh =
    is-set-truncation-is-set-quotient B f
      ( is-set-quotient-is-equiv-is-set-quotient
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( H)
        ( is-set-quotient-is-set-truncation C g Sg)
        ( Eh))

  is-set-truncation-is-set-truncation-is-equiv :
    is-equiv h → ({l : Level} → is-set-truncation l B f) →
    {l : Level} → is-set-truncation l C g
  is-set-truncation-is-set-truncation-is-equiv Eh Sf =
    is-set-truncation-is-set-quotient C g
      ( is-set-quotient-is-set-quotient-is-equiv
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( H)
        ( Eh)
        ( is-set-quotient-is-set-truncation B f Sf))

module _
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (C : UU-Set l3) (g : A → type-Set C)
  (Sf : {l : Level} → is-set-truncation l B f)
  (Sg : {l : Level} → is-set-truncation l C g)
  where

  uniqueness-set-truncation :
    is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ f) ~ g))
  uniqueness-set-truncation =
    uniqueness-set-quotient
      ( mere-eq-Eq-Rel A)
      ( B)
      ( reflecting-map-mere-eq B f)
      ( is-set-quotient-is-set-truncation B f Sf)
      ( C)
      ( reflecting-map-mere-eq C g)
      ( is-set-quotient-is-set-truncation C g Sg)
  
  equiv-uniqueness-set-truncation : type-Set B ≃ type-Set C
  equiv-uniqueness-set-truncation =
    pr1 (center uniqueness-set-truncation)

  map-equiv-uniqueness-set-truncation : type-Set B → type-Set C
  map-equiv-uniqueness-set-truncation =
    map-equiv equiv-uniqueness-set-truncation

  triangle-uniqueness-set-truncation :
    (map-equiv-uniqueness-set-truncation ∘ f) ~ g
  triangle-uniqueness-set-truncation =
    pr2 (center uniqueness-set-truncation)

postulate type-trunc-Set : {l : Level} → UU l → UU l

postulate
  is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)

trunc-Set : {l : Level} → UU l → UU-Set l
trunc-Set A = pair (type-trunc-Set A) is-set-type-trunc-Set

postulate unit-trunc-Set : {l : Level} {A : UU l} → A → type-Set (trunc-Set A)

postulate
  is-set-truncation-trunc-Set :
    {l1 l2 : Level} (A : UU l1) →
    is-set-truncation l2 (trunc-Set A) unit-trunc-Set

equiv-universal-property-trunc-Set :
  {l1 l2 : Level} (A : UU l1) (B : UU-Set l2) →
  (type-trunc-Set A → type-Set B) ≃ (A → type-Set B)
equiv-universal-property-trunc-Set A B =
  pair
    ( precomp-Set unit-trunc-Set B)
    ( is-set-truncation-trunc-Set A B)

universal-property-trunc-Set : {l1 l2 : Level} (A : UU l1) →
  universal-property-set-truncation l2
    ( trunc-Set A)
    ( unit-trunc-Set)
universal-property-trunc-Set A =
  universal-property-is-set-truncation _
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)

map-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (A → type-Set B) → type-hom-Set (trunc-Set A) B
map-universal-property-trunc-Set {A = A} B f =
  map-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)
    ( B)
    ( f)

triangle-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (f : A → type-Set B) →
  (map-universal-property-trunc-Set B f ∘ unit-trunc-Set) ~ f
triangle-universal-property-trunc-Set {A = A} B f =
  triangle-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)
    ( B)
    ( f)

apply-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Set A) (B : UU-Set l2) →
  (A → type-Set B) → type-Set B
apply-universal-property-trunc-Set t B f =
  map-universal-property-trunc-Set B f t

dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) → 
  is-equiv (precomp-Π-Set unit-trunc-Set B)
dependent-universal-property-trunc-Set {A = A} =
  dependent-universal-property-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( λ {l} → is-set-truncation-trunc-Set A)

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set B =
  pair ( precomp-Π-Set unit-trunc-Set B)
       ( dependent-universal-property-trunc-Set B)

apply-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1}
  (B : type-trunc-Set A → UU-Set l2) →
  ((x : A) → type-Set (B (unit-trunc-Set x))) →
  (x : type-trunc-Set A) → type-Set (B x)
apply-dependent-universal-property-trunc-Set B =
  map-inv-equiv (equiv-dependent-universal-property-trunc-Set B)

reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-Eq-Rel (mere-eq-Eq-Rel A) (type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A =
  pair unit-trunc-Set (reflects-mere-eq (trunc-Set A) unit-trunc-Set)

is-set-quotient-trunc-Set :
  {l1 l2 : Level} (A : UU l1) →
  is-set-quotient l2
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( reflecting-map-mere-eq-unit-trunc-Set A)
is-set-quotient-trunc-Set A =
  is-set-quotient-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( λ {l} → is-set-truncation-trunc-Set A)

is-surjective-and-effective-unit-trunc-Set :
  {l1 : Level} (A : UU l1) →
  is-surjective-and-effective (mere-eq-Eq-Rel A) unit-trunc-Set
is-surjective-and-effective-unit-trunc-Set A =
  is-surjective-and-effective-is-set-quotient
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( reflects-mere-eq (trunc-Set A) unit-trunc-Set)
    ( λ {l} → is-set-quotient-trunc-Set A)

is-surjective-unit-trunc-Set :
  {l1 : Level} (A : UU l1) → is-surjective (unit-trunc-Set {A = A})
is-surjective-unit-trunc-Set A =
  pr1 (is-surjective-and-effective-unit-trunc-Set A)

is-effective-unit-trunc-Set :
  {l1 : Level} (A : UU l1) →
  is-effective (mere-eq-Eq-Rel A) (unit-trunc-Set {A = A})
is-effective-unit-trunc-Set A =
  pr2 (is-surjective-and-effective-unit-trunc-Set A)

apply-effectiveness-unit-trunc-Set :
  {l1 : Level} {A : UU l1} {x y : A} →
  Id (unit-trunc-Set x) (unit-trunc-Set y) → mere-eq x y
apply-effectiveness-unit-trunc-Set {A = A} {x} {y} =
  map-equiv (is-effective-unit-trunc-Set A x y)

apply-effectiveness-unit-trunc-Set' :
  {l1 : Level} {A : UU l1} {x y : A} →
  mere-eq x y → Id (unit-trunc-Set x) (unit-trunc-Set y)
apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} =
  map-inv-equiv (is-effective-unit-trunc-Set A x y)

emb-trunc-Set :
  {l1 : Level} (A : UU l1) → type-trunc-Set A ↪ (A → UU-Prop l1)
emb-trunc-Set A =
  emb-is-surjective-and-effective
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-surjective-and-effective-unit-trunc-Set A)

hom-slice-trunc-Set :
  {l1 : Level} (A : UU l1) →
  hom-slice (mere-eq-Prop {A = A}) (map-emb (emb-trunc-Set A))
hom-slice-trunc-Set A =
  pair
    ( unit-trunc-Set)
    ( triangle-emb-is-surjective-and-effective
      ( mere-eq-Eq-Rel A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-surjective-and-effective-unit-trunc-Set A))

is-image-trunc-Set :
  {l1 l2 : Level} (A : UU l1) →
  is-image l2
    ( mere-eq-Prop {A = A})
    ( emb-trunc-Set A)
    ( hom-slice-trunc-Set A)
is-image-trunc-Set A =
  is-image-is-surjective-and-effective
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-surjective-and-effective-unit-trunc-Set A)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  {h : type-hom-Set B (trunc-Set A)} (H : (h ∘ f) ~ unit-trunc-Set)
  where

  is-equiv-is-set-truncation' :
    ({l : Level} → is-set-truncation l B f) → is-equiv h
  is-equiv-is-set-truncation' Sf =
    is-equiv-is-set-truncation-is-set-truncation
      ( B)
      ( f)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( H)
      ( Sf)
      ( λ {h} → is-set-truncation-trunc-Set A)

  is-set-truncation-is-equiv' :
    is-equiv h → ({l : Level} → is-set-truncation l B f)
  is-set-truncation-is-equiv' Eh =
    is-set-truncation-is-equiv-is-set-truncation
      ( B)
      ( f)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( H)
      ( λ {l} → is-set-truncation-trunc-Set A)
      ( Eh)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  {h : type-hom-Set (trunc-Set A) B} (H : (h ∘ unit-trunc-Set) ~ f)
  where

  is-equiv-is-set-truncation :
    ({l : Level} → is-set-truncation l B f) → is-equiv h
  is-equiv-is-set-truncation Sf =
    is-equiv-is-set-truncation-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( B)
      ( f)
      ( H)
      ( λ {l} → is-set-truncation-trunc-Set A)
      ( Sf)

  is-set-truncation-is-equiv :
    is-equiv h → ({l : Level} → is-set-truncation l B f)
  is-set-truncation-is-equiv Eh =
    is-set-truncation-is-set-truncation-is-equiv
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( B)
      ( f)
      ( H)
      ( Eh)
      ( λ {l} → is-set-truncation-trunc-Set A)

is-equiv-unit-trunc-Set :
  {l : Level} (A : UU-Set l) → is-equiv (unit-trunc-Set {A = type-Set A})
is-equiv-unit-trunc-Set A =
  is-equiv-is-set-truncation' A id refl-htpy
    ( is-set-truncation-id (is-set-type-Set A))

equiv-unit-trunc-Set :
  {l : Level} (A : UU-Set l) → type-Set A ≃ type-trunc-Set (type-Set A)
equiv-unit-trunc-Set A =
  pair unit-trunc-Set (is-equiv-unit-trunc-Set A)

equiv-unit-trunc-empty-Set : empty ≃ type-trunc-Set empty
equiv-unit-trunc-empty-Set = equiv-unit-trunc-Set empty-Set

is-empty-trunc-Set :
  {l : Level} {A : UU l} → is-empty A → is-empty (type-trunc-Set A)
is-empty-trunc-Set f x = apply-universal-property-trunc-Set x empty-Set f

is-empty-is-empty-trunc-Set :
  {l : Level} {A : UU l} → is-empty (type-trunc-Set A) → is-empty A
is-empty-is-empty-trunc-Set f = f ∘ unit-trunc-Set

equiv-unit-trunc-unit-Set : unit ≃ type-trunc-Set unit
equiv-unit-trunc-unit-Set = equiv-unit-trunc-Set unit-Set

equiv-unit-trunc-ℕ-Set : ℕ ≃ type-trunc-Set ℕ
equiv-unit-trunc-ℕ-Set = equiv-unit-trunc-Set ℕ-Set

equiv-unit-trunc-ℤ-Set : ℤ ≃ type-trunc-Set ℤ
equiv-unit-trunc-ℤ-Set = equiv-unit-trunc-Set ℤ-Set

equiv-unit-trunc-Fin-Set : (k : ℕ) → Fin k ≃ type-trunc-Set (Fin k)
equiv-unit-trunc-Fin-Set k = equiv-unit-trunc-Set (Fin-Set k)

is-contr-trunc-Set :
  {l : Level} {A : UU l} → is-contr A → is-contr (type-trunc-Set A)
is-contr-trunc-Set {l} {A} H =
  is-contr-equiv'
    ( A)
    ( equiv-unit-trunc-Set (pair A (is-set-is-contr H)))
    ( H)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (Sf : {l : Level} → is-set-truncation l B f)
  where

  uniqueness-trunc-Set :
    is-contr
      ( Σ (type-trunc-Set A ≃ type-Set B)
      ( λ e → (map-equiv e ∘ unit-trunc-Set) ~ f))
  uniqueness-trunc-Set =
    uniqueness-set-truncation (trunc-Set A) unit-trunc-Set B f
      ( λ {l} → is-set-truncation-trunc-Set A)
      ( Sf)

  equiv-uniqueness-trunc-Set : type-trunc-Set A ≃ type-Set B
  equiv-uniqueness-trunc-Set =
    pr1 (center uniqueness-trunc-Set)

  map-equiv-uniqueness-trunc-Set : type-trunc-Set A → type-Set B
  map-equiv-uniqueness-trunc-Set =
    map-equiv equiv-uniqueness-trunc-Set

  triangle-uniqueness-trunc-Set :
    (map-equiv-uniqueness-trunc-Set ∘ unit-trunc-Set) ~ f
  triangle-uniqueness-trunc-Set =
    pr2 (center uniqueness-trunc-Set)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (Sf : {l : Level} → is-set-truncation l B f)
  where

  uniqueness-trunc-Set' :
    is-contr
      ( Σ ( type-Set B ≃ type-trunc-Set A)
          ( λ e → (map-equiv e ∘ f) ~ unit-trunc-Set))
  uniqueness-trunc-Set' =
    uniqueness-set-truncation B f (trunc-Set A) unit-trunc-Set Sf
      ( λ {l} → is-set-truncation-trunc-Set A)

  equiv-uniqueness-trunc-Set' : type-Set B ≃ type-trunc-Set A
  equiv-uniqueness-trunc-Set' =
    pr1 (center uniqueness-trunc-Set')

  map-equiv-uniqueness-trunc-Set' : type-Set B → type-trunc-Set A
  map-equiv-uniqueness-trunc-Set' =
    map-equiv equiv-uniqueness-trunc-Set'
  
  triangle-uniqueness-trunc-Set' :
    (map-equiv-uniqueness-trunc-Set' ∘ f) ~ unit-trunc-Set
  triangle-uniqueness-trunc-Set' =
    pr2 (center uniqueness-trunc-Set')

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  unique-map-trunc-Set :
    is-contr
      ( Σ ( type-trunc-Set A → type-trunc-Set B)
          ( λ h → (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)))
  unique-map-trunc-Set =
    universal-property-trunc-Set A (trunc-Set B) (unit-trunc-Set ∘ f)

  map-trunc-Set :
    type-trunc-Set A → type-trunc-Set B
  map-trunc-Set =
    pr1 (center unique-map-trunc-Set)

  naturality-trunc-Set :
    (map-trunc-Set ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)
  naturality-trunc-Set =
    pr2 (center unique-map-trunc-Set)

  htpy-map-trunc-Set :
    (h : type-trunc-Set A → type-trunc-Set B) →
    (H : (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)) →
    map-trunc-Set ~ h
  htpy-map-trunc-Set h H =
    htpy-eq
      ( ap pr1
        ( eq-is-contr unique-map-trunc-Set
          { pair map-trunc-Set naturality-trunc-Set}
          { pair h H}))

map-id-trunc-Set :
  {l1 : Level} {A : UU l1} → map-trunc-Set (id {A = A}) ~ id
map-id-trunc-Set {l1} {A} =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( universal-property-trunc-Set A (trunc-Set A) unit-trunc-Set)
        { pair (map-trunc-Set id) (naturality-trunc-Set id)}
        { pair id refl-htpy}))

map-comp-trunc-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-trunc-Set (g ∘ f) ~ (map-trunc-Set g ∘ map-trunc-Set f)
map-comp-trunc-Set {A = A} {C = C} g f =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( universal-property-trunc-Set
          A
          (trunc-Set C)
          (unit-trunc-Set ∘ (g ∘ f)))
        { pair (map-trunc-Set (g ∘ f)) (naturality-trunc-Set (g ∘ f))}
        { pair ( map-trunc-Set g ∘ map-trunc-Set f)
               ( ( map-trunc-Set g ·l naturality-trunc-Set f) ∙h
                 ( naturality-trunc-Set g ·r f))}))

htpy-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-trunc-Set f ~ map-trunc-Set g)
htpy-trunc-Set {B = B} {f = f} {g} H =
  map-inv-is-equiv
    ( dependent-universal-property-trunc-Set
      ( λ x →
        set-Prop
          ( Id-Prop (trunc-Set B) (map-trunc-Set f x) (map-trunc-Set g x))))
    ( λ a →
      ( naturality-trunc-Set f a) ∙
      ( ( ap unit-trunc-Set (H a)) ∙
        ( inv (naturality-trunc-Set g a))))

is-equiv-map-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-equiv (map-trunc-Set f)
is-equiv-map-trunc-Set {f = f} H =
  pair
    ( pair
      ( map-trunc-Set (pr1 (pr1 H)))
      ( ( inv-htpy (map-comp-trunc-Set f (pr1 (pr1 H)))) ∙h
        ( ( htpy-trunc-Set (pr2 (pr1 H))) ∙h
          ( map-id-trunc-Set))))
    ( pair
      ( map-trunc-Set (pr1 (pr2 H)))
      ( ( inv-htpy (map-comp-trunc-Set (pr1 (pr2 H)) f)) ∙h
        ( ( htpy-trunc-Set (pr2 (pr2 H))) ∙h
          ( map-id-trunc-Set))))

equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (type-trunc-Set A ≃ type-trunc-Set B)
equiv-trunc-Set e =
  pair
    ( map-trunc-Set (map-equiv e))
    ( is-equiv-map-trunc-Set (is-equiv-map-equiv e))

map-equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Set A → type-trunc-Set B
map-equiv-trunc-Set e = map-equiv (equiv-trunc-Set e)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  distributive-trunc-coprod-Set :
    is-contr
      ( Σ ( type-equiv-Set
            ( trunc-Set (coprod A B))
            ( coprod-Set (trunc-Set A) (trunc-Set B)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-coprod unit-trunc-Set unit-trunc-Set)))
  distributive-trunc-coprod-Set =
    uniqueness-trunc-Set
      ( coprod-Set (trunc-Set A) (trunc-Set B))
      ( map-coprod unit-trunc-Set unit-trunc-Set)
      ( λ {l} C →
        is-equiv-right-factor'
          ( ev-inl-inr (λ x → type-Set C))
          ( precomp-Set (map-coprod unit-trunc-Set unit-trunc-Set) C)
          ( universal-property-coprod (type-Set C))
          ( is-equiv-comp'
            ( map-prod
              ( precomp-Set unit-trunc-Set C)
              ( precomp-Set unit-trunc-Set C))
            ( ev-inl-inr (λ x → type-Set C))
            ( universal-property-coprod (type-Set C))
            ( is-equiv-map-prod
              ( precomp-Set unit-trunc-Set C)
              ( precomp-Set unit-trunc-Set C)
              ( is-set-truncation-trunc-Set A C)
              ( is-set-truncation-trunc-Set B C))))

  equiv-distributive-trunc-coprod-Set :
    type-equiv-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  equiv-distributive-trunc-coprod-Set =
    pr1 (center distributive-trunc-coprod-Set)

  map-equiv-distributive-trunc-coprod-Set :
    type-hom-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  map-equiv-distributive-trunc-coprod-Set =
    map-equiv equiv-distributive-trunc-coprod-Set

  triangle-distributive-trunc-coprod-Set :
    ( map-equiv-distributive-trunc-coprod-Set ∘ unit-trunc-Set) ~
    ( map-coprod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-coprod-Set =
    pr2 (center distributive-trunc-coprod-Set)

module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where
  
  trunc-Σ-Set :
    is-contr
      ( Σ ( type-trunc-Set (Σ A B) ≃
            type-trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))))
  trunc-Σ-Set =
    uniqueness-trunc-Set
      ( trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
      ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
      ( λ {l} C →
        is-equiv-right-factor'
          ( ev-pair)
          ( precomp-Set (unit-trunc-Set ∘ tot (λ x → unit-trunc-Set)) C)
          ( is-equiv-ev-pair)
          ( is-equiv-htpy-equiv
            ( ( equiv-map-Π
                ( λ x → equiv-universal-property-trunc-Set (B x) C)) ∘e
              ( ( equiv-ev-pair) ∘e
                ( equiv-universal-property-trunc-Set
                  ( Σ A (type-trunc-Set ∘ B)) C)))
            ( refl-htpy)))

  equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) ≃ type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  equiv-trunc-Σ-Set =
    pr1 (center trunc-Σ-Set)

  map-equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) → type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  map-equiv-trunc-Σ-Set =
    map-equiv equiv-trunc-Σ-Set

  square-trunc-Σ-Set :
    ( map-equiv-trunc-Σ-Set ∘ unit-trunc-Set) ~
    ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
  square-trunc-Σ-Set =
    pr2 (center trunc-Σ-Set)

  htpy-map-equiv-trunc-Σ-Set :
    map-trunc-Set (tot (λ x → unit-trunc-Set)) ~ map-equiv-trunc-Σ-Set
  htpy-map-equiv-trunc-Σ-Set =
    htpy-map-trunc-Set
      ( tot (λ x → unit-trunc-Set))
      ( map-equiv-trunc-Σ-Set)
      ( square-trunc-Σ-Set)

  is-equiv-map-trunc-tot-unit-trunc-Set :
    is-equiv (map-trunc-Set (tot (λ (x : A) → unit-trunc-Set {A = B x})))
  is-equiv-map-trunc-tot-unit-trunc-Set =
    is-equiv-htpy-equiv
      ( equiv-trunc-Σ-Set)
      ( htpy-map-equiv-trunc-Σ-Set)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  distributive-trunc-prod-Set :
    is-contr
      ( Σ ( type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-prod unit-trunc-Set unit-trunc-Set)))
  distributive-trunc-prod-Set =
    uniqueness-trunc-Set
      ( prod-Set (trunc-Set A) (trunc-Set B))
      ( map-prod unit-trunc-Set unit-trunc-Set)
      ( λ {l} C →
        is-equiv-right-factor'
          ( ev-pair)
          ( precomp-Set (map-prod unit-trunc-Set unit-trunc-Set) C)
          ( is-equiv-ev-pair)
          ( is-equiv-htpy-equiv
            ( ( equiv-universal-property-trunc-Set A (Π-Set' B (λ y → C))) ∘e
              ( ( equiv-postcomp
                  ( type-trunc-Set A)
                  (equiv-universal-property-trunc-Set B C)) ∘e
                ( equiv-ev-pair)))
            ( refl-htpy)))

  equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B)
  equiv-distributive-trunc-prod-Set =
    pr1 (center distributive-trunc-prod-Set)

  map-equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) → type-trunc-Set A × type-trunc-Set B
  map-equiv-distributive-trunc-prod-Set =
    map-equiv equiv-distributive-trunc-prod-Set

  triangle-distributive-trunc-prod-Set :
    ( map-equiv-distributive-trunc-prod-Set ∘ unit-trunc-Set) ~
    ( map-prod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-prod-Set =
    pr2 (center distributive-trunc-prod-Set)

distributive-trunc-Π-Fin-Set :
  {l : Level} (k : ℕ) (A : Fin k → UU l) →
  is-contr
    ( Σ ( ( type-trunc-Set ((x : Fin k) → A x)) ≃
          ( (x : Fin k) → type-trunc-Set (A x)))
        ( λ e →
          ( map-equiv e ∘ unit-trunc-Set) ~
          ( map-Π (λ x → unit-trunc-Set))))
distributive-trunc-Π-Fin-Set zero-ℕ A =
  uniqueness-trunc-Set
    ( Π-Set empty-Set (λ x → trunc-Set (A x)))
    ( map-Π (λ x → unit-trunc-Set))
    ( λ {l} B →
      is-equiv-precomp-is-equiv
        ( map-Π (λ x → unit-trunc-Set))
        ( is-equiv-is-contr
          ( map-Π (λ x → unit-trunc-Set))
          ( dependent-universal-property-empty' A)
          ( dependent-universal-property-empty' (type-trunc-Set ∘ A)))
        ( type-Set B))
distributive-trunc-Π-Fin-Set (succ-ℕ k) A =
  uniqueness-trunc-Set
    ( Π-Set (Fin-Set (succ-ℕ k)) (λ x → trunc-Set (A x)))
    ( map-Π (λ x → unit-trunc-Set))
    ( λ {l} B →
      is-equiv-left-factor'
        ( precomp (map-Π (λ x → unit-trunc-Set)) (type-Set B))
        ( precomp (ev-Maybe {B = type-trunc-Set ∘ A}) (type-Set B))
        ( is-equiv-comp'
          ( precomp ev-Maybe (type-Set B))
          ( precomp
            ( map-prod (map-Π (λ x → unit-trunc-Set)) unit-trunc-Set)
            ( type-Set B))
          ( is-equiv-right-factor'
            ( ev-pair)
            ( precomp
              ( map-prod (map-Π (λ x → unit-trunc-Set)) unit-trunc-Set)
              ( type-Set B))
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( ( pair
                    ( precomp
                      ( (map-Π (λ x → unit-trunc-Set)))
                      ( A (inr star) → type-Set B))
                    ( is-set-truncation-is-equiv
                      ( Π-Set (Fin-Set k) (λ x → trunc-Set (A (inl x))))
                      ( map-Π (λ x → unit-trunc-Set))
                      { map-equiv
                        ( pr1
                          ( center
                            ( distributive-trunc-Π-Fin-Set k (A ∘ inl))))}
                      ( pr2
                        ( center (distributive-trunc-Π-Fin-Set k (A ∘ inl))))
                      ( is-equiv-map-equiv
                        ( pr1
                          ( center
                            ( distributive-trunc-Π-Fin-Set k (A ∘ inl)))))
                      ( Π-Set' (A (inr star)) (λ a → B)))) ∘e
                  ( equiv-postcomp
                    ( (x : Fin k) → type-trunc-Set (A (inl x)))
                    ( equiv-universal-property-trunc-Set (A (inr star)) B))) ∘e
                ( equiv-ev-pair))
              ( refl-htpy)))
          ( is-equiv-precomp-is-equiv
            ( ev-Maybe)
            ( dependent-universal-property-Maybe)
            ( type-Set B)))
        ( is-equiv-precomp-is-equiv
          ( ev-Maybe)
          ( dependent-universal-property-Maybe)
          ( type-Set B)))

module _
  {l : Level} (k : ℕ) (A : Fin k → UU l)
  where

  equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) ≃ ((x : Fin k) → type-trunc-Set (A x))
  equiv-distributive-trunc-Π-Fin-Set =
    pr1 (center (distributive-trunc-Π-Fin-Set k A))

  map-equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) → ((x : Fin k) → type-trunc-Set (A x))
  map-equiv-distributive-trunc-Π-Fin-Set =
    map-equiv equiv-distributive-trunc-Π-Fin-Set

  triangle-distributive-trunc-Π-Fin-Set :
    ( map-equiv-distributive-trunc-Π-Fin-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-Fin-Set =
    pr2 (center (distributive-trunc-Π-Fin-Set k A))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (c : count A)
  where
  
  distributive-trunc-Π-count-Set :
    is-contr
      ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
            ( (x : A) → type-trunc-Set (B x)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-count-Set =
    is-contr-equiv
      ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
            ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
          ( λ f →
            ( map-equiv f ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B)))
      ( equiv-Σ
        ( λ f →
          ( map-equiv f ∘ unit-trunc-Set) ~
          ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B))
        ( equiv-postcomp-equiv
          ( equiv-precomp-Π e (type-trunc-Set ∘ B))
          ( type-trunc-Set ((x : A) → B x)))
        ( λ f →
          equiv-map-Π
            ( λ h →
              ( ( inv-equiv equiv-funext) ∘e
                ( equiv-precomp-Π e
                  ( λ x → Id ((map-equiv f ∘ unit-trunc-Set) h x)
                  ( map-Π (λ y → unit-trunc-Set) h x)))) ∘e
              ( equiv-funext))))
      ( is-contr-equiv'
        ( Σ ( ( type-trunc-Set ((x : Fin k) → B (map-equiv e x))) ≃
              ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
            ( λ f →
              ( map-equiv f ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set))))
        ( equiv-Σ
          ( λ f →
            ( map-equiv f ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B))
          ( equiv-precomp-equiv
            ( equiv-trunc-Set (equiv-precomp-Π e B))
            ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
          ( λ f →
            equiv-Π
              ( λ h →
                Id ( map-equiv f
                     ( map-equiv
                       ( equiv-trunc-Set (equiv-precomp-Π e B))
                       ( unit-trunc-Set h)))
                   ( map-Π (λ x → unit-trunc-Set) (λ x → h (map-equiv e x))))
              ( equiv-Π B e (λ x → equiv-id))
              ( λ h →
                ( ( inv-equiv equiv-funext) ∘e
                  ( equiv-Π
                    ( λ x →
                      Id ( map-equiv f
                           ( map-equiv-trunc-Set
                             ( equiv-precomp-Π e B)
                             ( unit-trunc-Set
                               ( map-equiv-Π B e (λ x → equiv-id) h)))
                           ( x))
                         ( unit-trunc-Set
                           ( map-equiv-Π B e
                             ( λ z → equiv-id)
                             ( h)
                             ( map-equiv e x))))
                    ( equiv-id)
                    ( λ x →
                      ( equiv-concat
                        ( ap
                          ( λ t → map-equiv f t x)
                          ( ( naturality-trunc-Set (precomp-Π (map-equiv e) B)
                              ( map-equiv-Π B e (λ _ → equiv-id) h)) ∙
                            ( ap
                              ( unit-trunc-Set)
                              ( eq-htpy
                                ( compute-map-equiv-Π B e
                                  ( λ _ → equiv-id)
                                  ( h))))))
                        ( unit-trunc-Set
                          ( map-equiv-Π B e
                            ( λ _ → equiv-id)
                            ( h)
                            ( map-equiv e x)))) ∘e
                      ( equiv-concat'
                        ( map-equiv f (unit-trunc-Set h) x)
                        ( ap unit-trunc-Set
                          ( inv
                            ( compute-map-equiv-Π B e
                              ( λ _ → equiv-id)
                              ( h)
                              ( x)))))))) ∘e
                ( equiv-funext))))
        ( distributive-trunc-Π-Fin-Set k (B ∘ map-equiv e)))
    where
    k = pr1 c
    e = pr2 c

  equiv-distributive-trunc-Π-count-Set :
    ( type-trunc-Set ((x : A) → B x)) ≃ ((x : A) → type-trunc-Set (B x))
  equiv-distributive-trunc-Π-count-Set =
    pr1 (center distributive-trunc-Π-count-Set)

  map-equiv-distributive-trunc-Π-count-Set :
    ( type-trunc-Set ((x : A) → B x)) → ((x : A) → type-trunc-Set (B x))
  map-equiv-distributive-trunc-Π-count-Set =
    map-equiv equiv-distributive-trunc-Π-count-Set

  triangle-distributive-trunc-Π-count-Set :
    ( map-equiv-distributive-trunc-Π-count-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-count-Set =
    pr2 (center distributive-trunc-Π-count-Set)

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (H : is-finite A)
  where
  
  distributive-trunc-Π-is-finite-Set :
    is-contr
      ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
            ( (x : A) → type-trunc-Set (B x)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-is-finite-Set =
    apply-universal-property-trunc-Prop H
      ( is-contr-Prop _)
      ( distributive-trunc-Π-count-Set B)

  equiv-distributive-trunc-Π-is-finite-Set :
    ( type-trunc-Set ((x : A) → B x)) ≃ ((x : A) → type-trunc-Set (B x))
  equiv-distributive-trunc-Π-is-finite-Set =
    pr1 (center distributive-trunc-Π-is-finite-Set)

  map-equiv-distributive-trunc-Π-is-finite-Set :
    ( type-trunc-Set ((x : A) → B x)) → ((x : A) → type-trunc-Set (B x))
  map-equiv-distributive-trunc-Π-is-finite-Set =
    map-equiv equiv-distributive-trunc-Π-is-finite-Set

  triangle-distributive-trunc-Π-is-finite-Set :
    ( map-equiv-distributive-trunc-Π-is-finite-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-is-finite-Set =
    pr2 (center distributive-trunc-Π-is-finite-Set)

is-path-connected-Prop : {l : Level} → UU l → UU-Prop l
is-path-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-path-connected : {l : Level} → UU l → UU l
is-path-connected A = type-Prop (is-path-connected-Prop A)

is-inhabited-is-path-connected :
  {l : Level} {A : UU l} → is-path-connected A → type-trunc-Prop A
is-inhabited-is-path-connected {l} {A} C =
  apply-universal-property-trunc-Set
    ( center C)
    ( set-Prop (trunc-Prop A))
    ( unit-trunc-Prop)

mere-eq-is-path-connected :
  {l : Level} {A : UU l} → is-path-connected A → (x y : A) → mere-eq x y
mere-eq-is-path-connected {A = A} H x y =
  apply-effectiveness-unit-trunc-Set (eq-is-contr H)

is-path-connected-mere-eq :
  {l : Level} {A : UU l} (a : A) → ((x : A) → mere-eq a x) → is-path-connected A
is-path-connected-mere-eq {l} {A} a e =
  pair
    ( unit-trunc-Set a)
    ( apply-dependent-universal-property-trunc-Set
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

is-surjective-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-path-connected A → (a : A) → is-surjective (fiber-inclusion B a)
is-surjective-fiber-inclusion {B = B} C a (pair x b) =
  apply-universal-property-trunc-Prop
    ( mere-eq-is-path-connected C a x)
    ( trunc-Prop (fib (fiber-inclusion B a) (pair x b)))
    ( λ { refl → unit-trunc-Prop (pair b refl)})

mere-eq-is-surjective-fiber-inclusion :
  {l1 : Level} {A : UU l1} (a : A) →
  ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
  (x : A) → mere-eq a x
mere-eq-is-surjective-fiber-inclusion a H x =
  apply-universal-property-trunc-Prop
    ( H (λ x → unit) (pair x star))
    ( mere-eq-Prop a x)
    ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

is-path-connected-is-surjective-fiber-inclusion :
  {l1 : Level} {A : UU l1} (a : A) →
  ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
  is-path-connected A
is-path-connected-is-surjective-fiber-inclusion a H =
  is-path-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)

mere-eq-mere-equiv :
  {l : Level} {A B : UU l} → mere-equiv A B → mere-eq A B
mere-eq-mere-equiv {l} {A} {B} = functor-trunc-Prop (eq-equiv A B)

is-path-connected-UU-Fin-Level :
  {l : Level} (n : ℕ) → is-path-connected (UU-Fin-Level l n)
is-path-connected-UU-Fin-Level {l} n =
  is-path-connected-mere-eq
    ( Fin-UU-Fin-Level l n)
    ( λ A →
      functor-trunc-Prop
        ( ( eq-equiv-UU-Fin-Level (Fin-UU-Fin-Level l n) A) ∘
          ( map-equiv
            ( equiv-precomp-equiv
              ( inv-equiv (equiv-raise l (Fin n)))
              ( type-UU-Fin-Level A))))
        ( pr2 A))

is-path-connected-UU-Fin :
  (n : ℕ) → is-path-connected (UU-Fin n)
is-path-connected-UU-Fin n =
  is-path-connected-mere-eq
    ( Fin-UU-Fin n)
    ( λ A → functor-trunc-Prop (eq-equiv-UU-Fin (Fin-UU-Fin n) A) (pr2 A))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  is-injective-map-trunc-Set :
    is-injective f → is-injective (map-trunc-Set f)
  is-injective-map-trunc-Set H {x} {y} =
    apply-dependent-universal-property-trunc-Set
      ( λ u →
        set-Prop
          ( function-Prop (Id (map-trunc-Set f u) (map-trunc-Set f y))
          ( Id-Prop (trunc-Set A) u y) ))
      ( λ a →
        apply-dependent-universal-property-trunc-Set
        ( λ v →
          set-Prop
            ( function-Prop
              ( Id (map-trunc-Set f (unit-trunc-Set a)) (map-trunc-Set f v))
              ( Id-Prop (trunc-Set A) (unit-trunc-Set a) v)))
        ( λ b p →
          apply-universal-property-trunc-Prop
            ( apply-effectiveness-unit-trunc-Set
              ( ( inv (naturality-trunc-Set f a)) ∙
                ( p ∙ (naturality-trunc-Set f b))))
            ( Id-Prop (trunc-Set A) (unit-trunc-Set a) (unit-trunc-Set b))
            ( λ q → ap unit-trunc-Set (H q)))
        ( y))
      ( x)

  is-surjective-map-trunc-Set :
    is-surjective f → is-surjective (map-trunc-Set f)
  is-surjective-map-trunc-Set H =
    apply-dependent-universal-property-trunc-Set
      ( λ x → set-Prop (trunc-Prop (fib (map-trunc-Set f) x)))
      ( λ b →
        apply-universal-property-trunc-Prop
          ( H b)
          ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set b)))
          ( λ { (pair a p) →
                unit-trunc-Prop
                  ( pair
                    ( unit-trunc-Set a)
                    ( naturality-trunc-Set f a ∙ ap unit-trunc-Set p))}))

  is-surjective-is-surjective-map-trunc-Set :
    is-surjective (map-trunc-Set f) → is-surjective f
  is-surjective-is-surjective-map-trunc-Set H b =
    apply-universal-property-trunc-Prop
      ( H (unit-trunc-Set b))
      ( trunc-Prop (fib f b))
      ( λ { (pair x p) →
            apply-universal-property-trunc-Prop
              ( is-surjective-unit-trunc-Set A x)
              ( trunc-Prop (fib f b))
              ( λ { (pair a refl) →
                    apply-universal-property-trunc-Prop
                      ( apply-effectiveness-unit-trunc-Set
                        ( inv (naturality-trunc-Set f a) ∙ p))
                      ( trunc-Prop (fib f b))
                      ( λ q → unit-trunc-Prop (pair a q))})})

im-Set :
  {l1 l2 : Level} {A : UU l2} (X : UU-Set l1) (f : A → type-Set X) →
  UU-Set (l1 ⊔ l2)
im-Set X f = pair (im f) (is-set-im f (is-set-type-Set X))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  inclusion-trunc-im-Set : type-trunc-Set (im f) → type-trunc-Set B
  inclusion-trunc-im-Set = map-trunc-Set (inclusion-im f)

  is-emb-inclusion-trunc-im-Set : is-emb inclusion-trunc-im-Set
  is-emb-inclusion-trunc-im-Set =
    is-emb-is-injective
      ( is-set-type-trunc-Set)
      ( is-injective-map-trunc-Set
        ( inclusion-im f)
        ( is-injective-is-emb (is-emb-inclusion-im f)))

  emb-trunc-im-Set : type-trunc-Set (im f) ↪ type-trunc-Set B
  emb-trunc-im-Set = pair inclusion-trunc-im-Set is-emb-inclusion-trunc-im-Set

  is-injective-inclusion-trunc-im-Set : is-injective inclusion-trunc-im-Set
  is-injective-inclusion-trunc-im-Set =
    is-injective-is-emb is-emb-inclusion-trunc-im-Set

  map-hom-slice-trunc-im-Set : type-trunc-Set A → type-trunc-Set (im f)
  map-hom-slice-trunc-im-Set = map-trunc-Set (map-unit-im f)

  triangle-hom-slice-trunc-im-Set :
    map-trunc-Set f ~ (inclusion-trunc-im-Set ∘ map-trunc-Set (map-unit-im f))
  triangle-hom-slice-trunc-im-Set =
    ( htpy-trunc-Set (triangle-unit-im f)) ∙h
    ( map-comp-trunc-Set (inclusion-im f) (map-unit-im f))

  hom-slice-trunc-im-Set : hom-slice (map-trunc-Set f) inclusion-trunc-im-Set
  hom-slice-trunc-im-Set =
    pair map-hom-slice-trunc-im-Set triangle-hom-slice-trunc-im-Set

  is-surjective-map-hom-slice-trunc-im-Set :
    is-surjective map-hom-slice-trunc-im-Set
  is-surjective-map-hom-slice-trunc-im-Set =
    is-surjective-map-trunc-Set
      ( map-unit-im f)
      ( is-surjective-map-unit-im f)
  
  is-image-trunc-im-Set :
    {l : Level} →
    is-image l
      ( map-trunc-Set f)
      ( emb-trunc-im-Set)
      ( hom-slice-trunc-im-Set)
  is-image-trunc-im-Set =
    is-image-is-surjective
      ( map-trunc-Set f)
      ( emb-trunc-im-Set)
      ( hom-slice-trunc-im-Set)
      ( is-surjective-map-hom-slice-trunc-im-Set)

  unique-equiv-trunc-im-Set :
    is-contr
      ( Σ ( equiv-slice (inclusion-im (map-trunc-Set f)) inclusion-trunc-im-Set)
          ( λ e →
            htpy-hom-slice (map-trunc-Set f)
              ( inclusion-trunc-im-Set)
              ( comp-hom-slice (map-trunc-Set f)
                ( inclusion-im (map-trunc-Set f))
                ( inclusion-trunc-im-Set)
                ( hom-equiv-slice
                  ( inclusion-im (map-trunc-Set f))
                  ( inclusion-trunc-im-Set)
                  ( e))
                ( hom-slice-im (map-trunc-Set f)))
              ( hom-slice-trunc-im-Set)))
  unique-equiv-trunc-im-Set =
    uniqueness-im
      ( map-trunc-Set f)
      ( emb-trunc-im-Set)
      ( hom-slice-trunc-im-Set)
      ( is-image-trunc-im-Set)

  equiv-slice-trunc-im-Set :
    equiv-slice (inclusion-im (map-trunc-Set f)) inclusion-trunc-im-Set
  equiv-slice-trunc-im-Set = pr1 (center unique-equiv-trunc-im-Set)

  equiv-trunc-im-Set : im (map-trunc-Set f) ≃ type-trunc-Set (im f)
  equiv-trunc-im-Set = pr1 equiv-slice-trunc-im-Set

  map-equiv-trunc-im-Set : im (map-trunc-Set f) → type-trunc-Set (im f)
  map-equiv-trunc-im-Set = map-equiv equiv-trunc-im-Set

  triangle-trunc-im-Set :
    ( inclusion-im (map-trunc-Set f)) ~
    ( inclusion-trunc-im-Set ∘ map-equiv-trunc-im-Set)
  triangle-trunc-im-Set = pr2 equiv-slice-trunc-im-Set

  htpy-hom-slice-trunc-im-Set :
    htpy-hom-slice
      ( map-trunc-Set f)
      ( inclusion-trunc-im-Set)
      ( comp-hom-slice
        ( map-trunc-Set f)
        ( inclusion-im (map-trunc-Set f))
        ( inclusion-trunc-im-Set)
        ( hom-equiv-slice
          ( inclusion-im (map-trunc-Set f))
          ( inclusion-trunc-im-Set)
          ( equiv-slice-trunc-im-Set))
        ( hom-slice-im (map-trunc-Set f)))
      ( hom-slice-trunc-im-Set)
  htpy-hom-slice-trunc-im-Set =
    pr2 (center unique-equiv-trunc-im-Set)

  htpy-map-hom-slice-trunc-im-Set :
    ( map-equiv-trunc-im-Set ∘ (map-unit-im (map-trunc-Set f))) ~
    ( map-hom-slice-trunc-im-Set)
  htpy-map-hom-slice-trunc-im-Set =
    pr1 htpy-hom-slice-trunc-im-Set

  tetrahedron-map-hom-slice-trunc-im-Set :
    ( ( triangle-trunc-im-Set ·r map-unit-im (map-trunc-Set f)) ∙h
      ( inclusion-trunc-im-Set ·l htpy-map-hom-slice-trunc-im-Set)) ~
    ( triangle-hom-slice-trunc-im-Set)
  tetrahedron-map-hom-slice-trunc-im-Set =
    pr2 htpy-hom-slice-trunc-im-Set

  unit-im-map-trunc-Set :
    im f → im (map-trunc-Set f)
  unit-im-map-trunc-Set x =
    pair
      ( unit-trunc-Set (pr1 x))
      ( apply-universal-property-trunc-Prop (pr2 x)
        ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set (pr1 x))))
        ( λ u →
          unit-trunc-Prop
            ( pair
              ( unit-trunc-Set (pr1 u))
              ( naturality-trunc-Set f (pr1 u) ∙ ap unit-trunc-Set (pr2 u)))))

  left-square-unit-im-map-trunc-Set :
    ( map-unit-im (map-trunc-Set f) ∘ unit-trunc-Set) ~
    ( unit-im-map-trunc-Set ∘ map-unit-im f)
  left-square-unit-im-map-trunc-Set a =
    eq-Eq-im
      ( map-trunc-Set f)
      ( map-unit-im (map-trunc-Set f) (unit-trunc-Set a))
      ( unit-im-map-trunc-Set (map-unit-im f a))
      ( naturality-trunc-Set f a)

  right-square-unit-im-map-trunc-Set :
    ( inclusion-im (map-trunc-Set f) ∘ unit-im-map-trunc-Set) ~
    ( unit-trunc-Set ∘ inclusion-im f)
  right-square-unit-im-map-trunc-Set x = refl
  
  is-set-truncation-im-map-trunc-Set :
    {l : Level} →
    is-set-truncation l
      ( im-Set (trunc-Set B) (map-trunc-Set f))
      ( unit-im-map-trunc-Set)
  is-set-truncation-im-map-trunc-Set =
    is-set-truncation-is-equiv-is-set-truncation
      ( im-Set (trunc-Set B) (map-trunc-Set f))
      ( unit-im-map-trunc-Set)
      ( trunc-Set (im f))
      ( unit-trunc-Set)
      ( λ b →
        is-injective-inclusion-trunc-im-Set
          ( ( inv (triangle-trunc-im-Set (unit-im-map-trunc-Set b))) ∙
            ( inv (naturality-trunc-Set (inclusion-im f) b))))
      ( is-set-truncation-trunc-Set (im f))
      ( is-equiv-map-equiv equiv-trunc-im-Set)

has-finite-components-Prop : {l : Level} → UU l → UU-Prop l
has-finite-components-Prop A = is-finite-Prop (type-trunc-Set A)

has-finite-components : {l : Level} → UU l → UU l
has-finite-components A = type-Prop (has-finite-components-Prop A)

has-cardinality-components-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
has-cardinality-components-Prop k A =
  has-cardinality-Prop (type-trunc-Set A) k

has-cardinality-components : {l : Level} (k : ℕ) → UU l → UU l
has-cardinality-components k A =
  type-Prop (has-cardinality-components-Prop k A)

has-set-presentation-Prop :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU l2) → UU-Prop (l1 ⊔ l2)
has-set-presentation-Prop A B =
  ∃-Prop (λ (f : type-Set A → B) → is-equiv (unit-trunc-Set ∘ f))

has-finite-presentation-Prop :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU-Prop l1
has-finite-presentation-Prop k A =
  has-set-presentation-Prop (Fin-Set k) A

has-finite-presentation :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU l1
has-finite-presentation k A = type-Prop (has-finite-presentation-Prop k A)
  
has-finite-presentation-has-cardinality-components :
  {l : Level} {k : ℕ} {A : UU l} → has-cardinality-components k A →
  has-finite-presentation k A
has-finite-presentation-has-cardinality-components {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-finite-presentation-Prop k A)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( P2 e)
        ( has-finite-presentation-Prop k A)
        ( λ g →
          unit-trunc-Prop
            ( pair
              ( λ x → pr1 (g x))
              ( is-equiv-htpy-equiv e (λ x → pr2 (g x))))))
  where
  P1 : (e : Fin k ≃ type-trunc-Set A) (x : Fin k) →
       type-trunc-Prop (fib unit-trunc-Set (map-equiv e x))
  P1 e x = is-surjective-unit-trunc-Set A (map-equiv e x)
  P2 : (e : Fin k ≃ type-trunc-Set A) →
       type-trunc-Prop ((x : Fin k) → fib unit-trunc-Set (map-equiv e x))
  P2 e = finite-choice-Fin (P1 e)

has-cardinality-components-has-finite-presentation :
  {l : Level} {k : ℕ} {A : UU l} → has-finite-presentation k A →
  has-cardinality-components k A
has-cardinality-components-has-finite-presentation {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-components-Prop k A)
    ( λ { (pair f E) → unit-trunc-Prop (pair (unit-trunc-Set ∘ f) E)})

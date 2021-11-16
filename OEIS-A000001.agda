{-# OPTIONS --without-K --exact-split #-}

module OEIS-A000001 where

open import 09-set-truncations

-- Homotopy finiteness

has-finite-connected-components-Prop : {l : Level} → UU l → UU-Prop l
has-finite-connected-components-Prop A =
  is-finite-Prop (type-trunc-Set A)

has-finite-connected-components : {l : Level} → UU l → UU l
has-finite-connected-components A =
  type-Prop (has-finite-connected-components-Prop A)

number-of-connected-components :
  {l : Level} {X : UU l} → has-finite-connected-components X → ℕ
number-of-connected-components H = number-of-elements-is-finite H

mere-equiv-number-of-connected-components :
  {l : Level} {X : UU l} (H : has-finite-connected-components X) →
  mere-equiv
    ( Fin (number-of-connected-components H))
    ( type-trunc-Set X)
mere-equiv-number-of-connected-components H =
  mere-equiv-is-finite H

is-homotopy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-homotopy-finite-Prop zero-ℕ X = has-finite-connected-components-Prop X
is-homotopy-finite-Prop (succ-ℕ k) X =
  prod-Prop ( is-homotopy-finite-Prop zero-ℕ X)
            ( Π-Prop X
              ( λ x → Π-Prop X (λ y → is-homotopy-finite-Prop k (Id x y))))

is-homotopy-finite : {l : Level} (k : ℕ) → UU l → UU l
is-homotopy-finite k X = type-Prop (is-homotopy-finite-Prop k X)

is-prop-is-homotopy-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-homotopy-finite k X)
is-prop-is-homotopy-finite k X =
  is-prop-type-Prop (is-homotopy-finite-Prop k X)

Homotopy-Finite : (l : Level) (k : ℕ) → UU (lsuc l)
Homotopy-Finite l k = Σ (UU l) (is-homotopy-finite k)

type-Homotopy-Finite :
  {l : Level} (k : ℕ) → Homotopy-Finite l k → UU l
type-Homotopy-Finite k = pr1

is-homotopy-finite-type-Homotopy-Finite :
  {l : Level} (k : ℕ) (A : Homotopy-Finite l k) →
  is-homotopy-finite k (type-Homotopy-Finite {l} k A)
is-homotopy-finite-type-Homotopy-Finite k = pr2

has-finite-connected-components-Σ-is-path-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-path-connected A → is-homotopy-finite one-ℕ A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ-is-path-connected {A = A} {B} C H K =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-path-connected C)
    ( is-homotopy-finite-Prop zero-ℕ (Σ A B))
    ( α)
    
  where
  α : A → is-homotopy-finite zero-ℕ (Σ A B)
  α a =
    is-finite-codomain-has-decidable-equality
      ( K a)
      ( is-surjective-map-trunc-Set
        ( fiber-inclusion B a)
        ( is-surjective-fiber-inclusion C a))
      ( apply-dependent-universal-property-trunc-Set
        ( λ x →
          set-Prop
            ( Π-Prop
              ( type-trunc-Set (Σ A B))
              ( λ y → is-decidable-Prop (Id-Prop (trunc-Set (Σ A B)) x y))))
        ( β))
        
    where
    β : (x : Σ A B) (v : type-trunc-Set (Σ A B)) →
        is-decidable (Id (unit-trunc-Set x) v)
    β (pair x y) =
      apply-dependent-universal-property-trunc-Set
        ( λ u →
          set-Prop
            ( is-decidable-Prop
              ( Id-Prop (trunc-Set (Σ A B)) (unit-trunc-Set (pair x y)) u)))
        ( γ)
        
      where
      γ : (v : Σ A B) →
          is-decidable (Id (unit-trunc-Set (pair x y)) (unit-trunc-Set v))
      γ (pair x' y') =
        is-decidable-equiv
          ( is-effective-unit-trunc-Set
            ( Σ A B)
            ( pair x y)
            ( pair x' y'))
          ( apply-universal-property-trunc-Prop
            ( mere-eq-is-path-connected C a x)
            ( is-decidable-Prop
              ( mere-eq-Prop (pair x y) (pair x' y')))
              ( δ))
              
        where
        δ : Id a x → is-decidable (mere-eq (pair x y) (pair x' y'))
        δ refl =
          apply-universal-property-trunc-Prop
            ( mere-eq-is-path-connected C a x')
            ( is-decidable-Prop
              ( mere-eq-Prop (pair a y) (pair x' y')))
            ( ε)
            
          where
          ε : Id a x' → is-decidable (mere-eq (pair x y) (pair x' y'))
          ε refl =
            is-decidable-equiv e
              ( is-decidable-type-trunc-Prop-is-finite
                ( is-finite-Σ
                  ( pr2 H a a)
                  ( λ ω → is-finite-is-decidable-Prop (P ω) (d ω))))
            
            where
            ℙ : is-contr
                ( Σ ( type-hom-Set (trunc-Set (Id a a)) (UU-Prop-Set _))
                    ( λ h →
                      ( λ a₁ → h (unit-trunc-Set a₁)) ~
                      ( λ ω₁ → trunc-Prop (Id (tr B ω₁ y) y'))))
            ℙ = universal-property-trunc-Set
                ( Id a a)
                ( UU-Prop-Set _)
                ( λ ω → trunc-Prop (Id (tr B ω y) y'))
            P : type-trunc-Set (Id a a) → UU-Prop _
            P = pr1 (center ℙ)
            compute-P :
              ( ω : Id a a) →
              type-Prop (P (unit-trunc-Set ω)) ≃
              type-trunc-Prop (Id (tr B ω y) y') 
            compute-P ω = equiv-eq (ap pr1 (pr2 (center ℙ) ω))
            d : (t : type-trunc-Set (Id a a)) → is-decidable (type-Prop (P t))
            d = apply-dependent-universal-property-trunc-Set
                ( λ t → set-Prop (is-decidable-Prop (P t)))
                ( λ ω →
                  is-decidable-equiv'
                    ( inv-equiv (compute-P ω))
                    ( is-decidable-equiv'
                      ( is-effective-unit-trunc-Set (B a) (tr B ω y) y')
                      ( has-decidable-equality-is-finite
                        ( K a)
                        ( unit-trunc-Set (tr B ω y))
                        ( unit-trunc-Set y'))))
            f : type-hom-Prop
                ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                ( mere-eq-Prop {A = Σ A B} (pair a y) (pair a y'))
            f t = apply-universal-property-trunc-Prop t
                    ( mere-eq-Prop (pair a y) (pair a y'))
                     λ { (pair u v) →
                         apply-dependent-universal-property-trunc-Set
                           ( λ u' →
                             hom-Set
                               ( set-Prop (P u'))
                               ( set-Prop
                                 ( mere-eq-Prop (pair a y) (pair a y'))))
                           ( λ ω v' →
                             apply-universal-property-trunc-Prop
                               ( map-equiv (compute-P ω) v')
                               ( mere-eq-Prop (pair a y) (pair a y'))
                               ( λ p → unit-trunc-Prop (eq-pair-Σ ω p)))
                           ( u)
                           ( v)}
            e : mere-eq {A = Σ A B} (pair a y) (pair a y') ≃
                type-trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P))
            e = equiv-iff
                  ( mere-eq-Prop (pair a y) (pair a y'))
                  ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                  ( λ t →
                    apply-universal-property-trunc-Prop t
                      ( trunc-Prop _)
                      ( ( λ { (pair ω r) →
                            unit-trunc-Prop
                              ( pair
                                ( unit-trunc-Set ω)
                                ( map-inv-equiv
                                  ( compute-P ω)
                                  ( unit-trunc-Prop r)))}) ∘
                        ( pair-eq-Σ)))
                  ( f)

is-coprod-codomain :
  {l1 l2 l3 : Level} {A1 : UU l1} {A2 : UU l2} {B : UU l3}
  (f : coprod A1 A2 → B) (e : coprod A1 A2 ≃ type-trunc-Set B)
  (H : (unit-trunc-Set ∘ f) ~ map-equiv e) →
  coprod (im (f ∘ inl)) (im (f ∘ inr)) ≃ B
is-coprod-codomain {B = B} f e H =
  pair α (is-equiv-is-emb-is-surjective is-surj-α is-emb-α)
  where
  α : coprod (im (f ∘ inl)) (im (f ∘ inr)) → B
  α = ind-coprod (λ x → B) pr1 pr1
  triangle-α : (α ∘ map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr))) ~ f
  triangle-α (inl a1) = refl
  triangle-α (inr a2) = refl
  is-emb-α : is-emb α
  is-emb-α =
    is-emb-coprod
      ( is-emb-pr1 (λ b → is-prop-type-trunc-Prop))
      ( is-emb-pr1 (λ b → is-prop-type-trunc-Prop))
      ( λ { (pair b1 u) (pair b2 v) →
          apply-universal-property-trunc-Prop u
            ( function-Prop _ empty-Prop)
            ( λ
              { (pair x refl) →
                apply-universal-property-trunc-Prop v
                  ( function-Prop _ empty-Prop)
                  ( λ
                    { (pair y refl) r →
                      map-compute-eq-coprod-inl-inr x y
                        ( is-injective-is-equiv
                          ( is-equiv-map-equiv e)
                          ( ( inv (H (inl x))) ∙
                            ( ( ap unit-trunc-Set r) ∙
                              ( H (inr y)))))})})})
  is-surj-α : is-surjective α
  is-surj-α b =
    apply-universal-property-trunc-Prop
      ( apply-effectiveness-unit-trunc-Set
        ( inv (issec-map-inv-equiv e (unit-trunc-Set b)) ∙ inv (H a)))
      ( trunc-Prop (fib α b))
      ( λ p →
        unit-trunc-Prop
          ( pair
            ( map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)) a)
            ( triangle-α a ∙ inv p)))
    where
    a = map-inv-equiv e (unit-trunc-Set b)

is-path-connected-unit : is-path-connected unit
is-path-connected-unit =
  is-contr-equiv' unit equiv-unit-trunc-unit-Set is-contr-unit

is-contr-im :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) {f : A → type-Set B}
  (a : A) (H : f ~ const A (type-Set B) (f a)) → is-contr (im f)
is-contr-im B {f} a H =
  pair
    ( map-unit-im f a)
    ( λ { (pair x u) →
      apply-dependent-universal-property-trunc-Prop
        ( λ v → Id-Prop (im-Set B f) (map-unit-im f a) (pair x v))
        ( u)
        ( λ { (pair a' refl) →
              eq-Eq-im f (map-unit-im f a) (map-unit-im f a') (inv (H a'))})})

is-path-connected-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-connected A → is-path-connected (im f)
is-path-connected-im {l1} {l2} {A} {B} f C =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-path-connected C)
    ( is-contr-Prop _)
    ( λ a →
      is-contr-equiv'
        ( im (map-trunc-Set f))
        ( equiv-trunc-im-Set f)
        ( is-contr-im
          ( trunc-Set B)
          ( unit-trunc-Set a)
          ( apply-dependent-universal-property-trunc-Set
            ( λ x →
              set-Prop
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f x)
                  ( map-trunc-Set f (unit-trunc-Set a))))
            ( λ a' →
              apply-universal-property-trunc-Prop
                ( mere-eq-is-path-connected C a' a)
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f (unit-trunc-Set a'))
                  ( map-trunc-Set f (unit-trunc-Set a)))
                ( λ {refl → refl})))))

is-path-connected-im-unit :
  {l1 : Level} {A : UU l1} (f : unit → A) → is-path-connected (im f)
is-path-connected-im-unit f =
  is-path-connected-im f is-path-connected-unit

is-homotopy-finite-empty : (k : ℕ) → is-homotopy-finite k empty
is-homotopy-finite-empty zero-ℕ =
  is-finite-equiv equiv-unit-trunc-empty-Set is-finite-empty
is-homotopy-finite-empty (succ-ℕ k) =
  pair (is-homotopy-finite-empty zero-ℕ) ind-empty

empty-Homotopy-Finite : (k : ℕ) → Homotopy-Finite lzero k
empty-Homotopy-Finite k = pair empty (is-homotopy-finite-empty k)

is-homotopy-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-homotopy-finite k A
is-homotopy-finite-is-empty zero-ℕ f =
  is-finite-is-empty (is-empty-trunc-Set f)
is-homotopy-finite-is-empty (succ-ℕ k) f =
  pair
    ( is-homotopy-finite-is-empty zero-ℕ f)
    ( λ a → ex-falso (f a))

is-homotopy-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-homotopy-finite k A
is-homotopy-finite-is-contr zero-ℕ H =
  is-finite-is-contr (is-contr-trunc-Set H)
is-homotopy-finite-is-contr (succ-ℕ k) H =
  pair
    ( is-homotopy-finite-is-contr zero-ℕ H)
    ( λ x y →
      is-homotopy-finite-is-contr k ( is-prop-is-contr H x y))

is-homotopy-finite-unit :
  (k : ℕ) → is-homotopy-finite k unit
is-homotopy-finite-unit k = is-homotopy-finite-is-contr k is-contr-unit

unit-Homotopy-Finite : (k : ℕ) → Homotopy-Finite lzero k
unit-Homotopy-Finite k = pair unit (is-homotopy-finite-unit k)

is-homotopy-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k B → is-homotopy-finite k A
is-homotopy-finite-equiv zero-ℕ e H =
  is-finite-equiv' (equiv-trunc-Set e) H
is-homotopy-finite-equiv (succ-ℕ k) e H =
  pair
    ( is-homotopy-finite-equiv zero-ℕ e (pr1 H))
    ( λ a b →
      is-homotopy-finite-equiv k
        ( equiv-ap e a b)
        ( pr2 H (map-equiv e a) (map-equiv e b)))

is-homotopy-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k A → is-homotopy-finite k B
is-homotopy-finite-equiv' k e = is-homotopy-finite-equiv k (inv-equiv e)

has-finite-connected-components-is-path-connected :
  {l : Level} {A : UU l} →
  is-path-connected A → has-finite-connected-components A
has-finite-connected-components-is-path-connected C =
  is-finite-is-contr C

is-homotopy-finite-coprod :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-homotopy-finite k A → is-homotopy-finite k B →
  is-homotopy-finite k (coprod A B)
is-homotopy-finite-coprod zero-ℕ H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-coprod-Set _ _)
    ( is-finite-coprod H K)
is-homotopy-finite-coprod (succ-ℕ k) H K =
  pair
    ( is-homotopy-finite-coprod zero-ℕ (pr1 H) (pr1 K))
    ( λ { (inl x) (inl y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inl-inl x y)
            ( pr2 H x y) ;
          (inl x) (inr y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inl-inr x y)
            ( is-homotopy-finite-empty k) ;
          (inr x) (inl y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inr-inl x y)
            ( is-homotopy-finite-empty k) ;
          (inr x) (inr y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inr-inr x y)
            ( pr2 K x y)})

coprod-Homotopy-Finite :
  {l1 l2 : Level} (k : ℕ) →
  Homotopy-Finite l1 k → Homotopy-Finite l2 k → Homotopy-Finite (l1 ⊔ l2) k
coprod-Homotopy-Finite k A B =
  pair
    ( coprod (type-Homotopy-Finite k A) (type-Homotopy-Finite k B))
    ( is-homotopy-finite-coprod k
      ( is-homotopy-finite-type-Homotopy-Finite k A)
      ( is-homotopy-finite-type-Homotopy-Finite k B))

is-homotopy-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite k A → is-homotopy-finite k (Maybe A)
is-homotopy-finite-Maybe k H =
  is-homotopy-finite-coprod k H (is-homotopy-finite-unit k)

is-homotopy-finite-Fin :
  (k n : ℕ) → is-homotopy-finite k (Fin n)
is-homotopy-finite-Fin k zero-ℕ =
  is-homotopy-finite-empty k
is-homotopy-finite-Fin k (succ-ℕ n) =
  is-homotopy-finite-Maybe k (is-homotopy-finite-Fin k n)

Fin-Homotopy-Finite : (k : ℕ) (n : ℕ) → Homotopy-Finite lzero k
Fin-Homotopy-Finite k n =
  pair (Fin n) (is-homotopy-finite-Fin k n)

is-homotopy-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-homotopy-finite k A
is-homotopy-finite-count k (pair n e) =
  is-homotopy-finite-equiv' k e (is-homotopy-finite-Fin k n)

is-homotopy-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-homotopy-finite k A
is-homotopy-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-homotopy-finite-Prop k A)
    ( is-homotopy-finite-count k)

is-homotopy-finite-UU-Fin :
  (k n : ℕ) → is-homotopy-finite k (UU-Fin n)
is-homotopy-finite-UU-Fin zero-ℕ n =
  has-finite-connected-components-is-path-connected
    ( is-path-connected-UU-Fin n)
is-homotopy-finite-UU-Fin (succ-ℕ k) n =
  pair
    ( is-homotopy-finite-UU-Fin zero-ℕ n)
    ( λ x y →
      is-homotopy-finite-equiv k
        ( equiv-equiv-eq-UU-Fin x y)
        ( is-homotopy-finite-is-finite k
          ( is-finite-≃
            ( is-finite-has-finite-cardinality (pair n (pr2 x)))
            ( is-finite-has-finite-cardinality (pair n (pr2 y))))))

is-homotopy-finite-UU-Fin-Level :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (UU-Fin-Level l n)
is-homotopy-finite-UU-Fin-Level {l} zero-ℕ n =
  has-finite-connected-components-is-path-connected
    ( is-path-connected-UU-Fin-Level n)
is-homotopy-finite-UU-Fin-Level {l} (succ-ℕ k) n =
  pair
    ( is-homotopy-finite-UU-Fin-Level zero-ℕ n)
    ( λ x y →
      is-homotopy-finite-equiv k
        ( equiv-equiv-eq-UU-Fin-Level x y)
        ( is-homotopy-finite-is-finite k
          ( is-finite-≃
            ( is-finite-has-finite-cardinality (pair n (pr2 x)))
            ( is-finite-has-finite-cardinality (pair n (pr2 y))))))

is-finite-has-finite-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finite-connected-components A → is-finite A
is-finite-has-finite-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (pair _ H))

has-finite-connected-components-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite k A → has-finite-connected-components A
has-finite-connected-components-is-homotopy-finite zero-ℕ H = H
has-finite-connected-components-is-homotopy-finite (succ-ℕ k) H = pr1 H

is-homotopy-finite-is-homotopy-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite (succ-ℕ k) A → is-homotopy-finite k A
is-homotopy-finite-is-homotopy-finite-succ-ℕ zero-ℕ H =
  has-finite-connected-components-is-homotopy-finite one-ℕ H
is-homotopy-finite-is-homotopy-finite-succ-ℕ (succ-ℕ k) H =
  pair
    ( has-finite-connected-components-is-homotopy-finite (succ-ℕ (succ-ℕ k)) H)
    ( λ x y → is-homotopy-finite-is-homotopy-finite-succ-ℕ k (pr2 H x y))

is-homotopy-finite-one-is-homotopy-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite (succ-ℕ k) A → is-homotopy-finite one-ℕ A
is-homotopy-finite-one-is-homotopy-finite-succ-ℕ zero-ℕ H = H
is-homotopy-finite-one-is-homotopy-finite-succ-ℕ (succ-ℕ k) H =
  is-homotopy-finite-one-is-homotopy-finite-succ-ℕ k
    ( is-homotopy-finite-is-homotopy-finite-succ-ℕ (succ-ℕ k) H)

is-finite-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-homotopy-finite k A → is-finite A
is-finite-is-homotopy-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (pair _ H))
    ( has-finite-connected-components-is-homotopy-finite k K)

has-finite-connected-components-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) → (Fin k ≃ (type-trunc-Set A)) →
  ((x y : A) → has-finite-connected-components (Id x y)) → 
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ' zero-ℕ e H K =
  is-homotopy-finite-is-empty zero-ℕ
    ( is-empty-is-empty-trunc-Set (map-inv-equiv e) ∘ pr1)
has-finite-connected-components-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e H K =
  apply-universal-property-trunc-Prop
    ( has-finite-presentation-has-cardinality-components (unit-trunc-Prop e))
    ( has-finite-connected-components-Prop (Σ A B))
    ( α)
  where
  α : Σ (Fin (succ-ℕ k) → A) (λ f → is-equiv (unit-trunc-Set ∘ f)) →
      has-finite-connected-components (Σ A B)
  α (pair f Eηf) =
    is-finite-equiv
      ( equiv-trunc-Set g)
      ( is-finite-equiv'
        ( equiv-distributive-trunc-coprod-Set
          ( Σ (im (f ∘ inl)) (B ∘ pr1))
          ( Σ (im (f ∘ inr)) (B ∘ pr1)))
        ( is-finite-coprod
          ( has-finite-connected-components-Σ' k
            ( h)
            ( λ x y →
              is-finite-equiv'
                ( equiv-trunc-Set
                  ( equiv-ap-emb
                    ( pair pr1
                      ( is-emb-pr1
                        ( λ u → is-prop-type-trunc-Prop)))))
                ( H (pr1 x) (pr1 y)))
            ( λ x → K (pr1 x)))
          ( has-finite-connected-components-Σ-is-path-connected
            ( is-path-connected-im (f ∘ inr) is-path-connected-unit)
            ( pair
              ( is-finite-is-contr
                ( is-path-connected-im (f ∘ inr) is-path-connected-unit))
              ( λ x y →
                is-homotopy-finite-equiv zero-ℕ
                  ( equiv-Eq-eq-im (f ∘ inr) x y)
                  ( H (pr1 x) (pr1 y))))
            ( λ x → K (pr1 x)))))
    where
    g : coprod (Σ (im (f ∘ inl)) (B ∘ pr1)) (Σ (im (f ∘ inr)) (B ∘ pr1)) ≃
        Σ A B
    g = ( equiv-Σ B
          ( is-coprod-codomain f
            ( pair (unit-trunc-Set ∘ f) Eηf)
            ( refl-htpy))
          ( λ { (inl x) → equiv-id ;
                (inr x) → equiv-id})) ∘e
        ( inv-equiv
          ( right-distributive-Σ-coprod
            ( im (f ∘ inl))
            ( im (f ∘ inr))
            ( ind-coprod (λ x → UU _) (B ∘ pr1) (B ∘ pr1))))
    i : Fin k → type-trunc-Set (im (f ∘ inl))
    i = unit-trunc-Set ∘ map-unit-im (f ∘ inl)
    is-surjective-i : is-surjective i
    is-surjective-i =
      is-surjective-comp'
        ( is-surjective-unit-trunc-Set _)
        ( is-surjective-map-unit-im (f ∘ inl))
    is-emb-i : is-emb i
    is-emb-i =
      is-emb-right-factor
        ( (unit-trunc-Set ∘ f) ∘ inl)
        ( inclusion-trunc-im-Set (f ∘ inl))
        ( i)
        ( ( inv-htpy (naturality-trunc-Set (inclusion-im (f ∘ inl)))) ·r
          ( map-unit-im (f ∘ inl)))
        ( is-emb-inclusion-trunc-im-Set (f ∘ inl))
        ( is-emb-comp'
          ( unit-trunc-Set ∘ f)
          ( inl)
          ( is-emb-is-equiv Eηf)
          ( is-emb-inl (Fin k) unit))
    h : Fin k ≃ type-trunc-Set (im (f ∘ inl))
    h = pair i (is-equiv-is-emb-is-surjective is-surjective-i is-emb-i)

has-finite-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-homotopy-finite one-ℕ A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ {l1} {l2} {A} {B} H K =
  apply-universal-property-trunc-Prop
    ( pr1 H)
    ( has-finite-connected-components-Prop (Σ A B))
    ( λ { (pair k e) →
          has-finite-connected-components-Σ' k e (λ x y → pr2 H x y) K})

is-homotopy-finite-Σ :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-homotopy-finite (succ-ℕ k) A → ((x : A) → is-homotopy-finite k (B x)) →
  is-homotopy-finite k (Σ A B)
is-homotopy-finite-Σ zero-ℕ {A} {B} H K = has-finite-connected-components-Σ H K
is-homotopy-finite-Σ (succ-ℕ k) H K =
  pair
    ( has-finite-connected-components-Σ
      ( is-homotopy-finite-one-is-homotopy-finite-succ-ℕ (succ-ℕ k) H)
      ( λ x →
        has-finite-connected-components-is-homotopy-finite (succ-ℕ k) (K x)))
    ( λ { (pair x u) (pair y v) →
          is-homotopy-finite-equiv k
            ( equiv-pair-eq-Σ (pair x u) (pair y v))
            ( is-homotopy-finite-Σ k
              ( pr2 H x y)
              ( λ { refl → pr2 (K x) u v}))})

Homotopy-Finite-Σ :
  {l1 l2 : Level} (k : ℕ) (A : Homotopy-Finite l1 (succ-ℕ k))
  (B : (x : type-Homotopy-Finite (succ-ℕ k) A) → Homotopy-Finite l2 k) →
  Homotopy-Finite (l1 ⊔ l2) k
Homotopy-Finite-Σ k A B =
  pair
    ( Σ ( type-Homotopy-Finite (succ-ℕ k) A)
        ( λ x → type-Homotopy-Finite k (B x)))
    ( is-homotopy-finite-Σ k
      ( is-homotopy-finite-type-Homotopy-Finite (succ-ℕ k) A)
      ( λ x → is-homotopy-finite-type-Homotopy-Finite k (B x)))

has-associative-mul : {l : Level} (X : UU l) → UU l
has-associative-mul X =
  Σ (X → X → X) (λ μ → (x y z : X) → Id (μ (μ x y) z) (μ x (μ y z)))

has-associative-mul-Set :
  {l : Level} (X : UU-Set l) → UU l
has-associative-mul-Set X =
  has-associative-mul (type-Set X)

Semi-Group :
  (l : Level) → UU (lsuc l)
Semi-Group l = Σ (UU-Set l) has-associative-mul-Set

set-Semi-Group :
  {l : Level} → Semi-Group l → UU-Set l
set-Semi-Group G = pr1 G

type-Semi-Group :
  {l : Level} → Semi-Group l → UU l
type-Semi-Group G = pr1 (set-Semi-Group G)

is-set-type-Semi-Group :
  {l : Level} (G : Semi-Group l) → is-set (type-Semi-Group G)
is-set-type-Semi-Group G = pr2 (set-Semi-Group G)

associative-mul-Semi-Group :
  {l : Level} (G : Semi-Group l) →
  has-associative-mul (type-Semi-Group G)
associative-mul-Semi-Group G = pr2 G

mul-Semi-Group :
  {l : Level} (G : Semi-Group l) →
  type-Semi-Group G →
    type-Semi-Group G → type-Semi-Group G
mul-Semi-Group G = pr1 (associative-mul-Semi-Group G)

is-associative-mul-Semi-Group :
  {l : Level} (G : Semi-Group l) (x y z : type-Semi-Group G) →
  Id ( mul-Semi-Group G (mul-Semi-Group G x y) z)
     ( mul-Semi-Group G x (mul-Semi-Group G y z))
is-associative-mul-Semi-Group G = pr2 (associative-mul-Semi-Group G)

is-unital :
  {l : Level} → Semi-Group l → UU l
is-unital G =
  Σ ( type-Semi-Group G)
    ( λ e →
      ( (y : type-Semi-Group G) → Id (mul-Semi-Group G e y) y) ×
      ( (x : type-Semi-Group G) → Id (mul-Semi-Group G x e) x))

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semi-Group l) is-unital

semi-group-Monoid :
  {l : Level} (M : Monoid l) → Semi-Group l
semi-group-Monoid M = pr1 M

type-Monoid :
  {l : Level} (M : Monoid l) → UU l
type-Monoid M = type-Semi-Group (semi-group-Monoid M)

is-set-type-Monoid :
  {l : Level} (M : Monoid l) → is-set (type-Monoid M)
is-set-type-Monoid M = is-set-type-Semi-Group (semi-group-Monoid M)

mul-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid M = mul-Semi-Group (semi-group-Monoid M)

is-associative-mul-Monoid :
  {l : Level} (M : Monoid l) (x y z : type-Monoid M) →
  Id (mul-Monoid M (mul-Monoid M x y) z) (mul-Monoid M x (mul-Monoid M y z))
is-associative-mul-Monoid M =
  is-associative-mul-Semi-Group (semi-group-Monoid M)

unit-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M
unit-Monoid M = pr1 (pr2 M)

left-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M (unit-Monoid M) x) x
left-unit-law-Monoid M = pr1 (pr2 (pr2 M))

right-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M x (unit-Monoid M)) x
right-unit-law-Monoid M = pr2 (pr2 (pr2 M))

all-elements-equal-is-unital :
  {l : Level} (G : Semi-Group l) → all-elements-equal (is-unital G)
all-elements-equal-is-unital (pair (pair X is-set-X) (pair μ assoc-μ))
  (pair e (pair left-unit-e right-unit-e))
  (pair e' (pair left-unit-e' right-unit-e')) =
  eq-subtype
    ( λ e → is-prop-prod
      ( is-prop-Π (λ y → is-set-X (μ e y) y))
      ( is-prop-Π (λ x → is-set-X (μ x e) x)))
    ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

is-prop-is-unital :
  {l : Level} (G : Semi-Group l) → is-prop (is-unital G)
is-prop-is-unital G =
  is-prop-all-elements-equal (all-elements-equal-is-unital G)

is-unital-Prop : {l : Level} (G : Semi-Group l) → UU-Prop l
is-unital-Prop G = pair (is-unital G) (is-prop-is-unital G)

is-invertible-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → UU l
is-invertible-Monoid M x =
  Σ ( type-Monoid M)
    ( λ y →
      Id (mul-Monoid M y x) (unit-Monoid M) ×
      Id (mul-Monoid M x y) (unit-Monoid M))

all-elements-equal-is-invertible-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  all-elements-equal (is-invertible-Monoid M x)
all-elements-equal-is-invertible-Monoid M x (pair y (pair p q)) (pair y' (pair p' q')) =
  eq-subtype
    ( ( λ z →
      is-prop-prod
        ( is-set-type-Monoid M (mul-Monoid M z x) (unit-Monoid M))
        ( is-set-type-Monoid M (mul-Monoid M x z) (unit-Monoid M))))
    ( ( inv (left-unit-law-Monoid M y)) ∙
      ( ( inv (ap (λ z → mul-Monoid M z y) p')) ∙
        ( ( is-associative-mul-Monoid M y' x y) ∙
          ( ( ap (mul-Monoid M y') q) ∙
            ( right-unit-law-Monoid M y')))))

is-prop-is-invertible-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  is-prop (is-invertible-Monoid M x)
is-prop-is-invertible-Monoid M x =
  is-prop-all-elements-equal (all-elements-equal-is-invertible-Monoid M x)

is-group' :
  {l : Level} (G : Semi-Group l) → is-unital G → UU l
is-group' G is-unital-G =
  Σ ( type-Semi-Group G → type-Semi-Group G)
    ( λ i →
      ( (x : type-Semi-Group G) →
        Id (mul-Semi-Group G (i x) x) (pr1 is-unital-G)) ×
      ( (x : type-Semi-Group G) →
        Id (mul-Semi-Group G x (i x)) (pr1 is-unital-G)))

is-group :
  {l : Level} (G : Semi-Group l) → UU l
is-group G =
  Σ (is-unital G) (is-group' G)

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semi-Group l) is-group

module _
  {l : Level} (G : Group l)
  where
  
  semi-group-Group : Semi-Group l
  semi-group-Group = pr1 G
  
  set-Group : UU-Set l
  set-Group = pr1 semi-group-Group
  
  type-Group : UU l
  type-Group = pr1 set-Group
  
  is-set-type-Group : is-set type-Group
  is-set-type-Group = pr2 set-Group
  
  associative-mul-Group : has-associative-mul type-Group
  associative-mul-Group = pr2 semi-group-Group
  
  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 associative-mul-Group
  
  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x
  
  is-associative-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  is-associative-mul-Group = pr2 associative-mul-Group
    
  is-group-Group : is-group semi-group-Group
  is-group-Group = pr2 G
  
  is-unital-Group : is-unital semi-group-Group
  is-unital-Group = pr1 is-group-Group
  
  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group
  
  left-unit-law-Group :
    (x : type-Group) → Id (mul-Group unit-Group x) x
  left-unit-law-Group = pr1 (pr2 is-unital-Group)
  
  right-unit-law-Group :
    (x : type-Group) → Id (mul-Group x unit-Group) x
  right-unit-law-Group = pr2 (pr2 is-unital-Group)
  
  has-inverses-Group : is-group' semi-group-Group is-unital-Group
  has-inverses-Group = pr2 is-group-Group
  
  inv-Group : type-Group → type-Group
  inv-Group = pr1 has-inverses-Group
  
  left-inverse-law-Group :
    (x : type-Group) → Id (mul-Group (inv-Group x) x) unit-Group
  left-inverse-law-Group = pr1 (pr2 has-inverses-Group)
  
  right-inverse-law-Group :
    (x : type-Group) → Id (mul-Group x (inv-Group x)) unit-Group
  right-inverse-law-Group = pr2 (pr2 has-inverses-Group)
  
  is-equiv-mul-Group : (x : type-Group) → is-equiv (mul-Group x)
  is-equiv-mul-Group x =
    is-equiv-has-inverse
      ( mul-Group (inv-Group x))
      ( λ y →
        ( inv (is-associative-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (right-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
      ( λ y →
        ( inv (is-associative-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (left-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
  
  equiv-mul-Group : (x : type-Group) → type-Group ≃ type-Group
  equiv-mul-Group x = pair (mul-Group x) (is-equiv-mul-Group x)
  
  is-equiv-mul-Group' : (x : type-Group) → is-equiv (mul-Group' x)
  is-equiv-mul-Group' x =
    is-equiv-has-inverse
    ( mul-Group' (inv-Group x))
      ( λ y →
        ( is-associative-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (left-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
      ( λ y →
        ( is-associative-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (right-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
  
  equiv-mul-Group' : (x : type-Group) → type-Group ≃ type-Group
  equiv-mul-Group' x = pair (mul-Group' x) (is-equiv-mul-Group' x)

all-elements-equal-is-group :
  {l : Level} (G : Semi-Group l) (e : is-unital G) →
  all-elements-equal (is-group' G e)
all-elements-equal-is-group
  ( pair (pair G is-set-G) (pair μ assoc-G))
  ( pair e (pair left-unit-G right-unit-G))
  ( pair i (pair left-inv-i right-inv-i))
  ( pair i' (pair left-inv-i' right-inv-i')) =
  eq-subtype
    ( λ i →
      is-prop-prod
        ( is-prop-Π (λ x → is-set-G (μ (i x) x) e))
        ( is-prop-Π (λ x → is-set-G (μ x (i x)) e)))
    ( eq-htpy
      ( λ x →                                             -- ix
        ( inv (left-unit-G (i x))) ∙                      -- = 1·(ix)
        ( ( ap (λ y → μ y (i x)) (inv (left-inv-i' x))) ∙ -- = (i'x·x)·(ix)
          ( ( assoc-G (i' x) x (i x)) ∙                   -- = (i'x)·(x·ix)
            ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
              ( right-unit-G (i' x)))))))                 -- = i'x

is-prop-is-group :
  {l : Level} (G : Semi-Group l) → is-prop (is-group G)
is-prop-is-group G =
  is-prop-Σ
    ( is-prop-is-unital G)
    ( λ e →
      is-prop-all-elements-equal (all-elements-equal-is-group G e))

is-group-Prop : {l : Level} (G : Semi-Group l) → UU-Prop l
is-group-Prop G = pair (is-group G) (is-prop-is-group G)

Semi-Group-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Semi-Group-of-Order' l n =
  Σ (UU-Fin-Level l n) (λ X → has-associative-mul (type-UU-Fin-Level X))

Semi-Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Semi-Group-of-Order l n =
  Σ (Semi-Group l) (λ G → mere-equiv (Fin n) (type-Semi-Group G))

is-finite-has-associative-mul :
  {l : Level} {X : UU l} → is-finite X → is-finite (has-associative-mul X)
is-finite-has-associative-mul H =
  is-finite-Σ
    ( is-finite-function-type H (is-finite-function-type H H))
    ( λ μ →
      is-finite-Π H
        ( λ x →
          is-finite-Π H
            ( λ y →
              is-finite-Π H
                ( λ z →
                  is-finite-eq (has-decidable-equality-is-finite H)))))

is-homotopy-finite-Semi-Group-of-Order' :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (Semi-Group-of-Order' l n)
is-homotopy-finite-Semi-Group-of-Order' k n =
  is-homotopy-finite-Σ k
    ( is-homotopy-finite-UU-Fin-Level (succ-ℕ k) n)
    ( λ x →
      is-homotopy-finite-is-finite k
        ( is-finite-has-associative-mul
          ( is-finite-type-UU-Fin-Level x)))

is-homotopy-finite-Semi-Group-of-Order :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (Semi-Group-of-Order l n)
is-homotopy-finite-Semi-Group-of-Order {l} k n =
  is-homotopy-finite-equiv k e
    ( is-homotopy-finite-Semi-Group-of-Order' k n)
  where
  e : Semi-Group-of-Order l n ≃ Semi-Group-of-Order' l n
  e = ( equiv-Σ
        ( has-associative-mul ∘ type-UU-Fin-Level)
        ( ( right-unit-law-Σ-is-contr
            ( λ X →
              is-proof-irrelevant-is-prop
                ( is-prop-is-set _)
                ( is-set-is-finite
                  ( is-finite-has-cardinality (pr2 X))))) ∘e
          ( equiv-right-swap-Σ))
        ( λ X → equiv-id)) ∘e
      ( equiv-right-swap-Σ
        { A = UU-Set l}
        { B = has-associative-mul-Set}
        { C = mere-equiv (Fin n) ∘ type-Set})

number-of-semi-groups-of-order : ℕ → ℕ
number-of-semi-groups-of-order n =
  number-of-connected-components
    ( is-homotopy-finite-Semi-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-semi-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-semi-groups-of-order n))
    ( type-trunc-Set (Semi-Group-of-Order lzero n))
mere-equiv-number-of-semi-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-homotopy-finite-Semi-Group-of-Order {lzero} zero-ℕ n)

Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order l n = Σ (Group l) (λ M → mere-equiv (Fin n) (type-Group M))

is-finite-is-group :
  {l : Level} {n : ℕ} (G : Semi-Group-of-Order l n) →
  is-finite {l} (is-group (pr1 G))
is-finite-is-group {l} {n} G =
  apply-universal-property-trunc-Prop
    ( pr2 G)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-group-Prop (pr1 G))
        ( is-decidable-Σ-count
          ( count-Σ
            ( pair n e)
            ( λ u →
              count-prod
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semi-Group (pr1 G) u x)
                      ( x)))
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semi-Group (pr1 G) x u)
                      ( x)))))
          ( λ u →
            is-decidable-Σ-count
              ( count-function-type (pair n e) (pair n e))
              ( λ i →
                is-decidable-prod
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semi-Group (pr1 G) (i x) x)
                        ( pr1 u)))
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semi-Group (pr1 G) x (i x))
                        ( pr1 u)))))))

is-homotopy-finite-Group-of-Order :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (Group-of-Order l n)
is-homotopy-finite-Group-of-Order {l} k n =
  is-homotopy-finite-equiv k e
    ( is-homotopy-finite-Σ k
      ( is-homotopy-finite-Semi-Group-of-Order (succ-ℕ k) n)
      ( λ X →
        is-homotopy-finite-is-finite k
          ( is-finite-is-group X)))
  where
  e : Group-of-Order l n ≃
      Σ (Semi-Group-of-Order l n) (λ X → is-group (pr1 X))
  e = equiv-right-swap-Σ

number-of-groups-of-order : ℕ → ℕ
number-of-groups-of-order n =
  number-of-connected-components
    ( is-homotopy-finite-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-groups-of-order n))
    ( type-trunc-Set (Group-of-Order lzero n))
mere-equiv-number-of-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-homotopy-finite-Group-of-Order {lzero} zero-ℕ n)

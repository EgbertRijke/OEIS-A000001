{-

This module converts between the path types and the inductively
defined equality types.

-}
{-# OPTIONS --cubical --safe #-}

module Id where

open import Cubical.Foundations.Prelude
  hiding ( _≡_ ; _≡⟨_⟩_ ; _∎ ; isPropIsContr)
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; subst     to substPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath )
open import Cubical.Foundations.Equiv
  renaming ( fiber     to fiberPath
           ; isEquiv   to isEquivPath
           ; _≃_       to EquivPath
           ; equivFun  to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath )
  hiding   ( equivCtr
           ; equivIsEquiv )
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence hiding (univalence)
open import Cubical.HITs.PropositionalTruncation
  renaming ( squash to squashPath
           ; rec to recPropTruncPath
           ; elim to elimPropTruncPath )
open import Cubical.HITs.SetTruncation.Base

-- Import the builtin equality type defined as an inductive family
open import Agda.Builtin.Equality

private
 variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : Type ℓ'

ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

transport : ∀ (C : A → Type ℓ') {x y : A} → x ≡ y → C x → C y
transport C refl b = b

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

apd : {C : A → Type ℓ} (f : (x : A) → C x) {x y : A} (p : x ≡ y) → transport C p (f x) ≡ f y
apd f refl = refl

congPathd : {C : A → Type ℓ} (f : (x : A) → C x) {x y : A} (p : Path A x y) → Path (C y) (substPath C p (f x)) (f y)
congPathd f p = fromPathP (congPath f p)

-- Equality between Path and equality
eqToPath : {x y : A} → x ≡ y → Path A x y
eqToPath refl = reflPath

pathToEq : {x y : A} → Path A x y → x ≡ y
pathToEq {x = x} = JPath (λ y _ → x ≡ y) refl

eqToPath-pathToEq : {x y : A} → (p : Path A x y) → Path _ (eqToPath (pathToEq p)) p
eqToPath-pathToEq p =
  JPath (λ _ h → Path _ (eqToPath (pathToEq h)) h)
        (congPath eqToPath (transportRefl refl)) p

pathToEq-eqToPath : {x y : A} → (p : x ≡ y) → Path _ (pathToEq (eqToPath p)) p
pathToEq-eqToPath refl = transportRefl refl

PathIsoEq : {x y : A} → Iso (Path A x y) (x ≡ y)
PathIsoEq = iso pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq

PathPathEq : {x y : A} → Path _ (Path A x y) (x ≡ y)
PathPathEq = isoToPath PathIsoEq

Path≡Eq : {x y : A} → (Path A x y) ≡ (x ≡ y)
Path≡Eq = pathToEq PathPathEq

pathToEq≡eqToPath : {x y : A} → (p : x ≡ y) → pathToEq (eqToPath p) ≡ p
pathToEq≡eqToPath p = transportPath PathPathEq (pathToEq-eqToPath p)

-- We get funext by going back and forth between Path and Eq
funExt : {B : A → Type ℓ} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExt p = pathToEq (λ i x → eqToPath (p x) i)

-- Some lemmas relating the definitions for Path and ≡
substPath≡transport' : (C : A → Type ℓ) {x y : A} (b : C x) (p : x ≡ y) → substPath C (eqToPath p) b ≡ transport C p b
substPath≡transport' C b refl = pathToEq (transportRefl b)

substPath≡transport : (C : A → Type ℓ) {x y : A} (b : C x) (p : Path _ x y) → substPath C p b ≡ transport C (pathToEq p) b
substPath≡transport C b p = ap (λ x → substPath C x b) (pathToEq (symPath (eqToPath-pathToEq p)))
                          ∙ substPath≡transport' C b (pathToEq p)


congPath≡ap : {x y : A} → (f : A → B) (p : x ≡ y) → congPath f (eqToPath p) ≡ eqToPath (ap f p)
congPath≡ap f refl = refl

ap≡congPath : {x y : A} → (f : A → B) (p : Path A x y) → ap f (pathToEq p) ≡ pathToEq (congPath f p)
ap≡congPath {x = x} f p = JPath (λ _ q → ap f (pathToEq q) ≡ pathToEq (congPath f q)) rem p
  where
  rem : ap f (transp (λ i → x ≡ x) i0 refl) ≡ transp (λ i → f x ≡ f x) i0 refl
  rem = pathToEq (compPath (λ i → ap f (transportRefl refl i)) (symPath (transportRefl refl)))

-- Equivalences expressed using ≡ everywhere
fiber : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

record isEquiv {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    equiv-proof : (y : B) → isContr (fiber f y)

open isEquiv

infix 4 _≃_

_≃_ : ∀ (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

equivFun : A ≃ B → A → B
equivFun e = e .fst

equivIsEquiv : (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = e .snd

equivCtr : (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst


-- Functions for going between the various definitions. This could
-- also be achieved by making lines in the universe and transporting
-- back and forth along them.

fiberPathToFiber : {f : A → B} {y : B} → fiberPath f y → fiber f y
fiberPathToFiber (x , p) = (x , pathToEq p)

fiberToFiberPath : {f : A → B} {y : B} → fiber f y → fiberPath f y
fiberToFiberPath (x , p) = (x , eqToPath p)

fiberToFiber : {f : A → B} {y : B} (p : fiber f y) → Path _ (fiberPathToFiber (fiberToFiberPath p)) p
fiberToFiber (x , p) i = x , pathToEq-eqToPath p i

fiberPathToFiberPath : {f : A → B} {y : B} (p : fiberPath f y) → Path _ (fiberToFiberPath (fiberPathToFiber p)) p
fiberPathToFiberPath (x , p) i = x , eqToPath-pathToEq p i

isContrPathToIsContr : isContrPath A → isContr A
isContrPathToIsContr (ctr , p) = (ctr , λ y → pathToEq (p y))

isContrToIsContrPath : isContr A → isContrPath A
isContrToIsContrPath (ctr , p) = (ctr , λ y → eqToPath (p y))

isPropPathToIsProp : isPropPath A → isProp A
isPropPathToIsProp H x y = pathToEq (H x y)

isPropToIsPropPath : isProp A → isPropPath A
isPropToIsPropPath H x y = eqToPath (H x y)

-- Specialized helper lemmas for going back and forth between
-- isContrPath and isContr:

helper1 : {A B : Type ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (f (g y)) y)
        → isContrPath A → isContr B
helper1 f g h (x , p) =
  (f x , λ y → pathToEq (λ i → hcomp (λ j → λ { (i = i0) → f x
                                              ; (i = i1) → h y j })
                                     (f (p (g y) i))))

helper2 : {A B : Type ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (g (f y)) y)
        → isContr B → isContrPath A
helper2 {A = A} f g h (x , p) = (g x , λ y → eqToPath (ap g (p (f y)) ∙ pathToEq (h y)))

-- This proof is essentially the one for proving that isContr with
-- Path is a proposition, but as we are working with ≡ we have to
-- insert a lof of conversion functions.
-- TODO: prove this directly following the HoTT proof?
isPropIsContr : (p1 p2 : isContr A) → Path (isContr A) p1 p2
isPropIsContr (a0 , p0) (a1 , p1) j =
  ( eqToPath (p0 a1) j ,
    hcomp (λ i → λ { (j = i0) →  λ x → pathToEq-eqToPath (p0 x) i
                   ; (j = i1) →  λ x → pathToEq-eqToPath (p1 x) i })
          (λ x → pathToEq (λ i → hcomp (λ k → λ { (i = i0) → eqToPath (p0 a1) j
                                                ; (i = i1) → eqToPath (p0 x) (j ∨ k)
                                                ; (j = i0) → eqToPath (p0 x) (i ∧ k)
                                                ; (j = i1) → eqToPath (p1 x) i })
                                       (eqToPath (p0 (eqToPath (p1 x) i)) j))))

-- We now prove that isEquiv is a proposition
isPropIsEquiv : {A B : Type ℓ} {f : A → B} (h1 h2 : isEquiv f) → Path _ h1 h2
equiv-proof (isPropIsEquiv h1 h2 i) y = isPropIsContr (h1 .equiv-proof y) (h2 .equiv-proof y) i

equivToEquivPath : A ≃ B → EquivPath A B
equivToEquivPath (f , p) =
  (f , λ { .equiv-proof y → helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y) })

-- Go from a Path equivalence to an ≡ equivalence
equivPathToEquiv : EquivPath A B → A ≃ B
equivPathToEquiv (f , p) =
  (f , λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber (p .equiv-proof y) })

equivToEquiv : {A B : Type ℓ} (p : A ≃ B) → Path _ (equivPathToEquiv (equivToEquivPath p)) p
equivToEquiv (f , p) i =
  (f , isPropIsEquiv (λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber
                                             (helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y)) }) p i)

equivPathToEquivPath : {A B : Type ℓ} (p : EquivPath A B) → Path _ (equivToEquivPath (equivPathToEquiv p)) p
equivPathToEquivPath (f , p) i =
  ( f , isPropIsEquivPath f (equivToEquivPath (equivPathToEquiv (f , p)) .snd) p i )

equivPath≡Equiv : {A B : Type ℓ} → Path _ (EquivPath A B) (A ≃ B)
equivPath≡Equiv {ℓ} = isoToPath (iso (equivPathToEquiv {ℓ}) equivToEquivPath equivToEquiv equivPathToEquivPath)

path≡Eq : {A B : Type ℓ} → Path _ (Path _ A B) (A ≡ B)
path≡Eq = isoToPath (iso pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq)

-- Univalence formulated using ≡ everywhere
univalenceEq : (A ≡ B) ≃ (A ≃ B)
univalenceEq {A = A} {B = B} = equivPathToEquiv rem
  where
  rem0 : Path _ (Lift (EquivPath A B)) (Lift (A ≃ B))
  rem0 = congPath Lift equivPath≡Equiv

  rem1 : Path _ (A ≡ B) (Lift (A ≃ B))
  rem1 i = hcomp (λ j → λ { (i = i0) → path≡Eq {A = A} {B = B} j
                          ; (i = i1) → rem0 j })
                 (univalencePath {A = A} {B = B} i)

  rem : EquivPath (A ≡ B) (A ≃ B)
  rem = compEquiv (eqweqmap rem1) (invEquiv LiftEquiv)


-- Propositional truncation using ≡ with paths under the hood

∥∥-isProp : ∀ (x y : ∥ A ∥) → x ≡ y
∥∥-isProp x y = pathToEq (squashPath x y)

∥∥-recursion : ∀ {A : Type ℓ} {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥ → P
∥∥-recursion Pprop = recPropTruncPath (isPropToIsPropPath Pprop)

∥∥-induction : ∀ {A : Type ℓ'} {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
                ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
∥∥-induction Pprop = elimPropTruncPath (λ a → isPropToIsPropPath (Pprop a))



module EgbertPostulates where

  -- postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

  -- Not exactly the same formulation... Do we really need the other form?
  funext : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funext p = funExt p

  -- postulate type-trunc-Prop : {l : Level} → UU l → UU l
  type-trunc-Prop : {l : Level} → Type l → Type l
  type-trunc-Prop = ∥_∥

  -- postulate unit-trunc-Prop : {l : Level} {A : UU l} → A → type-trunc-Prop A
  unit-trunc-Prop : {l : Level} {A : Type l} → A → type-trunc-Prop A
  unit-trunc-Prop = ∣_∣

  -- postulate
  --   all-elements-equal-type-trunc-Prop :
  --     {l : Level} {A : UU l} → all-elements-equal (type-trunc-Prop A)
  all-elements-equal-type-trunc-Prop : {l : Level} {A : Type l} → (x y : type-trunc-Prop A) → x ≡ y
  all-elements-equal-type-trunc-Prop = ∥∥-isProp

  -- postulate
  --   ind-trunc-Prop' :
  --     {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU l)
  --     (f : (x : A) → P (unit-trunc-Prop x))
  --     (g : (x y : type-trunc-Prop A) (u : P x) (v : P y) →
  --          Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
  --     (x : type-trunc-Prop A) → P x

  -- This is a bit annoying to prove. Do we really need this form?
  ind-trunc-Prop' :
      {l l1 : Level} {A : Type l1} (P : type-trunc-Prop A → Type l)
      (f : (x : A) → P (unit-trunc-Prop x))
      (g : (x y : type-trunc-Prop A) (u : P x) (v : P y)
         → transport P (all-elements-equal-type-trunc-Prop x y) u ≡ v)
    → (x : type-trunc-Prop A) → P x
  ind-trunc-Prop' P f g x = ∥∥-induction {P = P} (λ a p q → {!!} ∙ g a a p q) f x

  -- postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B
  univalence : {i : Level} → (A B : Type i) → (A ≡ B) ≃ (A ≃ B)
  univalence A B = univalenceEq {A = A} {B = B}

  -- postulate type-trunc-Set : {l : Level} → UU l → UU l
  type-trunc-Set : {l : Level} → Type l → Type l
  type-trunc-Set = ∥_∥₂

  -- postulate
  --   is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)
  is-set-type-trunc-Set : {l : Level} {A : Type l} → (x y : type-trunc-Set A) → (p q : x ≡ y) → p ≡ q
  is-set-type-trunc-Set x y p q = sym (pathToEq≡eqToPath p)
                                ∙ (ap pathToEq (pathToEq (squash₂ x y (eqToPath p) (eqToPath q)))
                                ∙ pathToEq≡eqToPath q)

  -- postulate unit-trunc-Set : {l : Level} {A : UU l} → A → type-Set (trunc-Set A)
  -- unit-trunc-Set : {l : Level} {A : Type l} → A → type-Set (trunc-Set A)
  -- unit-trunc-Set = ?  -- TODO

  -- TODO
  -- postulate
  --   is-set-truncation-trunc-Set :
  --     {l1 l2 : Level} (A : UU l1) →
  --     is-set-truncation l2 (trunc-Set A) unit-trunc-Set

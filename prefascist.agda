{-# OPTIONS --prop --local-rewriting --rewriting #-}

module prefascist where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Sigma
  renaming (fst to ₁; snd to ₂)

record ⊤ {a} : Set a where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}

record ⊤ᵖ {a} : Prop a where
  instance constructor ttᵖ

record ∃ {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,ᵖ_
  field
    fstᵖ : A
    sndᵖ : B fstᵖ
open ∃ public
  renaming (fstᵖ to ₁; sndᵖ to ₂)

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Prop a where       -- prop-valued equality.
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE  _≡_ #-}

postulate
  coe :
    ∀ {a b} {A : Set a} (P : A → Set b) {x y : A} →
    x ≡ y → P x → P y                                      -- transports Set-valued data along the Prop-valued equality.

  coe-refl :
    ∀ {a b} {A : Set a} (P : A → Set b) {x : A} (u : P x) →
    coe P refl u ≡ u                                       -- a computational rule for coe.

{-# REWRITE coe-refl #-}

coeᵖ :
  ∀ {a b} {A : Set a} (P : A → Prop b) {x y : A} →
  x ≡ y → P x → P y
coeᵖ P refl p = p                                          -- coe's propositional counterpart.

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

postulate
  funext :
    ∀ {a b} {A : Set a} {B : A → Set b}
      {f g : (x : A) → B x} →
      ((x : A) → f x ≡ g x) →
      f ≡ g

cong :
  ∀ {a b} {A : Set a} {B : Set b}
    (h : A → B) {x y : A} →
  x ≡ y → h x ≡ h y
cong h refl = refl

funextᵢ :
  ∀ {a b} {A : Set a} {B : A → Set b}
    {f g : ∀ {x : A} → B x} →
  ((x : A) → f {x} ≡ g {x}) →
  (λ {x} → f {x}) ≡ (λ {x} → g {x})
funextᵢ p = cong (λ k → λ {x} → k x) (funext p)             -- counterpart of funext for functions with implicit arguments.

-------------------------------------------------------------------------------------------------------------------------

module CwF
-- Base category 
  (Obj  : Set)
  (Hom  : Obj → Obj → Set)
  (id   : ∀ {x} → Hom x x)
  (comp : ∀ {x y z} → Hom y z → Hom x y → Hom x z)

  (@rewrite id-left :
    ∀ {x y} (f : Hom x y) → comp id f ≡ f)

  (@rewrite id-right :
    ∀ {x y} (f : Hom x y) → comp f id ≡ f)

  (@rewrite assoc :
    ∀ {w x y z}
      (h₁ : Hom y z) (g : Hom x y) (f : Hom w x) →
      comp (comp h₁ g) f ≡ comp h₁ (comp g f))
  where

  infixr 40 _∘_

  _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
  _∘_ = comp

  ----------------------------------------------------------------------
  -- Cofree presheaves

  □ : (Obj → Set) → Obj → Set 
  □ P = λ x → ∀ {y} → Hom y x → P y

  infixl 50 _[_]□

  _[_]□ : ∀ {P : Obj → Set} {x y} → □ P x → Hom y x → □ P y
  (s [ f ]□) g = s (f ∘ g)

  ----------------------------------------------------------------------
  -- Contexts and decoded elements

  record Con : Set₁  where
    field
      Γ₀ : Obj → Set
      Γ₁ : ∀ {x} → □ Γ₀ x → Prop

  open Con public
    renaming (Γ₀ to ₀; Γ₁ to ₁)

  record El (Γ : Con) (x : Obj) : Set  where
    constructor el
    field
      run : □ (Γ .₀) x
      sat : ∀ {y} (f : Hom y x) → Γ .₁ (run [ f ]□)

  open El public

  infixl 50 _[_]E

  _[_]E : ∀ {Γ : Con} {x y} → El Γ x → Hom y x → El Γ y
  run (γ [ f ]E) g = run γ (f ∘ g)
  sat (γ [ f ]E) g = sat γ (f ∘ g)

  E-id : ∀ {Γ : Con} {x} (γ : El Γ x) → γ [ id ]E ≡ γ
  E-id γ = refl

  E-comp : ∀ {Γ : Con} {x y z}
             (γ : El Γ x) (f : Hom y x) (g : Hom z y) →
             (γ [ f ]E) [ g ]E ≡ γ [ f ∘ g ]E
  E-comp γ f g = refl

  ----------------------------------------------------------------------
  -- Substitutions

  record Sub (Γ Δ : Con) : Set where
    field
      map₀ : ∀ {x} → El Γ x → Δ .₀ x
      map₁ : ∀ {x} (γ : El Γ x) →
             Δ .₁ λ {y} (f : Hom y x) → map₀ (γ [ f ]E)

  open Sub public
    renaming (map₀ to ₀; map₁ to ₁)

  ElS : ∀ {Δ Γ : Con} → Sub Δ Γ → ∀ {x} → El Δ x → El Γ x
  run (ElS σ δ) f = σ .₀ (δ [ f ]E)
  sat (ElS σ δ) f = σ .₁ (δ [ f ]E)

  ElS-natural : ∀ {Δ Γ : Con} {x y}
                  (σ : Sub Δ Γ) (δ : El Δ x) (f : Hom y x) →
                  ElS σ δ [ f ]E ≡ ElS σ (δ [ f ]E)
  ElS-natural σ δ f = refl

  idS : ∀ {Γ : Con} → Sub Γ Γ
  ₀ idS γ = run γ id
  ₁ idS γ = sat γ id

  infixr 35 _∘S_

  _∘S_ : ∀ {Θ Δ Γ : Con} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  (σ ∘S τ) .₀ θ = σ .₀ (ElS τ θ)
  (σ ∘S τ) .₁ θ = σ .₁ (ElS τ θ)

  ElS-id : ∀ {Γ : Con} {x} (γ : El Γ x) → ElS idS γ ≡ γ
  ElS-id γ = refl

  ElS-comp : ∀ {Θ Δ Γ : Con} {x}
               (σ : Sub Δ Γ) (τ : Sub Θ Δ) (θ : El Θ x) →
               ElS (σ ∘S τ) θ ≡ ElS σ (ElS τ θ)
  ElS-comp σ τ θ = refl

  Sub-id-left : ∀ {Δ Γ : Con} (σ : Sub Δ Γ) → idS ∘S σ ≡ σ
  Sub-id-left σ = refl

  Sub-id-right : ∀ {Δ Γ : Con} (σ : Sub Δ Γ) → σ ∘S idS ≡ σ
  Sub-id-right σ = refl

  Sub-assoc : ∀ {Ξ Θ Δ Γ : Con}
                (σ : Sub Δ Γ) (τ : Sub Θ Δ) (υ : Sub Ξ Θ) →
                (σ ∘S τ) ∘S υ ≡ σ ∘S (τ ∘S υ)
  Sub-assoc σ τ υ = refl
  
  ----------------------------------------------------------------------
  -- Types and dependent elements

  record Ty (Γ : Con) : Set₁ where
    field
      A₀ : ∀ {x} → El Γ x → Set
      A₁ : ∀ {x} (γ : El Γ x) →
                (∀ {y} (f : Hom y x) → A₀ (γ [ f ]E)) → Prop

  open Ty public
    renaming (A₀ to ₀; A₁ to ₁)

  record ElT {Γ : Con} (A : Ty Γ) {x : Obj} (γ : El Γ x) : Set where
    constructor elt
    field
      runT : ∀ {y} (f : Hom y x) → A .₀ (γ [ f ]E)
      satT : ∀ {y} (f : Hom y x) →
             A .₁ (γ [ f ]E) (λ g → runT (f ∘ g))

  open ElT public

  infixl 50 _[_]ET

  _[_]ET : ∀ {Γ : Con} {A : Ty Γ} {x y} {γ : El Γ x} →
           ElT A γ → (f : Hom y x) → ElT A (γ [ f ]E)
  runT (a [ f ]ET) g = runT a (f ∘ g)
  satT (a [ f ]ET) g = satT a (f ∘ g)

  ET-id : ∀ {Γ : Con} (A : Ty Γ) {x} {γ : El Γ x}
            (a : ElT A γ) → _[_]ET {A = A} {γ = γ} a id ≡ a
  ET-id A a = refl

  ET-comp : ∀ {Γ : Con} (A : Ty Γ) {x y z} {γ : El Γ x}
              (a : ElT A γ) (f : Hom y x) (g : Hom z y) →
              _[_]ET {A = A} {γ = γ [ f ]E} (_[_]ET {A = A} {γ = γ} a f) g
              ≡ _[_]ET {A = A} {γ = γ} a (f ∘ g)
  ET-comp A a f g = refl

  ----------------------------------------------------------------------
  -- Terms

  record Tm (Γ : Con) (A : Ty Γ) : Set where
    field
      tm₀ : ∀ {x} (γ : El Γ x) → A .₀ γ
      tm₁ : ∀ {x} (γ : El Γ x) →
            A .₁ γ (λ f → tm₀ (γ [ f ]E))
  open Tm public
    renaming (tm₀ to ₀; tm₁ to ₁)

  ElTm : ∀ {Γ : Con} {A : Ty Γ} →
         Tm Γ A → ∀ {x} (γ : El Γ x) → ElT A γ
  runT (ElTm t γ) f = ₀ t (γ [ f ]E)
  satT (ElTm t γ) f = ₁ t (γ [ f ]E)

  ElTm-natural : ∀ {Γ : Con} (A : Ty Γ) {x y}
                   (t : Tm Γ A) (γ : El Γ x) (f : Hom y x) →
                   _[_]ET {A = A} {γ = γ} (ElTm t γ) f ≡ ElTm t (γ [ f ]E)
  ElTm-natural A t γ f = refl

  ----------------------------------------------------------------------
  -- Strict substitution of types and terms

  infixl 45 _[_]T _[_]t

  _[_]T : ∀ {Δ Γ : Con} → Ty Γ → Sub Δ Γ → Ty Δ
  (A [ σ ]T) .₀ δ = A .₀ (ElS σ δ)
  (A [ σ ]T) .₁ δ = A .₁ (ElS σ δ)

  _[_]t : ∀ {Δ Γ : Con} {A : Ty Γ} →
          Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]T)
  (t [ σ ]t) .₀ δ = t .₀ (ElS σ δ)
  (t [ σ ]t) .₁ δ = t .₁ (ElS σ δ)

  Ty-id : ∀ {Γ : Con} (A : Ty Γ) → A [ idS ]T ≡ A
  Ty-id A = refl

  Ty-comp : ∀ {Θ Δ Γ : Con}
              (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) →
              A [ σ ∘S τ ]T ≡ (A [ σ ]T) [ τ ]T
  Ty-comp A σ τ = refl

  Tm-id : ∀ {Γ : Con} {A : Ty Γ} (t : Tm Γ A) →
          t [ idS ]t ≡ t
  Tm-id t = refl

  Tm-comp : ∀ {Θ Δ Γ : Con} {A : Ty Γ}
              (t : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) →
              t [ σ ∘S τ ]t ≡ (t [ σ ]t) [ τ ]t
  Tm-comp t σ τ = refl

  ----------------------------------------------------------------------
  -- Empty context

  ∅ : Con
  ∅ .₀ _ = ⊤
  ∅ .₁ _ = ⊤ᵖ

  ε : ∀ {Γ} → Sub Γ ∅
  ε .₀ _ = tt
  ε .₁ _ = ttᵖ

  ∅-η : ∀ {Γ} (σ : Sub Γ ∅) → σ ≡ ε
  ∅-η σ = refl

  ----------------------------------------------------------------------
  -- Extensionality lemmas
  
  El-ext : ∀ {Γ x} {γ γ' : El Γ x} →
         (λ {y} (f : Hom y x) → run γ f)
         ≡ (λ {y} (f : Hom y x) → run γ' f) →
         γ ≡ γ'
  El-ext {γ = el r s} {γ' = el .r t} refl = refl

  Sub-ext : ∀ {Γ Δ} {σ τ : Sub Γ Δ} →
            (∀ {x} (ρ : El Γ x) → σ .₀ ρ ≡ τ .₀ ρ) →
             σ ≡ τ
  Sub-ext {σ = record { map₀ = σ₀ ; map₁ = σ₁ }}
          {τ = record { map₀ = τ₀ ; map₁ = τ₁ }} h with map₀-ext
    where
      map₀-ext : (λ {x} → σ₀ {x}) ≡ (λ {x} → τ₀ {x})
      map₀-ext = funextᵢ λ x → funext λ ρ → h ρ
  ... | refl = refl

  Tm-ext : ∀ {Γ} {A : Ty Γ} {t t' : Tm Γ A} →
           (λ {x} (γ : El Γ x) → t .₀ γ)
           ≡ (λ {x} (γ : El Γ x) → t' .₀ γ) →
           t ≡ t'
  Tm-ext {t = record { tm₀ = t₀ ; tm₁ = t₁ }} {t' = record { tm₀ = .t₀ ; tm₁ = t₁' }} refl = refl

  -- By proof-irrelevance, two records are equal whenever their computational fields are equal.

  ----------------------------------------------------------------------
  -- Context comprehension
  
  _▷_ : (Γ : Con) (A : Ty Γ) → Con
  (Γ ▷ A) .₀ x     = Σ (El Γ x) (λ γ → A .₀ γ)
  (Γ ▷ A) .₁ {x} θ = ∃ Γ-coh A-valid
    where
      Γ-coh : Prop
      Γ-coh = ∀ {y z} {f : Hom y x} {g : Hom z y} →
              run (θ f .₁) g ≡ run (θ (f ∘ g) .₁) id

      A-valid : Γ-coh → Prop
      A-valid γ-coh = A .₁ γ̂ â
        where
          run-ext : ∀ {y} (f : Hom y x) →
            (λ {z} (g : Hom z y) → run (θ f .₁) g)
            ≡ (λ {z} (g : Hom z y) → run (θ (f ∘ g) .₁) id)
          run-ext f = funextᵢ λ z → funext λ g → γ-coh

          γ̂ : El Γ x
          run γ̂ f = run (θ f .₁) id
          sat γ̂ f = coeᵖ (Γ .₁) (run-ext f) (sat (θ f .₁) id)

          â : ∀ {y} (f : Hom y x) → A .₀ (γ̂ [ f ]E)
          â f = coe (A .₀) (El-ext (run-ext f)) (θ f .₂)

  -- A raw thunk θ in Γ ▷ A consists of a context part and a dependent type part.
  -- Γ-coh ensures that its first projections θ f .₁ form a coherent context element γ̂.
  -- More precisely, the proof γ-coh gives run-ext, which is used to construct γ̂.
  -- Its second projections θ f .₂ are transported to form a dependent element â over γ̂.
  -- A-valid requires this dependent element to be valid in A.

  fst-coh : ∀ {Γ} (A : Ty Γ) {x} (ρ : El (Γ ▷ A) x) →
            (λ {y} (f : Hom y x) → run (run ρ id .₁) f)
          ≡ (λ {y} (f : Hom y x) → run (run ρ (f ∘ id) .₁) id)              -- fst-coh proves that extracting the context component of ρ and then restricting along f
  fst-coh A ρ = funextᵢ λ y → funext λ f → (sat ρ id .₁) {f = id} {g = f}   -- agrees with first restricting and then extracting its context component.
  
  p : ∀ {Γ} (A : Ty Γ) → Sub (Γ ▷ A) Γ
  p     A .₀ ρ = run (run ρ id .₁) id
  p {Γ} A .₁ ρ = coeᵖ (Γ .₁) (fst-coh A ρ) (sat (run ρ id .₁) id)

  q : ∀ {Γ} (A : Ty Γ) → Tm (Γ ▷ A) (A [ p A ]T)
  q A .₀ ρ = coe (A .₀) (El-ext (fst-coh A ρ)) (run ρ id .₂)
  q A .₁ ρ = sat ρ id .₂

  ⟨_,_⟩ : ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ) → Tm Δ (A [ σ ]T) → Sub Δ (Γ ▷ A)
  ⟨ σ , t ⟩ .₀ δ = ElS σ δ , t .₀ δ
  ⟨ σ , t ⟩ .₁ δ = refl ,ᵖ t .₁ δ

  p∘⟨⟩ : ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]T)) →
         (p A ∘S (⟨_,_⟩ {A = A} σ t)) ≡ σ
  p∘⟨⟩ σ t = refl

  q⟨⟩ : ∀ {Γ Δ} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]T)) →
         (q A [ ⟨_,_⟩ {A = A} σ t ]t ) ≡ t
  q⟨⟩ σ t = refl

  ⟨⟩∘ : ∀ {Γ Δ Θ} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]T)) (τ : Sub Θ Δ) →
       (⟨_,_⟩ {A = A} σ t) ∘S τ ≡ ⟨_,_⟩ {A = A} (σ ∘S τ) (t [ τ ]t)
  ⟨⟩∘ σ t τ = refl

  Σ-coe : ∀ {A : Set} {B : A → Set} {x y : A} →
          (e : x ≡ y) → (u : B x) → (y , coe B e u) ≡ (x , u)   -- Σ-coe proves the equality of dependent pairs after transporting
  Σ-coe refl u = refl                                           -- the second component along the equality of the first components.

  ⟨⟩-η : ∀ {Γ} {A : Ty Γ} → ⟨_,_⟩ {A = A} (p A) (q A) ≡ idS
  ⟨⟩-η {A = A} = Sub-ext λ ρ → Σ-coe (El-ext (fst-coh A ρ)) (run ρ id .₂) 
 
  -- Idea of proof of ⟨⟩-η: 
    -- To prove equality of substitutions, we use Sub-ext.
    -- For every ρ : El (Γ ▷ A) x, we need to prove an equality of pairs. So, we use Σ-coe.
    -- The first components are in El Γ x, so we fill in El-ext (fst-coh A ρ).
    -- The second component is run ρ id .₂, which Σ-coe transports automatically.
  
  _,ᵉ_ : ∀ {Γ} {A : Ty Γ} {x} → (γ : El Γ x) → ElT A γ → El (Γ ▷ A) x
  run (γ ,ᵉ a) f = γ [ f ]E , runT a f
  sat (γ ,ᵉ a) f = refl ,ᵖ satT a f

  ElT-sub : ∀ {Δ Γ} (σ : Sub Δ Γ) (A : Ty Γ) {x}
              (δ : El Δ x) → ElT (A [ σ ]T) δ → ElT A (ElS σ δ)    -- ElT-sub packages an element of ElT (A [ σ ]T) δ
  runT (ElT-sub σ A δ a) f = runT a f                              -- as an element of ElT A (ElS σ δ), keeping runT and satT unchanged.
  satT (ElT-sub σ A δ a) f = satT a f
  
  ,ᵉ-η : ∀ {Γ} (A : Ty Γ) {x} (ρ : El (Γ ▷ A) x) →
        _,ᵉ_ {A = A} (ElS (p A) ρ) (ElT-sub (p A) A ρ (ElTm (q A) ρ)) ≡ ρ
  ,ᵉ-η A ρ = El-ext (funextᵢ λ y → funext λ f → Σ-coe (El-ext (fst-coh A (ρ [ f ]E))) (run ρ f .₂))

  -- The idea of proof of ,ᵉ-η is similar to that of ⟨⟩-η.

  ----------------------------------------------------------------------
  -- Pi Type

  lift : ∀ {Γ Δ} (σ : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ▷ (A [ σ ]T)) (Γ ▷ A)   -- lift extends σ under one context extension.
  lift σ A = ⟨_,_⟩ {A = A} (σ ∘S p (A [ σ ]T)) (q (A [ σ ]T))

  RunT : ∀ {Γ} (A : Ty Γ) {x} → El Γ x → Set
  RunT A γ = ∀ {y} (f : Hom y _) → A .₀ (γ [ f ]E)

  SatT : ∀ {Γ} (A : Ty Γ) {x} (γ : El Γ x) → RunT A γ → Prop
  SatT A γ r = ∀ {y} (f : Hom y _) → A .₁ (γ [ f ]E) (λ g → r (f ∘ g))

  packT : ∀ {Γ} {A : Ty Γ} {x} {γ : El Γ x} →
          (r : RunT A γ) → (s : SatT A γ r) → ElT A γ
  runT (packT r s) f = r f
  satT (packT r s) f = s f

  -- RunT and SatT open up the two fields of ElT. For a : ElT A γ,
    -- runT a : RunT A γ,
    -- satT a : SatT A γ (runT a).
  -- packT puts these components back into ElT.
  -- This expanded presentation makes substitution for Pi compute definitionally.

  Pi : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
  Pi A B .₀ γ   = (r : RunT A γ) → (s : SatT A γ r) → B .₀ (_,ᵉ_ {A = A} γ (packT r s))
  Pi A B .₁ γ θ = (r : RunT A γ) → (s : SatT A γ r) →
                  B .₁ (_,ᵉ_ {A = A} γ (packT r s))
                       (λ f → θ f (λ g → r (f ∘ g)) (λ g → s (f ∘ g)))

  -- Originally, we have λ f → θ f (a [ f ]ET). Opening up a [ f ]ET into its runT and satT fields
  -- gives (λ f → θ f (λ g → r (f ∘ g)) (λ g → s (f ∘ g))).
  
  lam : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) → Tm (Γ ▷ A) B → Tm Γ (Pi A B)
  lam A B b .₀ γ r s = b .₀ (_,ᵉ_ {A = A} γ (packT r s))
  lam A B b .₁ γ r s = b .₁ (_,ᵉ_ {A = A} γ (packT r s))

  app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} → Tm Γ (Pi A B) → (a : Tm Γ A) →
                                         Tm Γ (B [ ⟨_,_⟩ {A = A} idS a ]T)
  app u a .₀ γ = u .₀ γ (runT (ElTm a γ)) (satT (ElTm a γ))
  app u a .₁ γ = u .₁ γ (runT (ElTm a γ)) (satT (ElTm a γ))

  appPQ : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) → Tm Γ (Pi A B) →                          -- appPQ weakens u along p and applies it to the generic variable q.
          Tm (Γ ▷ A) ((B [ lift (p A) A ]T) [ ⟨_,_⟩ {A = A [ p A ]T} idS (q A) ]T)
  appPQ A B u = app {A = A [ p A ]T} {B = B [ lift (p A) A ]T} (u [ p A ]t) (q A)
  
  appGen : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} → Tm Γ (Pi A B) → Tm (Γ ▷ A) B            -- generic application.
  appGen     {A = A} {B = B} u .₀     ρ = coe  (B .₀) (,ᵉ-η A ρ) (appPQ A B u .₀ ρ)
  appGen {Γ} {A = A} {B = B} u .₁ {x} ρ = coeᵖ  B₁    (,ᵉ-η A ρ) (appPQ A B u .₁ ρ)
    where
      B₁ : El (Γ ▷ A) x → Prop
      B₁ ξ = B .₁ ξ (λ f → appGen {A = A} {B = B} u .₀ (ξ [ f ]E))
      
      -- B₁ ξ states that the values produced by appGen u at every restriction
      -- of ξ form a valid B-thunk over ξ.
      -- It is the Prop-valued counterpart of B .₀ used as the motive for coeᵖ.

  Pi-β : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) (b : Tm (Γ ▷ A) B) (a : Tm Γ A) →
       app {A = A} {B = B} (lam A B b) a ≡ b [ ⟨_,_⟩ {A = A} idS a ]t
  Pi-β A B b a = refl

  Pi-η : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) (u : Tm Γ (Pi A B)) →
         lam A B (appGen {A = A} {B = B} u) ≡ u
  Pi-η A B u = refl

  Pi∘ : ∀ {Γ Δ} (A : Ty Γ) (B : Ty (Γ ▷ A)) →
        (σ : Sub Δ Γ) →
        Pi A B [ σ ]T ≡ Pi (A [ σ ]T) (B [ lift σ A ]T)
  Pi∘ A B σ = refl

  lam∘ : ∀ {Γ Δ} (A : Ty Γ) (B : Ty (Γ ▷ A)) →
        (σ : Sub Δ Γ) → (b : Tm (Γ ▷ A) B) →
        coe (Tm Δ) (Pi∘ A B σ) (lam A B b [ σ ]t) ≡
        lam (A [ σ ]T) (B [ lift σ A ]T) (b [ lift σ A ]t)
  lam∘ A B σ b = refl

  app∘ : ∀ {Γ Δ} (A : Ty Γ) (B : Ty (Γ ▷ A)) →
        (σ : Sub Δ Γ) → (u : Tm Γ (Pi A B)) → (a : Tm Γ A) →
        app {A = A} {B = B} u a [ σ ]t ≡
        app {A = A [ σ ]T} {B = B [ lift σ A ]T} (coe (Tm Δ) (Pi∘ A B σ) (u [ σ ]t)) (a [ σ ]t)
  app∘ A B σ u a = refl

  -- Pi-η uses the derived generic application appGen.
  -- Pi-β and app∘ use the primitive binary application app.

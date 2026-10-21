{-# OPTIONS --prop --local-rewriting --rewriting #-}

open import prefascist

module prefascistYoneda
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

open prefascist.CwF Obj Hom id comp id-left id-right assoc

-----------------------------------------------------------
-- Yoneda embedding

Yo : Obj → Con
Yo x .₀       = λ x' → Hom x' x
Yo x .₁ {y} ĥ = ∀ {z} (f : Hom z y) → ĥ f ≡ (ĥ id) ∘ f

YoS : ∀ {x y} (f : Hom y x) → Sub (Yo y) (Yo x)
YoS f .₀ χ   = f ∘ (run χ id)
YoS f .₁ γ g = cong (λ k → f ∘ k) ((sat γ id) g)

Yo-id : ∀ {x} → YoS {x} id ≡ idS
Yo-id = refl

Yo-comp : ∀ {x y z} {f : Hom y x} {g : Hom z y} → YoS (f ∘ g) ≡ (YoS f) ∘S (YoS g)
Yo-comp = refl

------------------------------------------------------------------------------------------
-- Yoneda lemma: Sub (Yo x) Γ ≅ El Γ x naturally

YoId : ∀ {x} → El (Yo x) x
run YoId f = f
sat YoId f = λ g → refl

YoEv : ∀ {x} {Γ : Con} → Sub (Yo x) Γ → El Γ x
YoEv α = ElS α YoId

YoNat : ∀ {x} {Γ : Con} → El Γ x → Sub (Yo x) Γ
YoNat         γ .₀ = λ ρ → run γ (run ρ id)
YoNat {Γ = Γ} γ .₁ = λ ρ → coeᵖ (Γ .₁)
                           (funextᵢ λ y → funext λ f → cong (run γ) (sym (sat ρ id f)))
                           (sat γ (run ρ id))

Yo-nat-ev : ∀ {x} {Γ : Con} (γ : El Γ x) →
                YoEv (YoNat γ) ≡ γ
Yo-nat-ev γ = refl

Yo-ev-nat : ∀ {x} {Γ : Con} (α : Sub (Yo x) Γ) →
                YoNat (YoEv α) ≡ α
Yo-ev-nat α = Sub-ext (λ ρ → cong (α .₀) (El-ext (funextᵢ λ y → funext λ f → sym (sat ρ id f))))

-- naturality of the bijection:

YoEv-natural-Obj : ∀ {x y} {Γ : Con} (α : Sub (Yo x) Γ) (f : Hom y x) →
                    YoEv (α ∘S YoS f) ≡ YoEv α [ f ]E
YoEv-natural-Obj α f = refl

YoEv-natural-Con : ∀ {x} {Γ Δ : Con} (σ : Sub Γ Δ) (α : Sub (Yo x) Γ) →
                       YoEv (σ ∘S α) ≡ ElS σ (YoEv α)
YoEv-natural-Con σ α = refl

------------------------------------------------------------------------------------------
-- Yoneda embedding is fully faithful: Hom x y ≅ Sub (Yo x) (Yo y) naturally

YoUnemb : ∀ {x y} → Sub (Yo x) (Yo y) → Hom x y
YoUnemb α = run (YoEv α) id

YoEmb : ∀ {x y} → Hom x y → Sub (Yo x) (Yo y)
YoEmb = YoS

Yo-unemb-emb : ∀ {x y} → (f : Hom x y) → YoUnemb (YoEmb f) ≡ f
Yo-unemb-emb f = refl                   

Yo-emb-unemb-lemma : ∀ {x y} (α : Sub (Yo x) (Yo y)) → YoEmb (YoUnemb α) ≡ YoNat (YoEv α)
Yo-emb-unemb-lemma α = Sub-ext (λ χ → sym (sat (YoEv α) id (run χ id)))

Yo-emb-unemb : ∀ {x y} → (α : Sub (Yo x) (Yo y)) → YoEmb (YoUnemb α) ≡ α
Yo-emb-unemb {x = x} {y = y} α = trans (Yo-emb-unemb-lemma α) (Yo-ev-nat α)

-- Since YoEmb = YoS, its naturality is already expressed by Yo-id and Yo-comp.
-- YoUnemb is the inverse of YoEmb, so its naturality follows from the inverse laws.
-- Hence no separate naturality equations are needed for this part (full faithfulness).

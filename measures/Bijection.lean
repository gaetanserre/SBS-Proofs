import Mathlib.Tactic

def is_injective {α : Type _} {β : Type _} (f : α -> β) :=  ∀ (a₁ a₂ : α), a₁ ≠ a₂ -> f a₁ ≠ f a₂

def is_surjective {α : Type _} {β : Type _} (f : α -> β) := ∀ (b : β), ∃ (a : α), f a = b

/- def is_bijective {α : Type _} {β : Type _} (f : α -> β) := ∀ (b : β),
∃ (a : α), (f a = b) ∧ (∀ (a₂ : α), a ≠ a₂ -> f a ≠ f a₂)

theorem bijective_is_inj_and_surj {α : Type _} {β : Type _} (f : α -> β) (hinj : is_injective f) (hsurj : is_surjective f) : is_bijective f := by
intro b
specialize hsurj b
cases hsurj with
  | intro a fab =>
      use a
      constructor
      {exact fab}
      {
        intros a2 neqa
        exact hinj a a2 neqa
      } -/

def is_bijective {α : Type _} {β : Type _} (f : α -> β) := is_injective f ∧ is_surjective f

lemma bijective_imp_inversible {α : Type _} {β : Type _} (f : α -> β) (h : is_bijective f) : ∃ (f_inv : β -> α), (∀ (b : β), f (f_inv b) = b ∧ ∀ (a : α), f_inv (f a) = a) := by
cases h with
  | intro hinj hsurj =>
    choose f_inv h using hsurj
    use f_inv
    intro b
    constructor
    {
      exact h b
    }
    intro a
    specialize h (f a)
    by_contra hbar
    push_neg at hbar
    have key : f (f_inv (f a)) ≠ f a := hinj _ _ hbar
    exact key h -- (a ≠ b : a = b -> False)


/- def is_reciprocal {α : Type _} {β : Type _} (f : α -> β) (f_inv : β -> α) := (∀ (b : β), f (f_inv b) = b ∧ ∀ (a : α), f_inv (f a) = a)

lemma deterministic_function {α : Type _} {β : Type _} (f : α -> β) : ∀ (a₁ a₂ : α), f a₁ ≠ f a₂ -> a₁ ≠ a₂ := by
intros a₁ a₂ h
contrapose h
push_neg at h 
push_neg
rw [h]

lemma hom_inv_is_surj {α : Type _} {β : Type _} (f : α -> β) (f_inv : β -> α) (h1 : is_bijective f) (h2 : is_reciprocal f f_inv) : is_surjective f_inv := by
intro a
use (f a)
exact And.right hom.is_bij_reci a

lemma bij_reciprocal_is_injective {α : Type _} {β : Type _} (f : α -> β) (f_inv : β -> α) (h1 : is_bijective f) (h2 : is_reciprocal f f_inv) : is_injective f_inv := by
intros b₁ b₂ hdif
have key1 : ∃ (a : α), f a = b₁ := h1.right b₁
have key2 : ∃ (a : α), f a = b₂ := h1.right b₂
cases key1 with 
  | intro a₁ key1 =>
    cases key2 with 
      | intro a₂ key2 =>
        rw [← key1, ← key2]
        rw [And.right hom.is_bij_reci a₁, And.right hom.is_bij_reci a₂]
        rw [← h1, ← h2 ] at hdif
        exact deterministic_function hom.f a₁ a₂ hdif

/- A surjective reciprocal is the reciprocal bijective -/
example {α : Type _} {β : Type _} (f : α -> β)  (f_inv : β -> α) (h1 : is_reciprocal f f_inv)  (h2 : is_surjective f_inv) : ∀ (a : α), f_inv (f a) = a := by
intro a
have key : ∃ (b : β), f_inv b = a := h2 a
cases key with
  | intro b key =>
    rw [←key]
    rw [h1 b]

def is_bij_reciprocal {α : Type _} {β : Type _} (f : α -> β) (f_inv : β -> α) := is_reciprocal f f_inv ∧ ∀ (a : α), f_inv (f a) = a


structure homeomorphism (α : Type _) (β : Type _)
where
f : α -> β
inv_f : β -> α
is_bij : is_bijective f
is_bij_reci : is_bij_reciprocal f inv_f
is_bij_inv : is_bijective inv_f

lemma hom_inv_is_surj {α : Type _} {β : Type _} (hom : homeomorphism α β) : is_surjective hom.inv_f := by
intro a
use (hom.f a)
exact And.right hom.is_bij_reci a

lemma hom_inv_is_inj {α : Type _} {β : Type _} (hom : homeomorphism α β) : is_injective hom.inv_f := by
intros b₁ b₂ hdif
have h1 : ∃ (a : α), hom.f a = b₁ := (And.right hom.is_bij) b₁
have h2 : ∃ (a : α), hom.f a = b₂ := (And.right hom.is_bij) b₂
cases h1 with 
  | intro a₁ h1 =>
    cases h2 with 
      | intro a₂ h2 =>
        rw [← h1, ← h2]
        rw [And.right hom.is_bij_reci a₁, And.right hom.is_bij_reci a₂]
        rw [← h1, ← h2 ] at hdif
        exact deterministic_function hom.f a₁ a₂ hdif

lemma hom_inv_is_bij {α : Type _} {β : Type _} (hom : homeomorphism α β) : is_bijective hom.inv_f := by
exact ⟨hom_inv_is_inj hom, hom_inv_is_surj hom⟩ -/
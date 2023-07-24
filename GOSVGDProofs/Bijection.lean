import Mathlib.Tactic

def is_injective {α : Type _} {β : Type _} (f : α → β) :=  ∀ (a₁ a₂ : α), a₁ ≠ a₂ → f a₁ ≠ f a₂

lemma is_inj_imp_set_inj {α : Type _} {β : Type _} (f : α → β) : is_injective f → ∀ (A : Set α), Set.InjOn f A :=
by
intros h _A x₁ _x₁InA x₂ _x₂InA hf
specialize h x₁ x₂
by_contra xdif
push_neg at xdif
exact h xdif hf

def is_surjective {α : Type _} {β : Type _} (f : α → β) := ∀ (b : β), ∃ (a : α), f a = b

lemma is_surj_imp_set_surj {α : Type _} {β : Type _} (f : α → β) : is_surjective f → Set.SurjOn f (Set.univ) (Set.univ) :=
by
intros h b _huniv
specialize h b
cases h with
  | intro a h =>
    use a
    constructor
    {simp}
    {exact h}

/- def is_bijective {α : Type _} {β : Type _} (f : α → β) := ∀ (b : β),
∃ (a : α), (f a = b) ∧ (∀ (a₂ : α), a ≠ a₂ → f a ≠ f a₂)

theorem bijective_is_inj_and_surj {α : Type _} {β : Type _} (f : α → β) (hinj : is_injective f) (hsurj : is_surjective f) : is_bijective f := by
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

def is_bijective {α : Type _} {β : Type _} (f : α → β) := is_injective f ∧ is_surjective f

lemma is_bij_imp_set_bij {α : Type _} {β : Type _} (f : α → β) : is_bijective f → Set.BijOn f Set.univ Set.univ :=
by
intro h
constructor
{
  intros a ha
  simp
}
constructor
{exact is_inj_imp_set_inj f h.left Set.univ}
{exact is_surj_imp_set_surj f h.right}

lemma bijective_imp_inversible {α : Type _} {β : Type _} (f : α → β) (h : is_bijective f) : ∃ (f_inv : β → α), (∀ (b : β), f (f_inv b) = b ∧ ∀ (a : α), f_inv (f a) = a) := by
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
    exact key h -- (a ≠ b : a = b → False)

def is_reciprocal {α : Type _} {β : Type _} (f : α → β) (f_inv : β → α) := (∀ (b : β), f (f_inv b) = b) ∧ (∀ (a : α), f_inv (f a) = a)

lemma deterministic_function {α : Type _} {β : Type _} (f : α → β) : ∀ (a₁ a₂ : α), f a₁ ≠ f a₂ → a₁ ≠ a₂ := by
intros a₁ a₂ h
/- by_contra h2
rw [h2] at h
apply h
exact Eq.refl (f a₂) -/
contrapose h
push_neg at h 
push_neg
rw [h]

lemma reciprocal_of_bij_is_bij {α : Type _} {β : Type _} (f : α → β) (f_inv : β → α) (h1 : is_reciprocal f f_inv) (h2 : is_bijective f) : is_bijective f_inv := by
constructor
{
  intros b₁ b₂ difb₁b₂
  have key1 : ∃ (a : α), f a = b₁ := h2.right b₁
  have key2 : ∃ (a : α), f a = b₂ := h2.right b₂
  cases key1 with 
    | intro a₁ key1 =>
      cases key2 with 
        | intro a₂ key2 =>
          rw [← key1, ← key2]
          rw [h1.right a₁, h1.right a₂]
          rw [← key1, ← key2 ] at difb₁b₂
          exact deterministic_function f a₁ a₂ difb₁b₂
}

{
  intro a
  use (f a)
  exact h1.right a
}

lemma identity_reciprocal_set_extension (f : α → β) (f_inv : β → α) (h : is_reciprocal f f_inv) : (∀ (A : Set α), A = f_inv '' (f '' A)) ∧ (∀ (B : Set β), B = f '' (f_inv '' B)) :=
by
constructor
{
  intro A
  ext a
  constructor
  { 
    intro ainA
    unfold Set.image
    use (f a)
    constructor
    {
      use a
      constructor
      { exact ainA }
      { exact Eq.refl (f a) }
    }
    exact h.right a
  }

  {
    intro ainF
    unfold Set.image at ainF
    cases ainF with
      | intro b binF =>
        cases binF with
          | intro binF r =>
            cases binF with
              | intro a' rr =>
                cases rr with
                  | intro rrl rrr =>
                    rw [←rrr] at r
                    rw [h.right a'] at r
                    rwa [←r]
  }
}

{
  intro B
  ext b
  constructor
  { 
    intro binB
    unfold Set.image
    use (f_inv b)
    constructor
    {
      use b
      constructor
      { exact binB }
      { exact Eq.refl (f_inv b) }
    }
    exact h.left b
  }

  {
    intro binF
    unfold Set.image at binF
    cases binF with
      | intro a ainF =>
        cases ainF with
          | intro ainF r =>
            cases ainF with
              | intro b' rr =>
                cases rr with
                  | intro rrl rrr =>
                    rw [←rrr] at r
                    rw [h.left b'] at r
                    rwa [←r]
  }
}

lemma composition_inv_eq_id (f : α → β) (f_inv : β → α) (h : is_reciprocal f f_inv) : f ∘ f_inv = id ∧ f_inv ∘ f = id :=
by
constructor
{
  ext b
  exact h.left b
}

{
  ext a
  exact h.right a
}

lemma image_of_univ_is_univ (f : α → α) (f_inv : α → α) (h1 : is_bijective f) (h2 : is_reciprocal f f_inv) : f_inv '' Set.univ = Set.univ :=
by
ext a
constructor
{
  intro _aInfUniv
  simp
}
{
  intro _aInUniv
  have key : ∃ (b : α), f_inv b = a := (reciprocal_of_bij_is_bij f f_inv h2 h1).right a
  cases key with
    | intro b key =>
      use b
      constructor
      {simp}
      {exact key}
}

/- def is_reciprocal {α : Type _} {β : Type _} (f : α → β) (f_inv : β → α) := (∀ (b : β), f (f_inv b) = b ∧ ∀ (a : α), f_inv (f a) = a)

lemma deterministic_function {α : Type _} {β : Type _} (f : α → β) : ∀ (a₁ a₂ : α), f a₁ ≠ f a₂ → a₁ ≠ a₂ := by
intros a₁ a₂ h
contrapose h
push_neg at h 
push_neg
rw [h]

lemma hom_inv_is_surj {α : Type _} {β : Type _} (f : α → β) (f_inv : β → α) (h1 : is_bijective f) (h2 : is_reciprocal f f_inv) : is_surjective f_inv := by
intro a
use (f a)
exact And.right hom.is_bij_reci a

lemma bij_reciprocal_is_injective {α : Type _} {β : Type _} (f : α → β) (f_inv : β → α) (h1 : is_bijective f) (h2 : is_reciprocal f f_inv) : is_injective f_inv := by
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
example {α : Type _} {β : Type _} (f : α → β)  (f_inv : β → α) (h1 : is_reciprocal f f_inv)  (h2 : is_surjective f_inv) : ∀ (a : α), f_inv (f a) = a := by
intro a
have key : ∃ (b : β), f_inv b = a := h2 a
cases key with
  | intro b key =>
    rw [←key]
    rw [h1 b]

def is_bij_reciprocal {α : Type _} {β : Type _} (f : α → β) (f_inv : β → α) := is_reciprocal f f_inv ∧ ∀ (a : α), f_inv (f a) = a


structure homeomorphism (α : Type _) (β : Type _)
where
f : α → β
inv_f : β → α
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
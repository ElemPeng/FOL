inductive Wff where
| pv : Nat → Wff
| not : Wff → Wff
| imp : Wff → Wff → Wff

prefix:60 "~" => Wff.not
infixr:55 "⇒" => Wff.imp

abbrev TA := Nat → Bool

@[simp] def EvalW (v : TA) : Wff → Bool
  | Wff.pv n => v n
  | ~φ => ! (EvalW v φ)
  | φ ⇒ ψ => ! (EvalW v φ) || (EvalW v ψ)

def Wff.IsTautology (φ : Wff) : Prop := ∀ v : TA, EvalW v φ = true

theorem tail_subset {φ : Wff} {Γ : List Wff} : Γ ⊆ φ :: Γ :=
  (List.subset_cons_of_subset φ fun _ a => a)

inductive Deriv : List Wff → Wff → Prop where
  | assumption {φ : Wff} {Γ : List Wff} : φ ∈ Γ →  Deriv Γ φ
  | not_I (ψ : Wff) {φ : Wff} {Γ : List Wff}: Deriv (φ :: Γ) ψ → Deriv (φ :: Γ) (~ψ) → Deriv Γ (~φ)
  | dne {φ : Wff} {Γ : List Wff} : Deriv Γ (~~φ) → Deriv Γ φ
  | imp_I {φ ψ : Wff} {Γ : List Wff} : Deriv (φ :: Γ) ψ → Deriv Γ (φ ⇒ ψ)
  | MP {φ ψ : Wff} {Γ : List Wff} : Deriv Γ φ → Deriv Γ (φ ⇒ ψ) → Deriv Γ ψ

def Entails (Γ : List Wff) (φ : Wff) : Prop := ∀ v : TA, (∀ γ ∈ Γ, EvalW v γ = true) → EvalW v φ = true

theorem Deriv.weaken {φ : Wff} {Γ : List Wff} : Deriv Γ φ → ∀ Γ', Γ ⊆ Γ' → Deriv Γ' φ:= by
  intro h ; induction h with
  | assumption h1 => intro Γ' h'; exact assumption <| h' h1
  | not_I ψ h1 h2 ih1 ih2 =>
    intro Γ' h'; expose_names; have ha : φ_1 :: Γ_1 ⊆ φ_1 :: Γ' := List.cons_subset_cons φ_1 h'
    have ih1' := ih1 (φ_1 :: Γ') ha; have ih2' := ih2 (φ_1 :: Γ') ha; exact (not_I ψ ih1' ih2')
  | dne h ih => intro Γ' h'; exact dne <| ih Γ' h'
  | imp_I h ih =>
    intro Γ' h'; expose_names; have ha : φ_1 :: Γ_1 ⊆ φ_1 :: Γ' := List.cons_subset_cons φ_1 h'
    exact imp_I <| ih (φ_1 :: Γ') ha
  | MP h1 h2 ih1 ih2 => intro Γ' h'; expose_names; exact MP (ih1 (Γ') h') (ih2 (Γ') h')

infix:40 " ⊢₀ " => Deriv

infix:40 " ⊨ " => Entails

theorem Deriv.head {φ : Wff} {Γ : List Wff} : φ :: Γ ⊢₀ φ := assumption List.mem_cons_self

theorem Deriv.imp_self {φ : Wff} {Γ : List Wff} : Γ ⊢₀ φ ⇒ φ :=
  imp_I head

theorem Deriv.lem {φ ψ : Wff} {Γ : List Wff} : φ :: Γ ⊢₀ ψ → (~φ) :: Γ ⊢₀ ψ → Γ ⊢₀ ψ := by
  intro h1 h2; generalize hΔ : (~ψ) :: Γ = Δ
  have h3 : Δ ⊢₀ (~φ) := by
    apply not_I ψ
    · apply weaken (Γ := φ :: Γ) h1; simp [←hΔ]
    · apply weaken (Γ := Δ) (assumption (by simp [←hΔ])); simp
  have h4 : Δ ⊢₀ (~~φ) := by
    apply not_I ψ
    · apply weaken (Γ := (~φ) :: Γ) h2; simp [←hΔ]
    · apply weaken (Γ := Δ) (assumption (by simp [←hΔ])); simp
  simp_all [←hΔ]; apply dne; apply not_I (~φ) h3 h4

theorem Deriv.exfalso (ψ : Wff) {φ : Wff} {Γ : List Wff} : Γ ⊢₀ φ → Γ ⊢₀ (~φ) → Γ ⊢₀ ψ := by
  intro h1 h2; apply dne; apply not_I φ
  · apply weaken h1 ((~ψ) :: Γ) (tail_subset)
  · apply weaken h2 ((~ψ) :: Γ) (tail_subset)

theorem soundness_lem {Γ : List Wff} {φ : Wff} {v : TA} (h' : EvalW v φ = true)
(hv : ∀ (γ : Wff), γ ∈ Γ → EvalW v γ = true) :  ∀ (γ : Wff), γ ∈ φ :: Γ → EvalW v γ = true := by
  intro γ hγ; simp at hγ; rcases hγ with h | h
  · simp_all
  · exact hv γ h

theorem soundness {Γ : List Wff} {φ : Wff} : Γ ⊢₀ φ → Γ ⊨ φ := by
  intro h; induction h with
  | assumption h =>
    expose_names; intro v hv; exact hv φ_1 h
  | not_I ψ h1 h2 ih1 ih2 =>
    expose_names; intro v hv; by_cases h' : EvalW v (~φ_1) = true
    · exact h'
    simp at h'; have h'' := soundness_lem h' hv
    have ih1' := ih1 v h''; have ih2' := ih2 v h''
    simp at ih2'; rw [Bool.eq_false_iff] at ih2'
    exact absurd ih1' ih2'
  | dne h ih =>
    expose_names; intro v hv; have ih' := ih v hv; simpa using ih'
  | imp_I h ih =>
    expose_names; intro v hv; simp; by_cases h' : EvalW v (φ_1) = false
    · exact Or.inl h'
    simp at h'; exact Or.inr <| ih v (soundness_lem h' hv)
  | MP h1 h2 ih1 ih2 =>
    intro v hv; have ih1' := ih1 v hv
    have ih2' := ih2 v hv; simp at ih2'; rw [Bool.eq_false_iff] at ih2'
    exact Or.neg_resolve_left ih2' ih1'

theorem Deriv.not_not {Γ : List Wff} {φ : Wff} : Γ ⊢₀ φ → Γ ⊢₀ ~~φ := by
  intro h; apply not_I φ
  · exact weaken h ( (~φ) :: Γ) (tail_subset)
  · exact head

theorem Deriv.a_imp_b_of_not_a {Γ : List Wff} {φ ψ : Wff} : Γ ⊢₀ ~φ → Γ ⊢₀ φ ⇒ ψ := by
  intro h; apply imp_I; apply exfalso
  · exact head
  · exact weaken h (φ :: Γ) (tail_subset)

theorem Deriv.a_imp_b_of_b {Γ : List Wff} {φ ψ : Wff} : Γ ⊢₀ ψ → Γ ⊢₀ φ ⇒ ψ := by
  intro h; apply imp_I <| weaken h (φ :: Γ) (tail_subset)

theorem Deriv.a_and_not_b {Γ : List Wff} {φ ψ : Wff} : Γ ⊢₀ φ → Γ ⊢₀ ~ψ → Γ ⊢₀ ~(φ ⇒ ψ) := by
  intro h1 h2; apply not_I ψ
  · exact MP (weaken h1 ((φ ⇒ ψ ):: Γ) (tail_subset)) head
  · exact weaken h2 ((φ ⇒ ψ) :: Γ) tail_subset

-- Completeness time lol

def Wff.Bound : Wff → Nat
  | Wff.pv n => n + 1
  | Wff.not φ => Bound φ
  | Wff.imp φ ψ => max (Bound φ) (Bound ψ)

def lit (v : TA) (N : Nat) := if v N = true then Wff.pv N else ~(Wff.pv N)

def ctx (v : TA) : Nat → List Wff
  | Nat.zero => []
  | Nat.succ N => lit v N :: ctx v N

theorem lit_lem {n N : Nat} {v : TA} : n < N → lit v n ∈ ctx v (N) := by
  intro h; induction N with
  | zero => exact absurd h (Nat.not_lt_zero n)
  | succ k ih =>
    rw [Nat.add_one, Nat.lt_succ_iff_lt_or_eq] at h
    simp [ctx]; rcases h with h' | h'
    · exact Or.inr <| ih h'
    · rw [h']; exact Or.inl rfl

theorem kalmar_lemma {φ : Wff} {v : TA} (N : Nat) : φ.Bound ≤ N → (EvalW v φ = true → ctx v N ⊢₀ φ) ∧ (EvalW v φ = false → ctx v N ⊢₀ ~φ) := by
  intro h1; induction φ with
  | pv k =>
    constructor; all_goals (
        intro h2; rw [Wff.Bound, ←Nat.lt_iff_add_one_le] at h1; simp at h2
        have h3 : lit v k ∈ ctx v N := lit_lem h1
        unfold lit at h3; simp [h2] at h3; exact .assumption h3)
  | not φ' ih =>
    simp [Wff.Bound] at h1; have ⟨ih1, ih2⟩ := ih h1; constructor
    · intro h2; simp at h2; exact ih2 h2
    · intro h2; simp at h2; exact Deriv.not_not <| ih1 h2
  | imp φ' ψ' ihφ ihψ =>
    simp [Wff.Bound, Nat.max_le] at h1; obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨ihφ1, ihφ2⟩ := ihφ h1a; obtain ⟨ihψ1, ihψ2⟩ := ihψ h1b
    constructor
    · intro h; simp at h; rcases h with h' | h'
      · exact Deriv.a_imp_b_of_not_a <| ihφ2 h'
      · exact Deriv.a_imp_b_of_b <| ihψ1 h'
    · intro h; simp at h; have h1 := ihφ1 h.1; have h2 := ihψ2 h.2
      exact Deriv.a_and_not_b h1 h2

theorem ctx_eq_lem (v v' : TA) (N : Nat) : (∀ k : Nat, k < N → v k = v' k) → ctx v N = ctx v' N := by
  intro h; induction N with
  | zero => unfold ctx; rfl
  | succ N' ih =>
    unfold ctx; have h' : (∀ (k : Nat), k < N' → v k = v' k) := by
      intro k hk; apply h k; exact Nat.lt_add_right 1 hk
    simp [ih h', lit, h N' (Nat.lt_add_one N')]

theorem Deriv.com_lem {φ' : Wff} (n : Nat) :
  (φ'.IsTautology → ∀ v : TA, ctx v (φ'.Bound - n) ⊢₀ φ') := by
  induction n with
  | zero =>
    simp; intro htaut v; exact (kalmar_lemma (φ'.Bound) (Nat.le_refl φ'.Bound)).1 <| htaut v
  | succ k ih =>
    intro htaut v; have hv := (ih htaut) v; by_cases hk : k ≥ φ'.Bound
    · simp [hk] at hv; rwa [Nat.sub_eq_zero_of_le (Nat.le.step hk)]
    generalize hN : φ'.Bound - (k+1) = N
    simp at hk; let v' : TA := fun n ↦ if n = N then ! v n else v n
    have hv' := (ih htaut) v'; have hN' : φ'.Bound - k = N.succ := by grind
    rw [hN'] at hv hv'; unfold ctx at hv hv'
    have hctx : ctx v N = ctx v' N := by
      apply ctx_eq_lem; intro k' hk'; unfold v'; simp_all; exact Nat.ne_of_lt hk'
    rw [←hctx] at hv'; unfold lit at hv hv'; unfold v' at hv'; by_cases hvN : v N = true
    ·  simp_all; exact lem hv hv'
    simp_all; exact lem hv' hv

theorem completeness {φ' : Wff} : φ'.IsTautology → [] ⊢₀ φ' := by
  intro h; have h' := Deriv.com_lem φ'.Bound h
  simpa [ctx] using h'

theorem entails_iff_deriv₀ {φ : Wff} : [] ⊨ φ ↔ [] ⊢₀ φ := by
  constructor
  · intro h; apply completeness; intro v; apply h; simp
  · exact soundness

theorem Deriv.imp_iff {φ ψ : Wff} {Γ : List Wff} : φ :: Γ ⊢₀ ψ ↔ Γ ⊢₀ φ ⇒ ψ := by
  constructor
  · exact imp_I
  · intro h; refine MP head (weaken h (φ :: Γ) tail_subset)

theorem Entails.imp_iff {φ ψ : Wff} {Γ : List Wff} : φ :: Γ ⊨ ψ ↔ Γ ⊨ φ ⇒ ψ := by
  constructor
  · intro h v hv; simp; by_cases hφ : EvalW v φ = false
    · exact Or.inl hφ
    simp at hφ; have h' := h v (soundness_lem hφ hv); exact Or.inr h'
  · intro h v hv; have h' := h v
    have h1 : EvalW v φ = true := hv φ List.mem_cons_self
    have h2 : (∀ (γ : Wff), γ ∈ Γ → EvalW v γ = true) := by
      intro γ hγ; exact hv γ (List.mem_of_mem_tail hγ)
    have h3 := h' h2; simp at h3; rw [Bool.eq_false_iff] at h3
    exact Or.neg_resolve_left h3 h1

theorem entails_iff_deriv {φ : Wff} {Γ : List Wff} : Γ ⊨ φ ↔ Γ ⊢₀ φ := by
  induction Γ generalizing φ with
  | nil => exact entails_iff_deriv₀
  | cons φ' Γ' ih => rw [Deriv.imp_iff, Entails.imp_iff]; exact ih

inductive Term where
| zero : Term
| succ : Term → Term
| add : Term → Term → Term
| mul : Term → Term → Term

instance : Zero Term where zero := .zero
prefix:100 "S" => Term.succ
instance : Add Term where add a b := .add a b
instance : Mul Term where mul a b := .mul a b

def numeral : Nat → Term
| 0 => .zero
| n + 1 => S(numeral n)

notation:max "⌜" n "⌝" => numeral n

@[simp] theorem succ_eq_succ {n : Nat} :  ⌜n.succ⌝ = S ⌜n⌝ := rfl

@[simp] theorem num_zero_eq_zero : ⌜0⌝  = 0 := rfl

inductive Wff where
| eq : Term → Term → Wff
| not : Wff → Wff
| imp : Wff → Wff → Wff

infix:63 "≐" => Wff.eq
prefix:60 "~" => Wff.not
infixr:55 "⇒" => Wff.imp

abbrev TA := Term → Term → Bool --- arbitrary truth assignment to t ≐ u

@[simp] def EvalW (v : TA) : Wff → Bool
  | σ ≐ τ => v σ τ
  | ~φ => ! (EvalW v φ)
  | φ ⇒ ψ => !(EvalW v φ) || (EvalW v ψ)

def IsTautology (φ : Wff) : Prop := ∀ v : TA, EvalW v φ = true
/-  Checks to see if φ is a substitution instance of a tautology.
    Technically, this replaces every term of the Wff with a propositional variable and checks if
    that PL Wff is a tautology, but this is equivalent to φ being T(φ₁, φ₂, …, φₙ) where T(p₁, p₂, …, pₙ)
    is a tautology.
-/
inductive term_ll (σ τ: Term) : Term → Term → Prop where
| refl {ρ : Term} : term_ll σ τ ρ ρ
| id : term_ll σ τ σ τ
| succ {ρ ρ' : Term} : term_ll σ τ ρ ρ' → term_ll σ τ (S ρ) (S ρ')
| add {π π' ρ ρ' : Term} : term_ll σ τ π π' →
  term_ll σ τ ρ ρ' → term_ll σ τ (π + ρ) (π' + ρ')
| mul {π π' ρ ρ' : Term} : term_ll σ τ π π' →
  term_ll σ τ ρ ρ' → term_ll σ τ (π * ρ) (π' * ρ')

inductive LL (σ τ : Term) : Wff → Wff → Prop where
-- ψ is φ with some instances of σ in φ replaced with τ
| eq {π π' ρ ρ' : Term} : term_ll σ τ π π' → term_ll σ τ ρ ρ' → LL σ τ (π ≐ ρ) (π' ≐ ρ')
| not {φ φ' : Wff} : LL σ τ φ φ' → LL σ τ (~φ) (~φ')
| imp {φ φ' ψ ψ' : Wff} : LL σ τ φ φ' → LL σ τ ψ ψ' → LL σ τ (φ ⇒ ψ) (φ' ⇒ ψ')

inductive Thm : Wff → Prop where
| eq_refl {τ : Term} : Thm (τ ≐ τ)
| ll {σ τ : Term} {φ φ': Wff} : LL σ τ φ φ' → Thm (φ ⇒ σ ≐ τ  ⇒ φ')
| taut {φ : Wff} : IsTautology φ → Thm φ
| ax1 {n : Nat} : Thm <| ~(0 ≐ S ⌜n⌝)
| ax2 {m n : Nat} : Thm <| S ⌜m⌝  ≐ S ⌜n⌝  ⇒ ⌜m⌝ ≐ ⌜n⌝
| ax3 {m : Nat} : Thm <| ⌜m⌝ + 0 ≐ ⌜m⌝
| ax4 {m n : Nat} : Thm <| ⌜m⌝ + S ⌜n⌝ ≐ S(⌜m⌝ + ⌜n⌝)
| ax5 {m : Nat} : Thm <| ⌜m⌝  * 0 ≐ 0
| ax6 {m n : Nat} : Thm <| ⌜m⌝ * S ⌜n⌝ ≐ ⌜m⌝ * ⌜n⌝ + ⌜m⌝
| MP {φ ψ : Wff} : Thm φ → Thm (φ ⇒ ψ) → Thm ψ

theorem Thm.ll' {σ τ : Term} {φ φ' : Wff} : LL σ τ φ φ' → Thm φ → Thm (σ ≐ τ) → Thm φ' :=
  fun h1 h2 h3 ↦ MP h3 <| MP h2 <| ll h1

theorem Thm.eq_symm {σ τ : Term} : Thm (σ ≐ τ ⇒ τ ≐ σ) :=
  MP eq_refl <| ll (.eq .id .refl)

theorem Thm.eq_symm' {σ τ : Term} (ht1 : Thm (σ ≐ τ)) : Thm (τ ≐ σ) :=
  MP ht1 eq_symm

theorem Thm.imp_switch {φ₁ φ₂ ψ: Wff} : Thm ( (φ₁ ⇒ φ₂ ⇒ ψ) ⇒ (φ₂ ⇒ φ₁ ⇒ ψ)) := by
  apply taut; intro v; simp [EvalW]; by_cases h1 : EvalW v φ₁ = true
  all_goals by_cases h2 : EvalW v φ₂ = true <;> by_cases h3 : EvalW v ψ = true
  all_goals simp_all

theorem Thm.eq_trans {σ τ ρ : Term} : Thm (σ ≐ τ ⇒ τ ≐ ρ ⇒ σ ≐ ρ) :=
  (ll (.eq .refl .id))

theorem Thm.eq_trans' {σ τ ρ : Term} (ht1: Thm (σ ≐ τ)) (ht2 : Thm (τ ≐ ρ)):
Thm (σ ≐ ρ) := ll' (.eq .refl .id) ht1 ht2

theorem Thm.add_eq_add' {σ σ' τ τ' : Term} (h1 : Thm (σ ≐ σ')) (h2 :Thm (τ ≐ τ')) :
Thm (σ + τ ≐ σ' + τ') := by
  have h3 : Thm (σ + τ ≐ σ' + τ) :=
    ll' (.eq (.add .refl .refl) (.add .id .refl) ) eq_refl h1
  exact ll' (.eq (.add .refl .refl) (.add .refl .id)) h3 h2

theorem Thm.mul_eq_mul' {σ σ' τ τ' : Term} (h1 : Thm (σ ≐ σ')) (h2 :Thm (τ ≐ τ')) :
Thm (σ * τ ≐ σ' * τ') := by
  have h3 : Thm (σ * τ ≐ σ' * τ) :=
    ll' (.eq (.mul .refl .refl) (.mul .id .refl) ) eq_refl h1
  exact ll' (.eq (.mul .refl .refl) (.mul .refl .id)) h3 h2

example : Thm (⌜1⌝  + ⌜1⌝  ≐ ⌜2⌝ ) := by
  have h1 : Thm (⌜1⌝  + ⌜1⌝ ≐ S(⌜1⌝  + 0)) := Thm.ax4
  have h2 : Thm (⌜1⌝  + 0 ≐ ⌜1⌝ ) := Thm.ax3
  have h3 : Thm (S (⌜1⌝  + 0) ≐ ⌜2⌝) := by
    have h31 : Thm (S (⌜1⌝  + 0) ≐ S (⌜1⌝  + 0)) := Thm.eq_refl
    exact Thm.ll' (LL.eq (term_ll.refl) <| term_ll.succ term_ll.id) h31 h2
  apply Thm.eq_trans' h1 h3

theorem Thm.imp_self {φ : Wff} : Thm (φ ⇒ φ) := by
  apply taut; intro v; simp [EvalW]

theorem Thm.contrapose {φ ψ : Wff} : Thm ((φ ⇒ ψ) ⇒ (~ψ ⇒ ~φ)) := by
  apply taut; intro v; simp [EvalW]
  by_cases h1 : EvalW v φ = true <;> by_cases h2 : EvalW v ψ = true
  all_goals simp_all

theorem Thm.ne_symm {σ τ : Term} : Thm (~(σ ≐ τ) ⇒ ~(τ ≐ σ)) := by
  exact MP eq_symm contrapose

theorem Thm.ne_symm' {σ τ : Term} : Thm (~(σ ≐ τ)) → Thm (~(τ ≐ σ)) := by
  intro ht1; exact MP ht1 ne_symm

-- Theorem 10.1 in Smith
theorem Thm.num_inj_lem {m k : Nat} :Thm (~(⌜m⌝ ≐ ⌜m + k.succ⌝)) := by
  induction m with
  | zero => simp [ax1]
  | succ m' ih =>
    rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]; simp
    exact MP ih <| MP (ax2) contrapose

theorem Thm.num_inj_lt {m n : Nat} : m < n → Thm (~(⌜m⌝ ≐ ⌜n⌝)) := by
  intro h; obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt h
  exact num_inj_lem

theorem Thm.num_inj {m n : Nat} : m ≠ n → Thm (~(⌜m⌝ ≐ ⌜n⌝)) := by
  intro h; rw [Nat.ne_iff_lt_or_gt] at h
  rcases h with h' | h'
  · exact num_inj_lt h'
  · apply ne_symm' (num_inj_lt h')

theorem Thm.succ_welldef {σ τ : Term} : Thm (σ ≐ τ ⇒ S σ ≐ S τ) :=
  MP eq_refl (ll (.eq .refl (.succ .id)))

-- Thm 10.2
theorem Thm.add_num_eq {m n : Nat} : Thm ( ⌜m⌝ + ⌜n⌝ ≐ ⌜m + n⌝) := by
  induction n with
  | zero => simp [ax3]
  | succ n' ih =>
    rw [←Nat.add_assoc]; exact eq_trans' ax4 <| MP ih succ_welldef

-- Thm 10.3
theorem Thm.mul_num_eq {m n : Nat} : Thm (⌜m⌝ * ⌜n⌝ ≐ ⌜m * n⌝) := by
  induction n with
  | zero => simp [ax5]
  | succ n' ih =>
    rw [Nat.mul_add, Nat.mul_one]; simp
    exact eq_trans' ax6 <| eq_trans' (add_eq_add' ih eq_refl) add_num_eq

example : Thm (~(⌜3⌝ ≐ ⌜4⌝)) := Thm.num_inj (by decide)

theorem Thm.succ_eq_add_one {n : Nat} : Thm (S⌜n⌝ ≐ ⌜n⌝ + ⌜1⌝) := by
  apply eq_symm'; refine eq_trans' add_num_eq eq_refl

@[simp] def Val : Term → Nat
| 0 => 0
| S n => Val (n) + 1
| n + m => Val (n) + Val (m)
| n * m => Val (n) * Val (m)

-- Theorem 10.4
theorem Thm.correct_val (τ : Term) : Thm (τ ≐ ⌜Val τ⌝) := by
  induction τ with
  | zero => exact eq_refl
  | succ k ih => exact MP ih succ_welldef
  | add m n hm hn => simp; exact eq_trans' (add_eq_add' hm hn) add_num_eq
  | mul m n hm hn => simp; exact eq_trans' (mul_eq_mul' hm hn) mul_num_eq

-- Thm 10.5
theorem Thm.decides_eq {σ τ : Term} : Val (σ) = Val (τ) → Thm (σ ≐ τ) :=
  fun h ↦ eq_trans' (h ▸ (correct_val σ) ) (Thm.eq_symm' (correct_val τ))

theorem Thm.decides_ne {σ τ : Term} : Val σ ≠ Val τ → Thm (~ (σ ≐ τ)) := by
  intro h; have h1 := num_inj h; have hσ := correct_val σ; have hτ := correct_val τ
  have h2 : Thm (~σ≐⌜Val τ⌝) := ll' (.not (.eq .id .refl ) ) h1 (eq_symm' hσ)
  exact ll' (.not (.eq .refl .id)) h2 (eq_symm' hτ)

@[simp] def v₀ : TA := fun σ τ ↦ Val σ = Val τ

@[simp] def Wff.TV (φ : Wff) : Bool := EvalW v₀ φ

theorem Thm.ll_sound_lem {σ τ π π' : Term} :
term_ll σ τ π π' → Val σ = Val τ → Val π = Val π' := by
  intro h1 h2; induction h1 with
  | refl => rfl
  | id => exact h2
  | succ _ ih => simp [ih]
  | add _ _ hn hm => simp [hn, hm]
  | mul _ _ hn hm => simp [hn, hm]

theorem Thm.LL_sound_lem {σ τ : Term} {φ φ' : Wff} :
LL σ τ φ φ' → Val σ = Val τ → φ.TV = φ'.TV := by
  intro h1 h2; induction h1 with
  | eq ha hb => simp [ll_sound_lem ha h2, ll_sound_lem hb h2]
  | not ha hb => simpa
  | imp ha hb hc hd => simp at hc hd ⊢; rw [←hc, ←hd]

theorem Thm.BA_is_sound {φ : Wff} : Thm φ → φ.TV = true := by
  intro h; induction h with
  | eq_refl => simp
  | taut ih => exact ih v₀
  | ax1 => simp
  | ax2 => simp
  | ax3 => simp
  | ax4 => simp [Nat.add_assoc]
  | ax5 => simp
  | MP _ _ ih1 ih2 =>
    simp at ih1 ih2 ⊢; apply Or.resolve_left ih2; simp [ih1]
  | ax6 => simp [Nat.mul_add]
  | ll ih =>
    simp; expose_names; have h := LL_sound_lem ih; by_cases h1 : Val σ = Val τ
    · have h2 := h h1; simp at h2; rw [h2]; by_cases h3 : EvalW v₀ φ' = true
      · exact Or.inr (Or.inr h3)
      · simp at h3; exact Or.inl h3
    exact Or.inr (Or.inl h1)

theorem Thm.BA_is_consistent {φ : Wff} : Thm φ → Thm (~φ) → False := by
  intro h1 h2; have h1' := BA_is_sound h1; have h2' := BA_is_sound h2
  simp_all

theorem Thm.not_not_intro {φ : Wff} : Thm (φ ⇒ ~~φ) := by
  apply taut; intro v; simp

theorem Thm.not_not_elim {φ : Wff} : Thm (~~φ ⇒ φ) := by
  apply taut; intro v; simp

theorem Thm.not_not_iff {φ : Wff} : Thm (~~φ) ↔ Thm (φ) := by
  constructor
  · intro h; exact MP h not_not_elim
  · intro h; exact MP h not_not_intro

theorem Thm.a_imp_b_of_not_a {φ ψ : Wff} : Thm (~φ ⇒ φ ⇒ ψ) := by
  apply taut; intro v; simp [←or_assoc]

theorem Thm.a_imp_b_of_b {φ ψ : Wff} : Thm (ψ ⇒ φ ⇒ ψ) := by
  apply taut; intro v; simp; rw [or_comm, or_assoc]; simp
theorem Thm.a_and_not_b {φ ψ : Wff} : Thm (φ ⇒ ~ψ ⇒ ~(φ ⇒ ψ)) := by
  apply taut; intro v; simp [or_and_left]; rw [or_comm, or_assoc]; simp

theorem Thm.BA_is_complete {φ : Wff} :
(φ.TV = true → Thm φ) ∧ (φ.TV = false → Thm (~φ)) := by
  induction φ with
  | eq σ τ => simp; exact ⟨decides_eq, decides_ne⟩
  | not φ ih =>
    simp at ih ⊢; rwa [and_comm, not_not_iff]
  | imp φ ψ h1 h2 =>
    simp_all; obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2; refine ⟨?_, ?_⟩
    · intro h; rcases h with h' | h'
      · exact MP (h1b h') a_imp_b_of_not_a
      · exact MP (h2a h') a_imp_b_of_b
    · intro h1 h2; obtain h1' := h1a h1; obtain h2' := h2b h2
      exact MP h2' (MP h1' a_and_not_b)

theorem Thm.BA_is_negation_complete (φ : Wff) : Thm (φ) ∨ Thm (~φ) := by
  by_cases h : φ.TV = true
  · exact Or.inl <| BA_is_complete.1 h
  simp at h; exact Or.inr <| BA_is_complete.2 h

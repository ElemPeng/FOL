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

@[simp] theorem succ_eq_n_plus_1 (n : Nat) : numeral (n + 1) = S numeral n := rfl

@[simp] theorem num_zero_eq_zero : numeral 0 = 0 := rfl

inductive Wff where
| eq : Term → Term → Wff
| not : Wff → Wff
| imp : Wff → Wff → Wff

infix:63 "≐" => Wff.eq
prefix:60 "~" => Wff.not
infixr:55 "⇒" => Wff.imp

abbrev TA := Term → Term → Bool --- arbitrary truth assignment to t ≐ u

def EvalW (v : TA) : Wff → Bool
  | σ ≐ τ => v σ τ
  | ~φ => ! (EvalW v φ)
  | φ ⇒ ψ => !(EvalW v φ) || (EvalW v ψ)

def IsTautology (φ : Wff) : Prop := ∀ v : TA, EvalW v φ = true
/-  Thecks to see if φ is a substitution instance of a tautology.
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
| refl {τ : Term} : Thm (τ ≐ τ)
| ll (σ τ : Term) {φ φ': Wff} : Thm φ → Thm (σ ≐ τ) → LL σ τ φ φ' → Thm φ'
| taut {φ : Wff} : IsTautology φ → Thm φ
| ax1 (n : Nat) : Thm <| ~(0 ≐ S ⌜n⌝)
| ax2 (m n : Nat) : Thm <| S ⌜m⌝  ≐ S ⌜n⌝  ⇒ ⌜m⌝ ≐ ⌜n⌝
| ax3 (m : Nat) : Thm <| ⌜m⌝ + 0 ≐ ⌜m⌝
| ax4 (m n : Nat) : Thm <| ⌜m⌝ + S ⌜n⌝ ≐ S(⌜m⌝ + ⌜n⌝)
| ax5 (m : Nat) : Thm <| ⌜m⌝  * 0 ≐ 0
| ax6 (m n : Nat) : Thm <| ⌜m⌝ * S ⌜n⌝ ≐ ⌜m⌝ * ⌜n⌝ + ⌜m⌝
| MP {φ ψ : Wff} : Thm φ → Thm (φ ⇒ ψ) → Thm ψ

example : Thm (⌜1⌝  + ⌜1⌝  ≐ ⌜2⌝ ) := by
  have h1 : Thm (⌜1⌝  + ⌜1⌝ ≐ S(⌜1⌝  + 0)) := Thm.ax4 1 0
  have h2 : Thm (⌜1⌝  + 0 ≐ ⌜1⌝ ) := Thm.ax3 1
  have h3 : Thm (S (⌜1⌝  + 0) ≐ ⌜2⌝) := by
    have h31 : Thm (S (⌜1⌝  + 0) ≐ S (⌜1⌝  + 0)) := Thm.refl
    apply Thm.ll (⌜1⌝  + 0) (⌜1⌝) h31 h2
    exact LL.eq (term_ll.refl) <| term_ll.succ term_ll.id
  apply Thm.ll (S (⌜1⌝  + 0)) (⌜2⌝) h1 h3
  exact LL.eq  (term_ll.refl) (term_ll.id)

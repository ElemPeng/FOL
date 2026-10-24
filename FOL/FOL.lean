
inductive Term where
| var : Nat → Term
| const : Nat → Term

deriving DecidableEq

structure Pset where
  set : List Term
  nodup : set.Nodup

instance : Membership Term Pset where
  mem t s := s ∈ t.set

def eqrel (x y : Pset) : Prop := x.set ⊆ y.set ∧ y.set ⊆ x.set

theorem eqrel_equiv : Equivalence eqrel := by
  constructor
  · intro x; unfold eqrel; simp
  · intro x y hxy; unfold eqrel at hxy ⊢; simp_all
  · intro x y z hxy hyz; unfold eqrel at hxy hyz ⊢; constructor
    · intro a ha; exact hyz.1 <| hxy.1 ha
    · intro a ha; exact hxy.2 <| hyz.2 ha

instance finset_setoid : Setoid Pset where
  r := eqrel
  iseqv := eqrel_equiv

def TermSet := Quotient finset_setoid

def TermSet.mk (s : Pset) : TermSet := Quotient.mk finset_setoid s

def TermSet.ofTerm (t : Term) : TermSet := TermSet.mk ⟨[t], by simp⟩

-- Thanks copilot
def Pset.vars (s : Pset) : Pset :=
  ⟨s.set.filter (fun t => match t with | .var _ => true | .const _ => false),
    s.nodup.filter _⟩

@[simp] theorem Pset.mem_vars (t : Term) (s : Pset) :
    t ∈ Pset.vars s ↔ t ∈ s ∧ ∃ n, t = .var n := by
  change t ∈ s.set.filter
      (fun t => match t with | .var _ => true | .const _ => false) ↔
    t ∈ s.set ∧ ∃ n, t = .var n
  cases t <;> simp

theorem Pset.vars_respects {x y : Pset} (h : eqrel x y) :
    eqrel (Pset.vars x) (Pset.vars y) := by
  unfold eqrel
  constructor
  · intro t ht
    change t ∈ (Pset.vars x).set at ht
    change t ∈ (Pset.vars y).set
    have ht' : t ∈ Pset.vars x := by change t ∈ (Pset.vars x).set; exact ht
    apply (Pset.mem_vars t y).2
    have ht' := (Pset.mem_vars t x).1 ht'
    exact ⟨h.1 ht'.1, ht'.2⟩
  · intro t ht
    change t ∈ (Pset.vars y).set at ht
    change t ∈ (Pset.vars x).set
    have ht' : t ∈ Pset.vars y := by change t ∈ (Pset.vars y).set; exact ht
    apply (Pset.mem_vars t x).2
    have ht' := (Pset.mem_vars t y).1 ht'
    exact ⟨h.2 ht'.1, ht'.2⟩

def TermSet.vars : TermSet → TermSet :=
  Quotient.lift
    (fun s => TermSet.mk (Pset.vars s))
    (by
      intro x y h
      apply Quotient.sound
      exact Pset.vars_respects h)

def Pset.union (x y : Pset) : Pset :=
  let right := y.set.filter fun t => decide (t ∉ x.set)
  have hright : right.Nodup := y.nodup.filter _
  have hdisjoint : ∀ a ∈ x.set, ∀ b ∈ right, a ≠ b := by
    intro a ha b hb hab
    have hb' : b ∉ x.set := by
      have hfilter := (List.mem_filter.mp hb).2
      simpa using hfilter
    exact hb' (hab ▸ ha)
  have hnodup : (x.set ++ right).Nodup := by
    rw [List.nodup_append]
    exact ⟨x.nodup, hright, hdisjoint⟩
  ⟨x.set ++ right, hnodup⟩

@[simp] theorem Pset.mem_union (t : Term) (x y : Pset) :
    t ∈ Pset.union x y ↔ t ∈ x ∨ t ∈ y := by
  change t ∈ x.set ++ y.set.filter (fun t => decide (t ∉ x.set)) ↔
    (t ∈ x.set ∨ t ∈ y.set)
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hx : t ∈ x.set
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩

theorem Pset.union_respects {x x' y y' : Pset}
    (hx : eqrel x x') (hy : eqrel y y') :
    eqrel (Pset.union x y) (Pset.union x' y') := by
  constructor
  · intro t ht
    change t ∈ Pset.union x y at ht
    change t ∈ Pset.union x' y'
    rw [Pset.mem_union] at ht ⊢
    rcases ht with h | h
    · exact Or.inl (hx.1 h)
    · exact Or.inr (hy.1 h)
  · intro t ht
    change t ∈ Pset.union x' y' at ht
    change t ∈ Pset.union x y
    rw [Pset.mem_union] at ht ⊢
    rcases ht with h | h
    · exact Or.inl (hx.2 h)
    · exact Or.inr (hy.2 h)

def TermSet.union : TermSet → TermSet → TermSet :=
  Quotient.lift₂
    (fun x y => Quotient.mk finset_setoid (Pset.union x y))
    (by
      intro x y x' y' hx hy
      apply Quotient.sound
      exact Pset.union_respects hx hy)

instance : Union TermSet where
  union := TermSet.union
-- end of what I let copilot write for me

abbrev TA := Nat → Bool

inductive Wff where
| eq : Term → Term → Wff
| pred : TermSet → Wff
| not : Wff → Wff
| imp : Wff → Wff → Wff

infix:63 "≐" => Wff.eq
prefix:60 "~" => Wff.not
infixr:55 "⇒" => Wff.imp

def Wff.FreeVars : Wff → TermSet
| x ≐ y => TermSet.ofTerm x ∪ TermSet.ofTerm y
| pred s => TermSet.vars s
| not p => p.FreeVars
| imp p q => p.FreeVars ∪ q.FreeVars

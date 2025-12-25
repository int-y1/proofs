import BBfLean.FM

/-!
# [7/15, 22/3, 6/77, 5/2, 9/5]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 1  1  0 -1 -1
-1  0  1  0  0
 0  2 -1  0  0
```

This is a sz20 machine that halts in 746 steps.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- TODO: Move into FM.lean
lemma step_stepNat_trans (n : ℕ) (h₁ : c₁ [fm]⊢ c₂) (h₂ : c₂ [fm]⊢^{n} c₃) :
    c₁ [fm]⊢^{n+1} c₃ := by
  rw [Nat.add_comm]
  exact stepNat_trans (c₂ := c₂) 1 n h₁ h₂

theorem fm_final : c₀ [fm]⊢^{746} ⟨0, 0, 0, 42, 0⟩ := by
  iterate 200 (refine step_stepNat_trans _ rfl ?_; simp only [Nat.succ_eq_add_one, Nat.reduceAdd])
  iterate 200 (refine step_stepNat_trans _ rfl ?_; simp only [Nat.succ_eq_add_one, Nat.reduceAdd])
  iterate 200 (refine step_stepNat_trans _ rfl ?_; simp only [Nat.succ_eq_add_one, Nat.reduceAdd])
  iterate 146 (refine step_stepNat_trans _ rfl ?_; simp only [Nat.succ_eq_add_one, Nat.reduceAdd])
  rfl

theorem fm_haltsIn_746 : haltsIn fm c₀ 746 := by
  simp only [haltsIn, fm_final, Option.some.injEq, exists_eq_left']
  rfl

theorem fm_halts : halts fm c₀ := ⟨_, fm_haltsIn_746⟩

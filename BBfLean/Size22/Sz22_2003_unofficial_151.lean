import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #151: [1/45, 25/77, 14/5, 3/14, 605/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0  2 -1 -1
 1  0 -1  1  0
-1  1  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_151

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

private theorem tuple_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ : ℕ}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) (h4 : d₁ = d₂) (h5 : e₁ = e₂) :
    (⟨a₁, b₁, c₁, d₁, e₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂, e₂⟩ := by
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

-- R3-R2 interleave (b=0): each pair does R3 then R2
-- Chain: (a, 0, c+1, 0, e+k) →* (a+k, 0, c+k+1, 0, e)
theorem r3r2_chain_b0 : ∀ k a c e,
    ⟨a, 0, c+1, 0, e+k⟩ [fm]⊢* ⟨a+k, (0:ℕ), c+k+1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show (⟨a + 1, 0, c + 2, 0, e + k⟩ : Q) = ⟨a + 1, 0, (c+1) + 1, 0, e + k⟩
      from tuple_eq rfl rfl (by ring) rfl rfl]
    apply stepStar_trans (ih (a + 1) (c + 1) e)
    rw [show (⟨a + 1 + k, 0, c + 1 + k + 1, 0, e⟩ : Q) = ⟨a + (k + 1), 0, c + (k + 1) + 1, 0, e⟩
      from tuple_eq (by ring) rfl (by ring) rfl rfl]
    finish

-- R3-R2 interleave (b=1): same pattern
-- Chain: (a, 1, c+1, 0, e+k) →* (a+k, 1, c+k+1, 0, e)
theorem r3r2_chain_b1 : ∀ k a c e,
    ⟨a, 1, c+1, 0, e+k⟩ [fm]⊢* ⟨a+k, (1:ℕ), c+k+1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show (⟨a + 1, 1, c + 2, 0, e + k⟩ : Q) = ⟨a + 1, 1, (c+1) + 1, 0, e + k⟩
      from tuple_eq rfl rfl (by ring) rfl rfl]
    apply stepStar_trans (ih (a + 1) (c + 1) e)
    rw [show (⟨a + 1 + k, 1, c + 1 + k + 1, 0, e⟩ : Q) = ⟨a + (k + 1), 1, c + (k + 1) + 1, 0, e⟩
      from tuple_eq (by ring) rfl (by ring) rfl rfl]
    finish

-- R3 chain (b=0, e=0): drains c, fills d
-- (a, 0, c+k, d, 0) →* (a+k, 0, c, d+k, 0)
theorem r3_chain_b0 : ∀ k a c d,
    ⟨a, 0, c+k, d, 0⟩ [fm]⊢* ⟨a+k, (0:ℕ), c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (d + 1))
    rw [show (⟨a + 1 + k, 0, c, d + 1 + k, 0⟩ : Q) = ⟨a + (k + 1), 0, c, d + (k + 1), 0⟩
      from tuple_eq (by ring) rfl rfl (by ring) rfl]
    finish

-- R3 chain (b=1, e=0): drains c, fills d
-- (a, 1, c+k, d, 0) →* (a+k, 1, c, d+k, 0)
theorem r3_chain_b1 : ∀ k a c d,
    ⟨a, 1, c+k, d, 0⟩ [fm]⊢* ⟨a+k, (1:ℕ), c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (d + 1))
    rw [show (⟨a + 1 + k, 1, c, d + 1 + k, 0⟩ : Q) = ⟨a + (k + 1), 1, c, d + (k + 1), 0⟩
      from tuple_eq (by ring) rfl rfl (by ring) rfl]
    finish

-- R4 chain (e=0): drains a and d, fills b
-- (a+k, b, 0, d+k, 0) →* (a, b+k, 0, d, 0)
theorem r4_chain : ∀ k a b d,
    ⟨a+k, b, 0, d+k, (0:ℕ)⟩ [fm]⊢* ⟨a, b+k, (0:ℕ), d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d)
    rw [show (⟨a, b + 1 + k, 0, d, 0⟩ : Q) = ⟨a, b + (k + 1), 0, d, 0⟩
      from tuple_eq rfl (by ring) rfl rfl rfl]
    finish

-- R5-R1 chain: each pair does R5 then R1
-- Chain: (a+k, b+2*k, 0, 0, e) →* (a, b, 0, 0, e+2*k)
theorem r5r1_chain : ∀ k a b e,
    ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, (0:ℕ), 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a b (e + 2))
    rw [show (⟨a, b, 0, 0, e + 2 + 2 * k⟩ : Q) = ⟨a, b, 0, 0, e + 2 * (k + 1)⟩
      from tuple_eq rfl rfl rfl rfl (by ring)]
    finish

-- Main transition: (a+1, 0, 0, 0, 2*e) →⁺ (a+2*e+1, 0, 0, 0, 2*e+6)
theorem main_trans (a e : ℕ) :
    ⟨a+1, 0, 0, 0, 2*e⟩ [fm]⊢⁺ ⟨a+2*e+1, (0:ℕ), 0, 0, 2*e+6⟩ := by
  -- Step 1 (R5): (a+1, 0, 0, 0, 2e) → (a, 0, 1, 0, 2e+2)
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 0, 0, 0, 2*e⟩ = some ⟨a, 0, 1, 0, 2*e+2⟩; simp [fm]
  -- Phase A: R3-R2 interleave b=0, (2e+2) pairs
  apply stepStar_trans
  · have h := r3r2_chain_b0 (2*e+2) a 0 0
    rw [show (⟨a, 0, 0+1, 0, 0+(2*e+2)⟩ : Q) = ⟨a, 0, 1, 0, 2*e+2⟩
      from tuple_eq rfl rfl (by ring) rfl (by ring),
        show (⟨a+(2*e+2), 0, 0+(2*e+2)+1, 0, 0⟩ : Q) = ⟨a+2*e+2, 0, 2*e+3, 0, 0⟩
      from tuple_eq (by ring) rfl (by ring) rfl rfl] at h
    exact h
  -- Phase B: R3 chain b=0, (2e+3) steps
  apply stepStar_trans
  · have h := r3_chain_b0 (2*e+3) (a+2*e+2) 0 0
    rw [show (⟨a+2*e+2, 0, 0+(2*e+3), 0, 0⟩ : Q) = ⟨a+2*e+2, 0, 2*e+3, 0, 0⟩
      from tuple_eq rfl rfl (by ring) rfl rfl,
        show (⟨(a+2*e+2)+(2*e+3), 0, 0, 0+(2*e+3), 0⟩ : Q) = ⟨a+4*e+5, 0, 0, 2*e+3, 0⟩
      from tuple_eq (by ring) rfl rfl (by ring) rfl] at h
    exact h
  -- Phase C: R4 chain, (2e+3) steps
  apply stepStar_trans
  · have h := r4_chain (2*e+3) (a+2*e+2) 0 0
    rw [show (⟨(a+2*e+2)+(2*e+3), 0, 0, 0+(2*e+3), 0⟩ : Q) = ⟨a+4*e+5, 0, 0, 2*e+3, 0⟩
      from tuple_eq (by ring) rfl rfl (by ring) rfl,
        show (⟨a+2*e+2, 0+(2*e+3), 0, 0, 0⟩ : Q) = ⟨a+2*e+2, 2*e+3, 0, 0, 0⟩
      from tuple_eq rfl (by ring) rfl rfl rfl] at h
    exact h
  -- Phase D: R5-R1 drain, e pairs
  apply stepStar_trans
  · have h := r5r1_chain e (a+e+2) 3 0
    rw [show (⟨(a+e+2)+e, 3+2*e, 0, 0, 0⟩ : Q) = ⟨a+2*e+2, 2*e+3, 0, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl rfl,
        show (⟨a+e+2, 3, 0, 0, 0+2*e⟩ : Q) = ⟨a+e+2, 3, 0, 0, 2*e⟩
      from tuple_eq rfl rfl rfl rfl (by ring)] at h
    exact h
  -- R5-R1-R5: (a+e+2, 3, 0, 0, 2e)
  step fm; step fm; step fm
  -- Now at (a+e, 1, 1, 0, 2e+4)
  -- Phase A': R3-R2 interleave b=1, (2e+4) pairs
  apply stepStar_trans
  · have h := r3r2_chain_b1 (2*e+4) (a+e) 0 0
    rw [show (⟨a+e, 1, 0+1, 0, 0+(2*e+4)⟩ : Q) = ⟨a+e, 1, 1, 0, 2*e+4⟩
      from tuple_eq rfl rfl (by ring) rfl (by ring),
        show (⟨(a+e)+(2*e+4), 1, 0+(2*e+4)+1, 0, 0⟩ : Q) = ⟨a+3*e+4, 1, 2*e+5, 0, 0⟩
      from tuple_eq (by ring) rfl (by ring) rfl rfl] at h
    exact h
  -- Phase B': R3 chain b=1, (2e+5) steps
  apply stepStar_trans
  · have h := r3_chain_b1 (2*e+5) (a+3*e+4) 0 0
    rw [show (⟨a+3*e+4, 1, 0+(2*e+5), 0, 0⟩ : Q) = ⟨a+3*e+4, 1, 2*e+5, 0, 0⟩
      from tuple_eq rfl rfl (by ring) rfl rfl,
        show (⟨(a+3*e+4)+(2*e+5), 1, 0, 0+(2*e+5), 0⟩ : Q) = ⟨a+5*e+9, 1, 0, 2*e+5, 0⟩
      from tuple_eq (by ring) rfl rfl (by ring) rfl] at h
    exact h
  -- Phase C': R4 chain, (2e+5) steps
  apply stepStar_trans
  · have h := r4_chain (2*e+5) (a+3*e+4) 1 0
    rw [show (⟨(a+3*e+4)+(2*e+5), 1, 0, 0+(2*e+5), 0⟩ : Q) = ⟨a+5*e+9, 1, 0, 2*e+5, 0⟩
      from tuple_eq (by ring) rfl rfl (by ring) rfl,
        show (⟨a+3*e+4, 1+(2*e+5), 0, 0, 0⟩ : Q) = ⟨a+3*e+4, 2*e+6, 0, 0, 0⟩
      from tuple_eq rfl (by ring) rfl rfl rfl] at h
    exact h
  -- Phase D': R5-R1 drain, (e+2) pairs
  apply stepStar_trans
  · have h := r5r1_chain (e+2) (a+2*e+2) 2 0
    rw [show (⟨(a+2*e+2)+(e+2), 2+2*(e+2), 0, 0, 0⟩ : Q) = ⟨a+3*e+4, 2*e+6, 0, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl rfl,
        show (⟨a+2*e+2, 2, 0, 0, 0+2*(e+2)⟩ : Q) = ⟨a+2*e+2, 2, 0, 0, 2*e+4⟩
      from tuple_eq rfl rfl rfl rfl (by ring)] at h
    exact h
  -- Final R5-R1: (a+2e+2, 2, 0, 0, 2e+4)
  step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · finish
  apply progress_nonhalt_simple (A := ℕ × ℕ) (C := fun p ↦ (⟨p.1+1, 0, 0, 0, 2*p.2⟩ : Q))
    (i₀ := ⟨0, 0⟩)
  intro ⟨a, e⟩
  exact ⟨⟨a+2*e, e+3⟩, by
    show ⟨a+1, 0, 0, 0, 2*e⟩ [fm]⊢⁺ ⟨(a+2*e)+1, (0:ℕ), 0, 0, 2*(e+3)⟩
    rw [show 2*(e+3) = 2*e+6 from by ring,
        show (a+2*e)+1 = a+2*e+1 from by ring]
    exact main_trans a e⟩

end Sz22_2003_unofficial_151

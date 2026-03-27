import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #132: [1/45, 14/5, 25/77, 3/14, 605/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0 -1  1  0
 0  0  2 -1 -1
-1  1  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_132

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- R2/R3 triple chain with b=0: each (R2,R2,R3) triple adds 2 to a, 1 to d, subtracts 1 from e
theorem r23_chain_b0 : ∀ k a d e, ⟨a, 0, 2, d, e+k⟩ [fm]⊢* ⟨a+2*k, (0 : ℕ), 2, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; simp; exists 0
  | succ k ih =>
    intro a d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm -- R2
    step fm -- R2
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm -- R3
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2/R3 triple chain with b=1
theorem r23_chain_b1 : ∀ k a d e, ⟨a, 1, 2, d, e+k⟩ [fm]⊢* ⟨a+2*k, (1 : ℕ), 2, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; simp; exists 0
  | succ k ih =>
    intro a d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm -- R2
    step fm -- R2
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm -- R3
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Full spiral with b=0: (a, 0, 1, 0, E+1) →* (a+2E+3, 0, 0, E+2, 0)
theorem spiral_b0 : ∀ a E, ⟨a, 0, 1, 0, E+1⟩ [fm]⊢* ⟨a+2*E+3, (0 : ℕ), (0 : ℕ), E+2, (0 : ℕ)⟩ := by
  intro a E
  -- R2: (a, 0, 1, 0, E+1) → (a+1, 0, 0, 1, E+1)
  step fm
  -- R3: (a+1, 0, 0, 1, E+1) → (a+1, 0, 2, 0, E)
  rw [show E + 1 = E + 1 from rfl]
  step fm
  -- r23_chain_b0 E: (a+1, 0, 2, 0, 0+E) →* (a+1+2E, 0, 2, E, 0)
  apply stepStar_trans (c₂ := ⟨a+1+2*E, 0, 2, E, 0⟩)
  · have h := r23_chain_b0 E (a+1) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- R2: (a+1+2E, 0, 2, E, 0) → (a+2+2E, 0, 1, E+1, 0)
  step fm
  -- R2: (a+2+2E, 0, 1, E+1, 0) → (a+3+2E, 0, 0, E+2, 0)
  step fm
  ring_nf; finish

-- Full spiral with b=1: (a, 1, 1, 0, E+1) →* (a+2E+3, 1, 0, E+2, 0)
theorem spiral_b1 : ∀ a E, ⟨a, 1, 1, 0, E+1⟩ [fm]⊢* ⟨a+2*E+3, (1 : ℕ), (0 : ℕ), E+2, (0 : ℕ)⟩ := by
  intro a E
  step fm
  rw [show E + 1 = E + 1 from rfl]
  step fm
  apply stepStar_trans (c₂ := ⟨a+1+2*E, 1, 2, E, 0⟩)
  · have h := r23_chain_b1 E (a+1) 0 0
    simp only [Nat.zero_add] at h
    exact h
  step fm
  step fm
  ring_nf; finish

-- R4 chain: d → b (when c=0, e=0)
theorem d_to_b : ∀ k a b d, ⟨a+k, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, (0 : ℕ), d, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5/R1 drain: (a+k, b+2k, 0, 0, e) →* (a, b, 0, 0, e+2k)
theorem drain : ∀ k a b e, ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, (0 : ℕ), (0 : ℕ), e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a b e; simp; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
    step fm -- R5
    rw [show b + 2 * k + 1 + 1 = (b + 2 * k) + 1 + 1 from by ring]
    step fm -- R1
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, 2f+2) ⊢⁺ (a+2f+3, 0, 0, 0, 2f+8)
theorem main_trans (a f : ℕ) : ⟨a+1, 0, 0, 0, 2*f+2⟩ [fm]⊢⁺ ⟨a+2*f+3, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2*f+8⟩ := by
  -- Phase 1: R5: (a+1, 0, 0, 0, 2f+2) → (a, 0, 1, 0, 2f+4)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 1, 0, 2*f+4⟩)
  · simp [fm]
  -- Phase 2: spiral_b0 with E = 2f+3:
  -- (a, 0, 1, 0, (2f+3)+1) →* (a+2(2f+3)+3, 0, 0, (2f+3)+2, 0) = (a+4f+9, 0, 0, 2f+5, 0)
  apply stepStar_trans (c₂ := ⟨a+4*f+9, 0, 0, 2*f+5, 0⟩)
  · have h := spiral_b0 a (2*f+3)
    rw [show 2 * f + 3 + 1 = 2 * f + 4 from by ring,
        show a + 2 * (2 * f + 3) + 3 = a + 4 * f + 9 from by ring,
        show 2 * f + 3 + 2 = 2 * f + 5 from by ring] at h
    exact h
  -- Phase 3: d_to_b with k = 2f+5:
  -- (a+4f+9, 0, 0, 2f+5, 0) →* (a+4f+9-(2f+5), 2f+5, 0, 0, 0) = (a+2f+4, 2f+5, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+2*f+4, 2*f+5, 0, 0, 0⟩)
  · have h := d_to_b (2*f+5) (a+2*f+4) 0 0
    rw [show a + 2 * f + 4 + (2 * f + 5) = a + 4 * f + 9 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 4: drain with k = f+2:
  -- (a+2f+4, 2f+5, 0, 0, 0) →* (a+f+2, 1, 0, 0, 2f+4)
  apply stepStar_trans (c₂ := ⟨a+f+2, 1, 0, 0, 2*f+4⟩)
  · have h := drain (f+2) (a+f+2) 1 0
    rw [show a + f + 2 + (f + 2) = a + 2 * f + 4 from by ring,
        show 1 + 2 * (f + 2) = 2 * f + 5 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 5: R5: (a+f+2, 1, 0, 0, 2f+4) → (a+f+1, 1, 1, 0, 2f+6)
  apply stepStar_trans (c₂ := ⟨a+f+1, 1, 1, 0, 2*f+6⟩)
  · rw [show a + f + 2 = (a + f + 1) + 1 from by ring]
    step fm
    rw [show 2 * f + 4 + 2 = 2 * f + 6 from by ring]
    finish
  -- Phase 6: spiral_b1 with E = 2f+5:
  -- (a+f+1, 1, 1, 0, (2f+5)+1) →* (a+f+1+2(2f+5)+3, 1, 0, (2f+5)+2, 0) = (a+5f+14, 1, 0, 2f+7, 0)
  apply stepStar_trans (c₂ := ⟨a+5*f+14, 1, 0, 2*f+7, 0⟩)
  · have h := spiral_b1 (a+f+1) (2*f+5)
    rw [show 2 * f + 5 + 1 = 2 * f + 6 from by ring,
        show a + f + 1 + 2 * (2 * f + 5) + 3 = a + 5 * f + 14 from by ring,
        show 2 * f + 5 + 2 = 2 * f + 7 from by ring] at h
    exact h
  -- Phase 7: d_to_b with k = 2f+7:
  -- (a+5f+14, 1, 0, 2f+7, 0) →* (a+3f+7, 2f+8, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+3*f+7, 2*f+8, 0, 0, 0⟩)
  · have h := d_to_b (2*f+7) (a+3*f+7) 1 0
    rw [show a + 3 * f + 7 + (2 * f + 7) = a + 5 * f + 14 from by ring,
        show 1 + (2 * f + 7) = 2 * f + 8 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 8: drain with k = f+4:
  -- (a+3f+7, 2f+8, 0, 0, 0) →* (a+2f+3, 0, 0, 0, 2f+8)
  · have h := drain (f+4) (a+2*f+3) 0 0
    rw [show a + 2 * f + 3 + (f + 4) = a + 3 * f + 7 from by ring,
        show 0 + 2 * (f + 4) = 2 * f + 8 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 6⟩) (by execute fm 38)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, f⟩ ↦ ⟨a+1, 0, 0, 0, 2*f+2⟩) ⟨0, 2⟩
  intro ⟨a, f⟩
  refine ⟨⟨a+2*f+2, f+3⟩, ?_⟩
  show ⟨a+1, 0, 0, 0, 2*f+2⟩ [fm]⊢⁺ ⟨a+2*f+2+1, 0, 0, 0, 2*(f+3)+2⟩
  rw [show a + 2 * f + 2 + 1 = a + 2 * f + 3 from by ring,
      show 2 * (f + 3) + 2 = 2 * f + 8 from by ring]
  exact main_trans a f

end Sz22_2003_unofficial_132

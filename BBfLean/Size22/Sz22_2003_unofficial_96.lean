import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #96: [1/30, 245/3, 3/77, 4/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0 -1  1  2  0
 0  1  0 -1 -1
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_96

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3/R2 interleaved chain:
-- (0, 0, c, c+1, m+1) -R3-> (0, 1, c, c, m) -R2-> (0, 0, c+1, c+2, m)
theorem r3r2_chain : ∀ m c, ⟨0, 0, c, c+1, m⟩ [fm]⊢* ⟨0, 0, c+m, c+1+m, 0⟩ := by
  intro m; induction' m with m h <;> intro c
  · exists 0
  rw [show c + (m + 1) = (c + m) + 1 from by ring,
      show c + 1 + (m + 1) = (c + 1) + 1 + m from by ring]
  step fm; step fm
  apply stepStar_trans (h (c + 1))
  ring_nf; finish

-- R4 chain: drain d, adding 2 to a per step
theorem r4_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a+2*k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show (a : ℕ) + 2 * (k + 1) = (a + 2) + 2 * k from by ring]
  step fm
  exact h (a + 2) c

-- R5/R1 interleaved chain:
-- (a+2, 0, c+1, 0, e) -R5-> (a+1, 1, c+1, 0, e+2) -R1-> (a, 0, c, 0, e+2)
theorem r5r1_chain : ∀ k a e, ⟨a+2*k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (h a (e + 2))
  ring_nf; finish

-- Main transition: (2, 0, 0, 0, e) ⊢⁺ (2, 0, 0, 0, 2*e+2)
theorem main_trans (e : ℕ) : ⟨2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 2*e+2⟩ := by
  -- Opening: 4 steps to (0, 0, 0, 1, e+1)
  apply step_stepStar_stepPlus
    (c₂ := ⟨1, 1, 0, 0, e+2⟩)
  · show fm ⟨1+1, 0, 0, 0, e⟩ = some ⟨1, 0+1, 0, 0, e+2⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨1, 0, 1, 2, e+2⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 1, e+1⟩)
  · rw [show (e : ℕ) + 2 = (e + 1) + 1 from by ring]
    step fm; step fm; finish
  -- R3/R2 chain: (0, 0, 0, 1, e+1) →* (0, 0, e+1, e+2, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, e+1, e+2, 0⟩)
  · have h := r3r2_chain (e+1) 0
    simp only [Nat.zero_add] at h
    rw [show (0 : ℕ) + 1 + (e + 1) = e + 2 from by ring] at h
    exact h
  -- R4 chain: (0, 0, e+1, e+2, 0) →* (2*e+4, 0, e+1, 0, 0)
  apply stepStar_trans (c₂ := ⟨2*e+4, 0, e+1, 0, 0⟩)
  · have h := r4_chain (e+2) 0 (e+1)
    simp only [Nat.zero_add] at h
    rw [show 2 * (e + 2) = 2 * e + 4 from by ring] at h
    exact h
  -- R5/R1 chain: (2*e+4, 0, e+1, 0, 0) →* (2, 0, 0, 0, 2*e+2)
  have h := r5r1_chain (e+1) 2 0
  simp only [Nat.zero_add] at h
  rw [show 2 + 2 * (e + 1) = 2 * e + 4 from by ring,
      show 2 * (e + 1) = 2 * e + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 6⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨2, 0, 0, 0, e⟩) 6
  intro e; exact ⟨2*e+2, main_trans e⟩

end Sz22_2003_unofficial_96

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #538: [28/15, 9/22, 175/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  2  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_538

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 repeated
theorem r3_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 repeated
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2,R1,R1 chain
theorem r2r1r1_chain : ∀ k, ∀ j c e,
    ⟨3 * j + 2, 0, c + 2 * k, 2 * j + 1, e + k⟩ [fm]⊢*
    ⟨3 * (j + k) + 2, 0, c, 2 * (j + k) + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro j c e
  · ring_nf; exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring,
      show 3 * j + 2 = (3 * j + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl, show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  rw [show 3 * j + 1 + 2 = (3 * j + 3) from by ring,
      show c + 2 * k = c + 2 * k from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans (ih (j + 1) c e)
  ring_nf; finish

-- R2 repeated
theorem r2_chain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3,R1,R1 chain
theorem r3r1r1_chain : ∀ k, ∀ a d, ⟨a + 1, 2 * k, 0, d, 0⟩ [fm]⊢*
    ⟨a + 3 * k + 1, 0, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · ring_nf; exists 0
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl, show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a + 3) (d + 3))
  ring_nf; finish

-- Main transition: (a+4, 0, 0, d+4, 0) →⁺ (3a+2d+21, 0, 0, 2a+3d+22, 0)
theorem main_trans {a d : ℕ} (ha : 3 * (a + 4) ≥ (d + 4) + 5) :
    ⟨a + 4, 0, 0, d + 4, 0⟩ [fm]⊢⁺ ⟨3 * a + 2 * d + 21, 0, 0, 2 * a + 3 * d + 22, 0⟩ := by
  have h1 := r3_chain (a + 4) 0 0 (d + 4)
  rw [Nat.zero_add, show 0 + 2 * (a + 4) = 2 * (a + 4) from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show d + 4 + (a + 4) = 0 + (d + a + 8) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d + a + 8) (2 * (a + 4)) 0 0)
  simp only [Nat.zero_add]
  rw [show 2 * (a + 4) = (2 * a + 6 + 1) + 1 from by ring,
      show (d + a + 8 : ℕ) = (d + a + 7) + 1 from by ring]
  step fm; step fm
  have h4 := r2r1r1_chain (a + 3) 0 0 (d + 5)
  rw [show 3 * 0 + 2 = 2 from by ring,
      show 0 + 2 * (a + 3) = 2 * a + 6 from by ring,
      show 2 * 0 + 1 = 1 from by ring,
      show d + 5 + (a + 3) = d + a + 8 from by ring,
      Nat.zero_add,
      show 3 * (a + 3) + 2 = 3 * a + 11 from by ring,
      show 2 * (a + 3) + 1 = 2 * a + 7 from by ring] at h4
  rw [show d + a + 7 + 1 = d + a + 8 from by ring]
  apply stepStar_trans h4
  obtain ⟨m, hm⟩ : ∃ m, 3 * a + 11 = (m + 1) + (d + 5) := ⟨3 * a + 11 - (d + 5) - 1, by omega⟩
  have h5 := r2_chain (d + 5) (m + 1) 0 (2 * a + 7)
  rw [← hm, show 0 + 2 * (d + 5) = 2 * (d + 5) from by ring] at h5
  apply stepStar_trans h5
  have h6 := r3r1r1_chain (d + 5) m (2 * a + 7)
  rw [show m + 3 * (d + 5) + 1 = 3 * a + 2 * d + 21 from by omega,
      show 2 * a + 7 + 3 * (d + 5) = 2 * a + 3 * d + 22 from by ring] at h6
  exact h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 4, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 4, 0, 0, d + 4, 0⟩ ∧ 3 * (a + 4) ≥ (d + 4) + 5)
  · intro c ⟨a, d, hq, hinv⟩
    subst hq
    refine ⟨⟨3 * a + 2 * d + 21, 0, 0, 2 * a + 3 * d + 22, 0⟩, ?_, main_trans hinv⟩
    exact ⟨3 * a + 2 * d + 17, 2 * a + 3 * d + 18, by ring_nf, by omega⟩
  · exact ⟨0, 0, by ring_nf, by omega⟩

end Sz22_2003_unofficial_538

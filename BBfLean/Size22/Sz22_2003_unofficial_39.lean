import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #39: [1/15, 4/3, 9/154, 35/2, 363/5]

Vector representation:
```
 0 -1 -1  0  0
 2 -1  0  0  0
-1  2  0 -1 -1
-1  0  1  1  0
 0  1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_39

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R4 chain (e=0 ensures R3 doesn't fire)
theorem r4_chain : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R5,R1 chain for odd c
theorem r5r1_chain : ∀ k d e, ⟨0, 0, 2*k+1, d, e⟩ [fm]⊢* ⟨0, 1, 0, d, e+2*(k+1)⟩ := by
  intro k; induction' k with k h <;> intro d e
  · step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R3,R2,R2 chain: each round a += 3, d -= 1, e -= 1
theorem r3r2r2_chain : ∀ k a d e, ⟨a+1, 0, 0, d+k, e+k+1⟩ [fm]⊢* ⟨a+3*k+1, 0, 0, d, e+1⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h (a+3) _ _); ring_nf; finish

-- Main transition: (2m+1, 0, 0, 0, 0) ->+ (6m+5, 0, 0, 0, 0)
theorem main_trans (m : ℕ) : ⟨2*m+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*m+5, 0, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2*m+1) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1_chain m (2*m+1) 0
    simp only [Nat.zero_add, (by ring : 2 * (m + 1) = 2 * m + 2)] at h; exact h
  step fm
  apply stepStar_trans
  · have h := r3r2r2_chain (2*m+1) 1 0 0
    simp only [Nat.zero_add, (by ring : 1 + 1 = 2),
               (by ring : 1 + 3 * (2 * m + 1) + 1 = 6 * m + 5)] at h; exact h
  show ⟨6 * m + 5, 0, 0, 0, 1⟩ [fm]⊢* ⟨6 * m + 5, 0, 0, 0, 0⟩
  rw [show 6 * m + 5 = (6 * m + 4) + 1 from by ring]
  step fm
  rw [show 6 * m + 4 = (6 * m + 3) + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun m ↦ ⟨2*m+1, 0, 0, 0, 0⟩) 2
  intro m; exists (3*m+2)
  show ⟨2 * m + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * (3 * m + 2) + 1, 0, 0, 0, 0⟩
  rw [show 2 * (3 * m + 2) + 1 = 6 * m + 5 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_39

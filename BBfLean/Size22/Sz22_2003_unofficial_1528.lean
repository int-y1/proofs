import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1528: [7/30, 15/77, 121/3, 4/11, 21/2]

Vector representation:
```
-1 -1 -1  1  0
 0  1  1 -1 -1
 0 -1  0  0  2
 2  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1528

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3r2r2_chain : ∀ k, ∀ b c d,
    ⟨0, b + 1, c, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b + k + 1, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 1) (c + 2) d); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih c (e + 2)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) c); ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ a c d,
    ⟨a + 2 * k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 2 * n + 3, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * n + 9, 0⟩ := by
  -- Phase 1: R5, R3
  step fm; step fm
  -- Phase 2: R2, R2
  rw [show 2 * n + 3 + 1 = (2 * n + 2) + 2 from by ring]
  step fm; step fm
  -- Phase 3: R3R2R2 chain (n+1 rounds)
  rw [show 2 * n + 2 = 0 + 2 * (n + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (n + 1) 1 2 0)
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show 2 + 2 * (n + 1) = 2 * n + 4 from by ring]
  -- Phase 4: R3 drain (n+3 rounds)
  apply stepStar_trans (r3_drain (n + 3) (2 * n + 4) 0)
  rw [show 0 + 2 * (n + 3) = 2 * n + 6 from by ring]
  -- Phase 5: R4 chain (2*n+6 rounds)
  apply stepStar_trans (r4_chain (2 * n + 6) 0 (2 * n + 4))
  rw [show 0 + 2 * (2 * n + 6) = 4 * n + 12 from by ring]
  -- Phase 6: R5R1 chain (2*n+4 rounds)
  have h6 := r5r1_chain (2 * n + 4) 4 0 0
  rw [show 4 + 2 * (2 * n + 4) = 4 * n + 12 from by ring,
      show 0 + (2 * n + 4) = 2 * n + 4 from by ring,
      show 0 + 2 * (2 * n + 4) = 4 * n + 8 from by ring] at h6
  apply stepStar_trans h6
  -- Phase 7: Tail (6 steps)
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 3, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 2 * n + 3, 0⟩) 0
  intro n; exact ⟨2 * n + 3, by rw [show 2 * (2 * n + 3) + 3 = 4 * n + 9 from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_1528

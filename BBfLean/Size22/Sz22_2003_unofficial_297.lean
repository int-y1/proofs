import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #297: [15/2, 1/147, 26/33, 847/5, 3/91]

Vector representation:
```
-1  1  1  0  0  0
 0 -1  0 -2  0  0
 1 -1  0  0 -1  1
 0  0 -1  1  2  0
 0  1  0 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_297

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | ⟨a, b+1, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+2, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R1/R3 zigzag: drain e into c and f
theorem zigzag_chain : ∀ k c e f,
    ⟨1, 0, c, 0, e + k, f⟩ [fm]⊢* ⟨1, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  show ⟨0 + 1, 0, c, 0, (e + k) + 1, f⟩ [fm]⊢* _
  step fm
  show ⟨0, 0 + 1, c + 1, 0, (e + k) + 1, f⟩ [fm]⊢* _
  step fm
  have h := ih (c + 1) e (f + 1)
  rw [show c + 1 + k = c + (k + 1) from by ring,
      show f + 1 + k = f + (k + 1) from by ring] at h
  exact h

-- R4 chain: drain c into d and e
theorem r4_chain : ∀ k c d e f,
    ⟨0, 0, c + k, d, e, f⟩ [fm]⊢* ⟨0, 0, c, d + k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  show ⟨0, 0, (c + k) + 1, d, e, f⟩ [fm]⊢* _
  step fm
  have h := ih c (d + 1) (e + 2) f
  rw [show d + 1 + k = d + (k + 1) from by ring,
      show e + 2 + 2 * k = e + 2 * (k + 1) from by ring] at h
  exact h

-- R5/R2 chain: each pair removes d by 3, f by 1
theorem r5r2_chain : ∀ k d e f,
    ⟨0, 0, 0, d + 3 * k, e, f + k⟩ [fm]⊢* ⟨0, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  rw [show d + 3 * (k + 1) = (d + 3 * k) + (2 + 1) from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  show ⟨0, 0, 0, (d + 3 * k) + (2 + 1), e, (f + k) + 1⟩ [fm]⊢* _
  step fm
  show ⟨0, 0 + 1, 0, (d + 3 * k) + 2, e, f + k⟩ [fm]⊢* _
  step fm
  exact ih d e f

-- Main cycle
theorem main_cycle (n : ℕ) :
    ⟨1, 0, 0, 0, 3 * n + 3, 2 * n + 2⟩ [fm]⊢⁺
    ⟨1, 0, 0, 0, 6 * n + 9, 4 * n + 6⟩ := by
  -- Phase 1: zigzag (3n+3) pairs of R1/R3
  -- (1, 0, 0, 0, 3n+3, 2n+2) →* (1, 0, 3n+3, 0, 0, 5n+5)
  have h1 := zigzag_chain (3 * n + 3) 0 0 (2 * n + 2)
  simp only [Nat.zero_add] at h1
  rw [show 2 * n + 2 + (3 * n + 3) = 5 * n + 5 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2+3: 8 explicit steps
  -- (1, 0, 3n+3, 0, 0, 5n+5) → ... → (0, 0, 3n+4, 0, 2, 5n+7)
  show ⟨0 + 1, 0, 3 * n + 3, 0, 0, 5 * n + 5⟩ [fm]⊢⁺ _
  step fm -- R1
  show ⟨0, 0 + 1, (3 * n + 3) + 1, 0, 0, 5 * n + 5⟩ [fm]⊢* _
  step fm -- R4
  show ⟨0, 0 + 1, 3 * n + 3, 1, 0 + 2, 5 * n + 5⟩ [fm]⊢* _
  step fm -- R3
  show ⟨0 + 1, 0, 3 * n + 3, 1, 1, (5 * n + 5) + 1⟩ [fm]⊢* _
  step fm -- R1
  show ⟨0, 0 + 1, (3 * n + 3) + 1, 1, 0 + 1, (5 * n + 5) + 1⟩ [fm]⊢* _
  step fm -- R3
  show ⟨0 + 1, 0, (3 * n + 3) + 1, 1, 0, (5 * n + 5) + 2⟩ [fm]⊢* _
  step fm -- R1
  show ⟨0, 0 + 1, ((3 * n + 3) + 1) + 1, 1, 0, (5 * n + 5) + 2⟩ [fm]⊢* _
  step fm -- R4
  show ⟨0, 0 + 1, (3 * n + 3) + 1, 0 + 2, 0 + 2, (5 * n + 5) + 2⟩ [fm]⊢* _
  step fm -- R2
  -- Now at (0, 0, 3n+4, 0, 2, 5n+7)
  -- Phase 4: R4 chain to drain c
  -- (0, 0, 3n+4, 0, 2, 5n+7) →* (0, 0, 0, 3n+4, 6n+10, 5n+7)
  have h4 := r4_chain (3 * n + 4) 0 0 2 (5 * n + 7)
  simp only [Nat.zero_add] at h4
  rw [show 2 + 2 * (3 * n + 4) = 6 * n + 10 from by ring] at h4
  apply stepStar_trans h4
  -- Phase 5: R5/R2 chain
  -- (0, 0, 0, 3n+4, 6n+10, 5n+7) →* (0, 0, 0, 1, 6n+10, 4n+6)
  have h5 := r5r2_chain (n + 1) 1 (6 * n + 10) (4 * n + 6)
  rw [show 1 + 3 * (n + 1) = 3 * n + 4 from by ring,
      show 4 * n + 6 + (n + 1) = 5 * n + 7 from by ring] at h5
  apply stepStar_trans h5
  -- Phase 6: R5 then R3
  -- (0, 0, 0, 1, 6n+10, 4n+6) → (0, 1, 0, 0, 6n+10, 4n+5) → (1, 0, 0, 0, 6n+9, 4n+6)
  show ⟨0, 0, 0, 0 + 1, 6 * n + 10, (4 * n + 5) + 1⟩ [fm]⊢* _
  step fm -- R5
  show ⟨0, 0 + 1, 0, 0, (6 * n + 9) + 1, 4 * n + 5⟩ [fm]⊢* _
  step fm -- R3
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3, 2⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, 0, 0, 3 * n + 3, 2 * n + 2⟩) 0
  intro n
  exact ⟨2 * n + 2, by
    rw [show 3 * (2 * n + 2) + 3 = 6 * n + 9 from by ring,
        show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
    exact main_cycle n⟩

end Sz22_2003_unofficial_297

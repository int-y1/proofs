import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1132: [5/6, 44/35, 49/2, 3/11, 18/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 1  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1132

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k, ∀ b D e, ⟨0, b, 0, D, e + k⟩ [fm]⊢* ⟨0, b + k, 0, D, e⟩ := by
  intro k; induction' k with k ih <;> intro b D e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) D e)
    ring_nf; finish

-- R3 chain: drain a to d
theorem drain_a : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

-- R2 chain: consume c and d, produce a and e
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- Interleaved R2,R1,R1 chain: k rounds
-- Each round: (0, 2j+3, c+1, d+1, e) -R2-> (2, 2j+3, c, d, e+1)
--             -R1-> (1, 2j+2, c+1, d, e+1) -R1-> (0, 2j+1, c+2, d, e+1)
theorem interleave :
    ∀ k, ∀ c d e, ⟨0, 2 * k + 1, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 1, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- Middle phase: interleave + R2 + R1 + r2_chain
-- From (0, 2m+3, 1, m²+4m+4, 0) to (2m+5, 0, 0, m²+2m, 2m+4)
theorem middle (m : ℕ) :
    ⟨0, 2*m+3, 1, m*m+4*m+4, 0⟩ [fm]⊢* ⟨2*m+5, 0, 0, m*m+2*m, 2*m+4⟩ := by
  rw [show m * m + 4 * m + 4 = (m * m + 3 * m + 3) + (m + 1) from by ring]
  apply stepStar_trans (interleave (m + 1) 0 (m * m + 3 * m + 3) 0)
  simp only [Nat.zero_add]
  rw [show m * m + 3 * m + 3 = (m * m + 3 * m + 2) + 1 from by ring]
  step fm
  step fm
  have h := r2_chain (m + 2) 1 0 (m * m + 2 * m) (m + 2)
  simp only [Nat.zero_add] at h
  rw [show m * m + 3 * m + 2 = m * m + 2 * m + (m + 2) from by ring]
  apply stepStar_trans h
  ring_nf; finish

-- Main transition for n ≥ 1: C(m+1) ⊢⁺ C(m+2)
-- C(m+1) = (0, 0, 0, m²+4m+5, 2m+2)
-- C(m+2) = (0, 0, 0, m²+6m+10, 2m+4)
theorem main_trans_ge1 (m : ℕ) :
    ⟨0, 0, 0, m * m + 4 * m + 5, 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, m * m + 6 * m + 10, 2 * m + 4⟩ := by
  rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 2) 0 (m * m + 4 * m + 5) 0)
  simp only [Nat.zero_add]
  rw [show m * m + 4 * m + 5 = (m * m + 4 * m + 4) + 1 from by ring]
  step fm  -- R5: (0, 2m+2, 0, D+1, 0) → (1, 2m+4, 0, D, 0)
  step fm  -- R1: (1, 2m+4, 0, D, 0) → (0, 2m+3, 1, D, 0)
  apply stepStar_trans (middle m)
  rw [show (2 * m + 5 : ℕ) = 0 + (2 * m + 5) from by ring]
  apply stepStar_trans (drain_a (2 * m + 5) 0 (m * m + 2 * m) (2 * m + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n * n + 2 * n + 2, 2 * n⟩) 0
  intro n
  rcases n with _ | m
  · exact ⟨1, by execute fm 8⟩
  · refine ⟨m + 2, ?_⟩
    show ⟨0, 0, 0, (m + 1) * (m + 1) + 2 * (m + 1) + 2, 2 * (m + 1)⟩ [fm]⊢⁺
         ⟨0, 0, 0, (m + 2) * (m + 2) + 2 * (m + 2) + 2, 2 * (m + 2)⟩
    rw [show (m + 1) * (m + 1) + 2 * (m + 1) + 2 = m * m + 4 * m + 5 from by ring,
        show 2 * (m + 1) = 2 * m + 2 from by ring,
        show (m + 2) * (m + 2) + 2 * (m + 2) + 2 = m * m + 6 * m + 10 from by ring,
        show 2 * (m + 2) = 2 * m + 4 from by ring]
    exact main_trans_ge1 m

end Sz22_2003_unofficial_1132

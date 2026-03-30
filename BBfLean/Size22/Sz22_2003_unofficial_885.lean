import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #885: [4/15, 147/2, 11/3, 5/77, 1/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2  0
 0 -1  0  0  1
 0  0  1 -1 -1
 0  0  0  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_885

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2 chain: drain a into b, doubling into d.
theorem a_to_b : ∀ k, ∀ a b D, ⟨a + k, b, 0, D, 0⟩ [fm]⊢* ⟨a, b + k, 0, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b D
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (D + 2))
    ring_nf; finish

-- R3 chain: drain b into e.
theorem b_to_e : ∀ k, ∀ b D e, ⟨0, b + k, 0, D, e⟩ [fm]⊢* ⟨0, b, 0, D, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b D e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b D (e + 1))
    ring_nf; finish

-- R4 chain: pair d,e into c.
theorem de_to_c : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2+R1 chain: (a+2, 0, c, d, 0) →* (a+2+c, 0, 0, d+2*c, 0)
theorem r2r1_chain : ∀ c, ∀ a d, ⟨a + 2, 0, c, d, 0⟩ [fm]⊢* ⟨a + 2 + c, 0, 0, d + 2 * c, 0⟩ := by
  intro c; induction' c with c ih <;> intro a d
  · exists 0
  · rw [show (c : ℕ) + 1 = c + 1 from by ring,
        show a + 2 = (a + 1) + 1 from by ring]
    step fm
    step fm
    rw [show a + 1 + 2 = (a + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- Phase 4: (0, 0, c+1, d+1, 0) →* (c+2, 0, 0, d+2*c, 0)
theorem interleaved : ∀ c, ∀ d, ⟨0, 0, c + 1, d + 1, 0⟩ [fm]⊢* ⟨c + 2, 0, 0, d + 2 * c, 0⟩ := by
  intro c d
  step fm
  step fm
  show ⟨0 + 2, 0, c, d, 0⟩ [fm]⊢* _
  apply stepStar_trans (r2r1_chain c 0 d)
  ring_nf; finish

-- Main transition: (n+1, 0, 0, D, 0) →⁺ (n+2, 0, 0, D+3*n, 0)
-- Phases: R2 drain → R3 drain → R4 chain → interleaved
theorem main_trans : ∀ n D, ⟨n + 1, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, D + 3 * n, 0⟩ := by
  intro n D
  -- First R2 step to get ⊢⁺: (n+1, 0, 0, D, 0) → (n, 1, 0, D+2, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, 0, D, 0⟩ = some ⟨n, 1, 0, D + 2, 0⟩; simp [fm]
  -- Remaining n R2 steps: (n, 1, 0, D+2, 0) →* (0, n+1, 0, D+2+2*n, 0)
  have h1 := a_to_b n 0 1 (D + 2)
  rw [show 0 + n = n from by ring,
      show 1 + n = n + 1 from by ring,
      show D + 2 + 2 * n = D + 2 * (n + 1) from by ring] at h1
  apply stepStar_trans h1
  -- R3 chain
  have h2 := b_to_e (n + 1) 0 (D + 2 * (n + 1)) 0
  rw [show 0 + (n + 1) = n + 1 from by ring] at h2
  apply stepStar_trans h2
  -- R4 chain
  have h3 := de_to_c (n + 1) 0 (D + n + 1) 0
  rw [show (D + n + 1) + (n + 1) = D + 2 * (n + 1) from by ring,
      show 0 + (n + 1) = n + 1 from by ring] at h3
  apply stepStar_trans h3
  -- Interleaved
  have h4 := interleaved n (D + n)
  rw [show (D + n) + 1 = D + n + 1 from by ring,
      show (D + n) + 2 * n = D + 3 * n from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0⟩)
  · execute fm 15
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, D⟩ ↦ ⟨n + 1, 0, 0, D, 0⟩) ⟨2, 3⟩
  intro ⟨n, D⟩
  exact ⟨⟨n + 1, D + 3 * n⟩, main_trans n D⟩

end Sz22_2003_unofficial_885

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1162: [5/6, 44/35, 91/2, 3/11, 242/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 1  0  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1162

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+2, f⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e, f) →* (a, 0, 0, d+k, e, f+k)
theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    rw [show d + (k + 1) = (d + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    exact ih a (d + 1) e (f + 1)

-- R4 chain: (0, b, 0, d, e+k, f) →* (0, b+k, 0, d, e, f)
theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    exact ih (b + 1) d e f

-- Round step: R2 then R1 x 2.
-- (0, b+2, c+1, d+1, e, f) →* (0, b, c+2, d, e+1, f)
theorem round_step : ∀ b c d e f, ⟨0, b + 2, c + 1, d + 1, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2, d, e + 1, f⟩ := by
  intro b c d e f; step fm; step fm; step fm; finish

-- Round chain: k rounds.
-- (0, b+2*k, c+1, d+k, e, f) →* (0, b, c+k+1, d, e+k, f)
theorem round_chain : ∀ k, ∀ b c d e, ⟨0, b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + k + 1, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (round_step (b + 2 * k) c (d + k) e f)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Partial round: R2, R1 x 1.
-- (0, 1, c+1, d+1, e, f) →* (1, 0, c+1, d, e+1, f)
theorem partial_round : ∀ c d e f, ⟨0, 1, c + 1, d + 1, e, f⟩ [fm]⊢* ⟨(1 : ℕ), 0, c + 1, d, e + 1, f⟩ := by
  intro c d e f; step fm; step fm; finish

-- R2 drain: (a, 0, c+k, d+k, e, f) →* (a+2*k, 0, c, d, e+k, f)
theorem r2_drain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (a + 2) c d (e + 1) f

-- R3/R2 chain: alternating R3 and R2.
-- (a+1, 0, k, 0, e, f) →* (a+k+1, 0, 0, 0, e+k, f+k)
theorem r3r2_chain : ∀ k, ∀ a e f, ⟨a + 1, 0, k, 0, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    exact ih (a + 1) (e + 1) (f + 1)

-- Phases 1-2: R3 then R4.
theorem phases12 : ∀ n, ⟨n + 3, 0, 0, 0, 2 * n + 4, n * (n + 2)⟩ [fm]⊢*
    ⟨0, 2 * n + 4, 0, n + 3, 0, n * (n + 2) + n + 3⟩ := by
  intro n
  rw [show n + 3 = 0 + (n + 3) from by ring]
  apply stepStar_trans (r3_chain (n + 3) 0 0 (2 * n + 4) (n * (n + 2)))
  simp only [Nat.zero_add]
  rw [show n * (n + 2) + (n + 3) = n * (n + 2) + n + 3 from by ring,
      show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 4) 0 (n + 3) 0 (n * (n + 2) + n + 3))
  simp only [Nat.zero_add]
  ring_nf; finish

-- Phase 3: one R5 step (produces ⊢⁺).
theorem phase3 : ∀ n, ⟨0, 2 * n + 4, 0, n + 3, 0, n * (n + 2) + n + 3⟩ [fm]⊢⁺
    ⟨1, 2 * n + 4, 0, n + 3, 2, n * (n + 2) + n + 2⟩ := by
  intro n
  rw [show n * (n + 2) + n + 3 = (n * (n + 2) + n + 2) + 1 from by ring]
  step fm; finish

-- Phase 4: one R1 step.
theorem phase4 : ∀ n F, ⟨1, 2 * n + 4, 0, n + 3, 2, F⟩ [fm]⊢*
    ⟨0, 2 * n + 3, 1, n + 3, 2, F⟩ := by
  intro n F
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm; finish

-- Phase 5: round chain x (n+1).
theorem phase5 : ∀ n F, ⟨0, 2 * n + 3, 1, n + 3, 2, F⟩ [fm]⊢*
    ⟨(0 : ℕ), 1, n + 2, 2, n + 3, F⟩ := by
  intro n F
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
      show n + 3 = 2 + (n + 1) from by ring]
  apply stepStar_trans (round_chain (n + 1) 1 0 2 2 (f := F))
  ring_nf; finish

-- Phase 6: partial round + R2.
theorem phase6 : ∀ n F, ⟨0, 1, n + 2, 2, n + 3, F⟩ [fm]⊢*
    ⟨3, 0, n + 1, 0, n + 5, F⟩ := by
  intro n F
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (partial_round (n + 1) 1 (n + 3) F)
  rw [show n + 1 + 1 = (n + 1) + 1 from rfl,
      show n + 3 + 1 = n + 4 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r2_drain 1 1 (n + 1) 0 (n + 4) F)
  ring_nf; finish

-- Phase 7: R3/R2 chain x (n+1).
theorem phase7 : ∀ n F, ⟨3, 0, n + 1, 0, n + 5, F⟩ [fm]⊢*
    ⟨n + 4, 0, 0, 0, 2 * n + 6, F + n + 1⟩ := by
  intro n F
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (n + 1) 2 (n + 5) F)
  ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1).
theorem main_trans : ∀ n, ⟨n + 3, 0, 0, 0, 2 * n + 4, n * (n + 2)⟩ [fm]⊢⁺
    ⟨n + 4, 0, 0, 0, 2 * n + 6, (n + 1) * (n + 3)⟩ := by
  intro n
  -- Phases 1-2 (⊢*)
  apply stepStar_stepPlus_stepPlus (phases12 n)
  -- Phase 3 (⊢⁺ — this gives us the ⊢⁺ for the whole chain)
  apply stepPlus_stepStar_stepPlus (phase3 n)
  -- Phase 4 (⊢*)
  apply stepStar_trans (phase4 n (n * (n + 2) + n + 2))
  -- Phase 5 (⊢*)
  apply stepStar_trans (phase5 n (n * (n + 2) + n + 2))
  -- Phase 6 (⊢*)
  apply stepStar_trans (phase6 n (n * (n + 2) + n + 2))
  -- Phase 7 (⊢*)
  apply stepStar_trans (phase7 n (n * (n + 2) + n + 2))
  rw [show n * (n + 2) + n + 2 + n + 1 = (n + 1) * (n + 3) from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 4, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 3, 0, 0, 0, 2 * n + 4, n * (n + 2)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1162

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #771: [35/6, 52/55, 77/2, 3/13, 15/7]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  1
-1  0  0  1  1  0
 0  1  0  0  0 -1
 0  1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_771

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r3_drain : ∀ k a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1) f)
    ring_nf; finish

theorem r4_drain : ∀ k b d e f, ⟨0, b, 0, d, e, f + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k b c d e f,
    ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show c + 1 + 1 = c + 2 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e (f + 1))
    ring_nf; finish

theorem r3r2_chain : ∀ k a d f,
    ⟨a + 1, 0, k, d, 0, f⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + k, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1) (f + 1))
    ring_nf; finish

-- Phases 1+2: R3 drain a, then R4 drain f
theorem phase12 (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n * n + 4 * n + 2, 0, 2 * n + 2⟩ [fm]⊢*
    ⟨0, 2 * n + 2, 0, 2 * n * n + 5 * n + 4, n + 2, 0⟩ := by
  apply stepStar_trans
  · rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring,
        show (0 : ℕ) = 0 + 0 from by ring]
    exact r3_drain (n + 2) 0 (2 * n * n + 4 * n + 2) 0 (2 * n + 2)
  rw [show 2 * n * n + 4 * n + 2 + (n + 2) = 2 * n * n + 5 * n + 4 from by ring,
      show 0 + (n + 2) = n + 2 from by ring,
      show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * n + 2) 0 (2 * n * n + 5 * n + 4) (n + 2) 0)
  ring_nf; finish

-- Phases 3+4: R5, R2
theorem phase34 (n : ℕ) :
    ⟨0, 2 * n + 2, 0, 2 * n * n + 5 * n + 4, n + 2, 0⟩ [fm]⊢*
    ⟨2, 2 * n + 3, 0, 2 * n * n + 5 * n + 3, n + 1, 1⟩ := by
  rw [show 2 * n * n + 5 * n + 4 = (2 * n * n + 5 * n + 3) + 1 from by ring,
      show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Phase 5: R1R1R2 chain (n+1 rounds)
theorem phase5 (n : ℕ) :
    ⟨2, 2 * n + 3, 0, 2 * n * n + 5 * n + 3, n + 1, 1⟩ [fm]⊢*
    ⟨2, 1, n + 1, 2 * n * n + 7 * n + 5, 0, n + 2⟩ := by
  have h := r1r1r2_chain (n + 1) 1 0 (2 * n * n + 5 * n + 3) 0 1
  simp only [show 1 + 2 * (n + 1) = 2 * n + 3 from by ring,
      show 0 + (n + 1) = n + 1 from by ring,
      show 2 * n * n + 5 * n + 3 + 2 * (n + 1) = 2 * n * n + 7 * n + 5 from by ring,
      show 1 + (n + 1) = n + 2 from by ring] at h
  exact h

-- Phase 6: R1 + R3 + R2
theorem phase6 (n : ℕ) :
    ⟨2, 1, n + 1, 2 * n * n + 7 * n + 5, 0, n + 2⟩ [fm]⊢*
    ⟨2, 0, n + 1, 2 * n * n + 7 * n + 7, 0, n + 3⟩ := by
  rw [show 2 * n * n + 7 * n + 5 = (2 * n * n + 7 * n + 4) + 1 from by ring]
  step fm  -- R1
  step fm  -- R3
  rw [show n + 1 + 1 = n + 2 from by ring,
      show 2 * n * n + 7 * n + 4 + 1 + 1 = (2 * n * n + 7 * n + 6) from by ring]
  step fm  -- R2
  ring_nf; finish

-- Phase 7: R3 + R2 + R3R2 chain
theorem phase7 (n : ℕ) :
    ⟨2, 0, n + 1, 2 * n * n + 7 * n + 7, 0, n + 3⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 2 * n * n + 8 * n + 8, 0, 2 * n + 4⟩ := by
  step fm  -- R3
  step fm  -- R2
  rw [show 2 * n * n + 7 * n + 7 + 1 = 2 * n * n + 7 * n + 8 from by ring,
      show n + 3 + 1 = n + 4 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  have h := r3r2_chain n 2 (2 * n * n + 7 * n + 8) (n + 4)
  rw [show 2 + n + 1 = n + 3 from by ring,
      show 2 * n * n + 7 * n + 8 + n = 2 * n * n + 8 * n + 8 from by ring,
      show n + 4 + n = 2 * n + 4 from by ring] at h
  exact h

-- Main transition: C(n) →⁺ C(n+1) where C(n) = (n+2, 0, 0, 2n^2+4n+2, 0, 2n+2)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n * n + 4 * n + 2, 0, 2 * n + 2⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 2 * n * n + 8 * n + 8, 0, 2 * n + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (phase12 n)
  apply stepStar_stepPlus_stepPlus (phase34 n)
  apply stepStar_stepPlus_stepPlus (phase5 n)
  apply stepStar_stepPlus_stepPlus (phase6 n)
  exact phase7 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n * n + 4 * n + 2, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  have h := main_trans n
  rw [show n + 3 = (n + 1) + 2 from by ring,
      show 2 * n * n + 8 * n + 8 = 2 * (n + 1) * (n + 1) + 4 * (n + 1) + 2 from by ring,
      show 2 * n + 4 = 2 * (n + 1) + 2 from by ring] at h
  exact h

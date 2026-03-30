import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1002: [4/15, 429/14, 55/2, 7/13, 39/11]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  1
-1  0  1  0  1  0
 0  0  0  1  0 -1
 0  1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1002

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R3 repeated k times.
theorem r3_chain : ∀ k a c e f, ⟨a + k, 0, c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1) f)
    ring_nf; finish

-- R4 repeated k times.
theorem r4_chain : ∀ k c d e f, ⟨0, 0, c, d, e, f + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [Nat.add_succ f k]
    step fm
    apply stepStar_trans (ih c (d + 1) e f)
    ring_nf; finish

-- Interleaved (R2, R1) chain: k rounds.
theorem r2r1_chain : ∀ k a e f, ⟨a + 2, 0, k, k, e, f⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · step fm
    step fm
    rw [show a + 3 = (a + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1).
theorem main_trans : ∀ n, ⟨n + 2, 0, 0, 0, (n + 1) * n, n + 1⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 0, (n + 2) * (n + 1), n + 2⟩ := by
  intro n
  -- Phase 1: R3 x (n+2)
  have h1 : ⟨n + 2, 0, 0, 0, (n + 1) * n, n + 1⟩ [fm]⊢*
      ⟨0, 0, n + 2, 0, (n + 1) * n + (n + 2), n + 1⟩ := by
    have := r3_chain (n + 2) 0 0 ((n + 1) * n) (n + 1)
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 2: R4 x (n+1)
  have h2 : ⟨0, 0, n + 2, 0, (n + 1) * n + (n + 2), n + 1⟩ [fm]⊢*
      ⟨0, 0, n + 2, n + 1, (n + 1) * n + (n + 2), 0⟩ := by
    have := r4_chain (n + 1) (n + 2) 0 ((n + 1) * n + (n + 2)) 0
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 3+4: R5 then R1 (2 steps)
  have h34 : ⟨0, 0, n + 2, n + 1, (n + 1) * n + (n + 2), 0⟩ [fm]⊢⁺
      ⟨2, 0, n + 1, n + 1, (n + 1) * n + (n + 1), 1⟩ := by
    rw [show (n + 1) * n + (n + 2) = ((n + 1) * n + (n + 1)) + 1 from by ring,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm
    step fm
    finish
  -- Phase 5: R2R1 x (n+1)
  have h5 : ⟨2, 0, n + 1, n + 1, (n + 1) * n + (n + 1), 1⟩ [fm]⊢*
      ⟨n + 3, 0, 0, 0, (n + 2) * (n + 1), n + 2⟩ := by
    have := r2r1_chain (n + 1) 0 ((n + 1) * n + (n + 1)) 1
    simp only [Nat.zero_add] at this
    apply stepStar_trans this
    ring_nf; finish
  -- Compose
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  exact stepPlus_stepStar_stepPlus h34 h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, (n + 1) * n, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

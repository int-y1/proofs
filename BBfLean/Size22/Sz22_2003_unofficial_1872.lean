import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1872: [9/35, 2662/5, 5/33, 7/121, 5/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  3
 0 -1  1  0 -1
 0  0  0  1 -2
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1872

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r5r1_drain : ∀ k a b d, ⟨a + k, b, 0, d + k, (0 : ℕ)⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 2) d)
    ring_nf; finish

theorem r3r2_chain : ∀ k a b e, ⟨a, b + (k + 1), 0, 0, e + 1⟩ [fm]⊢*
    ⟨a + (k + 1), b, 0, 0, e + 1 + 2 * (k + 1)⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · step fm; step fm; ring_nf; finish
  · rw [show b + (k + 1 + 1) = (b + (k + 1)) + 1 from by ring]
    step fm; step fm
    rw [show e + 2 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) b (e + 2))
    ring_nf; finish

theorem r4_drain : ∀ k a d, ⟨a, 0, 0, d, 1 + 2 * (k + 1)⟩ [fm]⊢* ⟨a, 0, 0, d + (k + 1), (1 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; finish
  · rw [show 1 + 2 * (k + 1 + 1) = (1 + 2 * (k + 1)) + 2 from by ring]
    step fm
    rw [show d + (k + 1 + 1) = (d + 1) + (k + 1) from by ring]
    exact ih a (d + 1)

-- Combined transition for n ≥ 1: opening 4 steps + r5r1_drain + 2 steps + r3r2 + r4
-- From (n+1, 0, 0, n+1, 1) to (2n+2, 0, 0, 2n+2, 1)
-- After 4 initial steps: (n+1, 3, 0, n, 0)
-- r5r1_drain n: needs (1+n, 3, 0, 0+n, 0) which is propositionally (n+1, 3, 0, n, 0)
-- Result: (1, 3+2n, 0, 0, 0)
-- 2 steps (R5, R2): (1, 2n+3, 0, 0, 3)
-- r3r2_chain: (2n+4, 0, 0, 0, 4n+9)
-- r4_drain: (2n+4, 0, 0, 2n+4, 1)

theorem phase_b_wrapper (n : ℕ) : ⟨n + 1, 3, 0, n, (0 : ℕ)⟩ [fm]⊢* ⟨(1 : ℕ), 2 * n + 3, 0, 0, (0 : ℕ)⟩ := by
  have h := r5r1_drain n 1 3 0
  -- h : (1 + n, 3, 0, 0 + n, 0) ⊢* (1, 3 + 2 * n, 0, 0, 0)
  -- Need (n + 1, 3, 0, n, 0) ⊢* (1, 2 * n + 3, 0, 0, 0)
  rw [show (1 : ℕ) + n = n + 1 from by ring, show (0 : ℕ) + n = n from by ring,
      show 3 + 2 * n = 2 * n + 3 from by ring] at h
  exact h

theorem phase_de_wrapper (n : ℕ) : ⟨(1 : ℕ), 2 * n + 3, 0, 0, 3⟩ [fm]⊢*
    ⟨2 * n + 4, 0, 0, 2 * n + 4, (1 : ℕ)⟩ := by
  rw [show 2 * n + 3 = 0 + (2 * n + 2 + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (2 * n + 2) 1 0 2)
  rw [show 1 + (2 * n + 2 + 1) = 2 * n + 4 from by ring,
      show 2 + 1 + 2 * (2 * n + 2 + 1) = 1 + 2 * (2 * n + 3 + 1) from by ring]
  have h := r4_drain (2 * n + 3) (2 * n + 4) 0
  rw [show (0 : ℕ) + (2 * n + 3 + 1) = 2 * n + 4 from by ring] at h
  exact h

theorem main_trans (n : ℕ) : ⟨n + 1, 0, 0, n + 1, 1⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 0, 2 * n + 2, 1⟩ := by
  rcases n with _ | n
  · execute fm 8
  · rw [show n + 1 + 1 = (n + 1) + 1 from by ring]
    step fm
    rw [show (n + 1) + 1 = n + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
    apply stepStar_trans (phase_b_wrapper n)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; step fm
    exact phase_de_wrapper n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n + 1, 1⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans n⟩

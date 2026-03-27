import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #233: [11/105, 2/3, 45/22, 49/2, 33/7]

Vector representation:
```
 0 -1 -1 -1  1
 1 -1  0  0  0
-1  2  1  0 -1
-1  0  0  2  0
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_233

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: (a+k, 0, c, d, 0) →* (a, 0, c, d+2k, 0)
theorem r4_chain : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (d + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]
    finish

-- Drain: alternating R5/R1 pairs drain c
-- (0, 0, c+k, d+2k, e) →* (0, 0, c, d, e+2k)
theorem drain : ∀ k c d e, ⟨0, 0, c + k, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    -- R5: (0, 0, c+k+1, d+2k+2, e) → (0, 1, c+k+1, d+2k+1, e+1)
    step fm
    -- R1: (0, 1, c+k+1, d+2k+1, e+1) → (0, 0, c+k, d+2k, e+2)
    step fm
    apply stepStar_trans (ih c d (e + 2))
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]
    finish

-- Tail: (0, 0, 0, 2, e) →* (0, 2, 1, 0, e)
-- R5: (0, 1, 0, 1, e+1)
-- R2: (1, 0, 0, 1, e+1)
-- R3: (0, 2, 1, 1, e)
-- R1: (0, 1, 0, 0, e+1)
-- R2: (1, 0, 0, 0, e+1)
-- R3: (0, 2, 1, 0, e)
theorem tail (e : ℕ) : ⟨0, 0, 0, 2, e⟩ [fm]⊢* ⟨0, 2, 1, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- R2 pair: (0, 2, c, 0, e) → (2, 0, c, 0, e)
theorem r2_pair (c e : ℕ) : ⟨0, 2, c, 0, e⟩ [fm]⊢* ⟨2, 0, c, 0, e⟩ := by
  rcases e with _ | e
  · rcases c with _ | c <;> (step fm; step fm; finish)
  · rcases c with _ | c <;> (step fm; step fm; finish)

-- Pump: (k+2, 0, k+1, 0, j) →* (k+j+2, 0, k+j+1, 0, 0)
-- Each step: R3, R2, R2
theorem pump : ∀ j k, ⟨k + 2, 0, k + 1, 0, j⟩ [fm]⊢* ⟨k + j + 2, 0, k + j + 1, 0, 0⟩ := by
  intro j; induction j with
  | zero => intro k; simp; exists 0
  | succ j ih =>
    intro k
    rw [show k + 2 = (k + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k + 1))
    rw [show k + 1 + j + 2 = k + (j + 1) + 2 from by ring,
        show k + 1 + j + 1 = k + (j + 1) + 1 from by ring]
    finish

-- Main transition: (2n+2, 0, 2n+1, 0, 0) →⁺ (4n+4, 0, 4n+3, 0, 0)
-- i.e., (2(n+1), 0, 2(n+1)-1, 0, 0) →⁺ (4(n+1), 0, 4(n+1)-1, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 2, 0, 2 * n + 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * n + 4, 0, 4 * n + 3, 0, 0⟩ := by
  -- Phase 1: R4 chain (2n+2 steps)
  -- (2n+2, 0, 2n+1, 0, 0) →* (0, 0, 2n+1, 4n+4, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * n + 1, 4 * n + 4, 0⟩)
  · have h := r4_chain (2 * n + 2) 0 (2 * n + 1) 0
    rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring,
        show (0 : ℕ) + 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 2: drain c (2n+1 pairs)
  -- (0, 0, 2n+1, 4n+4, 0) →* (0, 0, 0, 2, 4n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2, 4 * n + 2⟩)
  · have h := drain (2 * n + 1) 0 2 0
    rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring,
        show 2 + 2 * (2 * n + 1) = 4 * n + 4 from by ring,
        show (0 : ℕ) + 2 * (2 * n + 1) = 4 * n + 2 from by ring] at h
    exact h
  -- Phase 3: tail
  -- (0, 0, 0, 2, 4n+2) →* (0, 2, 1, 0, 4n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 1, 0, 4 * n + 2⟩)
  · exact tail (4 * n + 2)
  -- Phase 4a: R2 pair
  -- (0, 2, 1, 0, 4n+2) →* (2, 0, 1, 0, 4n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, 1, 0, 4 * n + 2⟩)
  · exact r2_pair 1 (4 * n + 2)
  -- Phase 4b: pump (4n+2 iterations from k=0)
  -- (2, 0, 1, 0, 4n+2) →* (4n+4, 0, 4n+3, 0, 0)
  have h := pump (4 * n + 2) 0
  rw [show (0 : ℕ) + 2 = 2 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring,
      show 0 + (4 * n + 2) + 2 = 4 * n + 4 from by ring,
      show 0 + (4 * n + 2) + 1 = 4 * n + 3 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq
    have := congr_arg (fun q : Q => q.1) heq
    simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, 2 * n + 1, 0, 0⟩) 0
  intro n; exact ⟨2 * n + 1, by rw [show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring,
    show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_233

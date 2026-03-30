import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #687: [35/6, 4/55, 11/2, 3/7, 24/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 3  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_687

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+3, b+1, c, d, e⟩
  | _ => none

-- R3 chain: drain a into e (b=0, c=0)
theorem a_to_e : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R4 chain: move d to b (a=0, c=0)
theorem d_to_b : ∀ k, ∀ b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R2 drain: consume paired c and e (b=0)
theorem r2_drain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

-- Round chain: m rounds of R2+R1+R1 in the middle phase
theorem round_chain : ∀ m, ∀ b c d e,
    ⟨0, b + 2 * m, c + 1, d, e + m⟩ [fm]⊢* ⟨0, b, c + m + 1, d + 2 * m, e⟩ := by
  intro m; induction' m with m ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (m + 1) = (b + 2) + 2 * m from by ring,
        show e + (m + 1) = (e + 1) + m from by ring]
    apply stepStar_trans (ih (b + 2) c d (e + 1))
    rw [show c + m + 1 = (c + m) + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish

-- Odd partial: R2+R1 when b=1
theorem odd_partial : ∀ c d e, ⟨0, 1, c + 1, d, e + 1⟩ [fm]⊢* ⟨1, 0, c + 1, d + 1, e⟩ := by
  intro c d e
  step fm; step fm; finish

-- Full transition from (a, 0, 0, d, e) through all phases:
-- a_to_e + d_to_b + R5 + R1x3 + middle + drain
-- For even n=2m: (2m+5, 0, 0, 2m+2, 2m) →⁺ (2m+6, 0, 0, 2m+3, 2m+1)
theorem even_main (m : ℕ) :
    ⟨2*m+5, 0, 0, 2*m+2, 2*m⟩ [fm]⊢⁺ ⟨2*m+6, 0, 0, 2*m+3, 2*m+1⟩ := by
  -- Phase 1: a_to_e (first step gives ⊢⁺)
  rw [show (2 * m + 5 : ℕ) = (2 * m + 4) + 1 from by ring]
  step fm
  -- Drain remaining a
  apply stepStar_trans (a_to_e (2 * m + 4) (2 * m + 2) (2 * m + 1))
  rw [show 2 * m + 1 + (2 * m + 4) = 4 * m + 5 from by ring]
  -- Phase 2: d_to_b
  apply stepStar_trans (d_to_b (2 * m + 2) 0 (4 * m + 5))
  -- Phase 3: R5
  rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring,
      show (4 * m + 5 : ℕ) = (4 * m + 4) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 + 1 = 2 * m + 3 from by ring]
  -- Phase 4: R1 x3
  step fm; step fm; step fm
  -- Now at (0, 2m, 3, 3, 4m+4)
  -- Phase 5: round_chain m rounds
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show (4 * m + 4 : ℕ) = (3 * m + 4) + m from by ring]
  apply stepStar_trans (round_chain m 0 2 3 (3 * m + 4))
  rw [show 2 + m + 1 = m + 3 from by ring,
      show 3 + 2 * m = 2 * m + 3 from by ring]
  -- Phase 6: r2_drain
  rw [show (m + 3 : ℕ) = 0 + (m + 3) from by ring,
      show (3 * m + 4 : ℕ) = (2 * m + 1) + (m + 3) from by ring]
  apply stepStar_trans (r2_drain (m + 3) 0 0 (2 * m + 3) (2 * m + 1))
  ring_nf; finish

-- For odd n=2m+1: (2m+6, 0, 0, 2m+3, 2m+1) →⁺ (2m+7, 0, 0, 2m+4, 2m+2)
theorem odd_main (m : ℕ) :
    ⟨2*m+6, 0, 0, 2*m+3, 2*m+1⟩ [fm]⊢⁺ ⟨2*m+7, 0, 0, 2*m+4, 2*m+2⟩ := by
  -- Phase 1: a_to_e (first step gives ⊢⁺)
  rw [show (2 * m + 6 : ℕ) = (2 * m + 5) + 1 from by ring]
  step fm
  apply stepStar_trans (a_to_e (2 * m + 5) (2 * m + 3) (2 * m + 1 + 1))
  rw [show 2 * m + 1 + 1 + (2 * m + 5) = 4 * m + 7 from by ring]
  -- Phase 2: d_to_b
  apply stepStar_trans (d_to_b (2 * m + 3) 0 (4 * m + 7))
  -- Phase 3: R5
  rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring,
      show (4 * m + 7 : ℕ) = (4 * m + 6) + 1 from by ring]
  step fm
  rw [show 2 * m + 3 + 1 = 2 * m + 4 from by ring]
  -- Phase 4: R1 x3
  step fm; step fm; step fm
  -- Now at (0, 2m+1, 3, 3, 4m+6)
  -- Phase 5: round_chain m rounds
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show (4 * m + 6 : ℕ) = (3 * m + 6) + m from by ring]
  apply stepStar_trans (round_chain m 1 2 3 (3 * m + 6))
  rw [show 2 + m + 1 = (m + 2) + 1 from by ring,
      show 3 + 2 * m = 2 * m + 3 from by ring]
  -- Phase 6: odd_partial
  rw [show (3 * m + 6 : ℕ) = (3 * m + 5) + 1 from by ring]
  apply stepStar_trans (odd_partial (m + 2) (2 * m + 3) (3 * m + 5))
  rw [show m + 2 + 1 = m + 3 from by ring,
      show 2 * m + 3 + 1 = 2 * m + 4 from by ring]
  -- Phase 7: r2_drain
  rw [show (m + 3 : ℕ) = 0 + (m + 3) from by ring,
      show (3 * m + 5 : ℕ) = (2 * m + 2) + (m + 3) from by ring]
  apply stepStar_trans (r2_drain (m + 3) 1 0 (2 * m + 4) (2 * m + 2))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 5, 0, 0, n + 2, n⟩ [fm]⊢⁺ ⟨n + 6, 0, 0, n + 3, n + 1⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact even_main m
  · subst hm
    rw [show 2 * m + 1 + 5 = 2 * m + 6 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 6 = 2 * m + 7 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
    exact odd_main m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 2, 0⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 5, 0, 0, n + 2, n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_687

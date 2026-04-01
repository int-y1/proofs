import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1304: [63/10, 121/2, 4/33, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2 -1  0  0 -1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1304

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k c, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- R1-R1-R3 interleaving chain
theorem r1r1r3_chain : ∀ k b d,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2))
    ring_nf; finish

-- R3-R2-R2 drain chain
theorem r3r2r2_chain : ∀ k b d e,
    ⟨0, b + k, 0, d, e + 1⟩ [fm]⊢* ⟨0, b, 0, d, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih b d (e + 3))
    ring_nf; finish

-- Main transition for even d-parameter (d_reg = 2n+2)
theorem main_even (n e : ℕ) :
    ⟨0, 0, 0, 2 * n + 2, e + 2 * n + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * n + 3, e + 10 * n + 12⟩ := by
  -- d_to_c
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * n + 2) 0 (e := e + 2 * n + 3))
  -- State: ⟨0, 0, 2*n+2, 0, e+2*n+3⟩
  -- R5
  rw [show e + 2 * n + 3 = (e + 2 * n + 2) + 1 from by ring]
  step fm
  -- R1
  rw [show 0 + (2 * n + 2) = (2 * n + 1) + 1 from by ring]
  step fm
  -- R3
  rw [show e + 2 * n + 2 = (e + 2 * n + 1) + 1 from by ring]
  step fm
  -- r1r1r3 chain with k = n
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show e + 2 * n + 1 = (e + n + 1) + n from by ring]
  apply stepStar_trans (r1r1r3_chain n (c := 1) (e := e + n + 1) 1 2)
  -- State: ⟨2, 1+3*n, 1, 2+2*n, e+n+1⟩
  -- R1 + R2
  rw [show 1 + 3 * n = (3 * n) + 1 from by ring,
      show 2 + 2 * n = (2 * n + 2) from by ring]
  step fm
  step fm
  -- r3r2r2 drain
  rw [show 3 * n + 1 + 2 = 0 + (3 * n + 3) from by ring,
      show e + n + 1 + 2 = (e + n + 2) + 1 from by ring,
      show 2 * n + 2 + 1 = 2 * n + 3 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * n + 3) 0 (2 * n + 3) (e + n + 2))
  rw [show e + n + 2 + 3 * (3 * n + 3) + 1 = e + 10 * n + 12 from by ring]
  finish

-- Main transition for odd d-parameter (d_reg = 2n+3)
theorem main_odd (n e : ℕ) :
    ⟨0, 0, 0, 2 * n + 3, e + 2 * n + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * n + 4, e + 10 * n + 17⟩ := by
  -- d_to_c
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * n + 3) 0 (e := e + 2 * n + 4))
  -- R5
  rw [show e + 2 * n + 4 = (e + 2 * n + 3) + 1 from by ring]
  step fm
  -- R1
  rw [show 0 + (2 * n + 3) = (2 * n + 2) + 1 from by ring]
  step fm
  -- R3
  rw [show e + 2 * n + 3 = (e + 2 * n + 2) + 1 from by ring]
  step fm
  -- r1r1r3 chain with k = n + 1
  rw [show 2 * n + 2 = 0 + 2 * (n + 1) from by ring,
      show e + 2 * n + 2 = (e + n + 1) + (n + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (n + 1) (c := 0) (e := e + n + 1) 1 2)
  -- State: ⟨2, 1+3*(n+1), 0, 2+2*(n+1), e+n+1⟩
  -- R2 + R2
  rw [show 1 + 3 * (n + 1) = (3 * n + 4) from by ring,
      show 2 + 2 * (n + 1) = (2 * n + 4) from by ring]
  step fm
  step fm
  -- r3r2r2 drain
  rw [show 3 * n + 4 = 0 + (3 * n + 4) from by ring,
      show e + n + 1 + 2 + 2 = (e + n + 4) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * n + 4) 0 (2 * n + 4) (e + n + 4))
  rw [show e + n + 4 + 3 * (3 * n + 4) + 1 = e + 10 * n + 17 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 8⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 2, e + d + 3⟩)
  · intro c ⟨d, e, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨n, hn⟩ | ⟨n, hn⟩
    · rw [show n + n = 2 * n from by ring] at hn; subst hn
      refine ⟨⟨0, 0, 0, 2 * n + 3, e + 10 * n + 12⟩,
        ⟨2 * n + 1, e + 8 * n + 8, by ring_nf⟩, ?_⟩
      rw [show e + (2 * n) + 3 = e + 2 * n + 3 from by ring]
      exact main_even n e
    · subst hn
      refine ⟨⟨0, 0, 0, 2 * n + 4, e + 10 * n + 17⟩,
        ⟨2 * n + 2, e + 8 * n + 12, by ring_nf⟩, ?_⟩
      rw [show e + (2 * n + 1) + 3 = e + 2 * n + 4 from by ring]
      exact main_odd n e
  · exact ⟨0, 5, by ring_nf⟩

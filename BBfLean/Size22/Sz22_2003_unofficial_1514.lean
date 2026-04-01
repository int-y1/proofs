import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1514: [7/15, 99/14, 2/3, 5/11, 495/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 1 -1  0  0  0
 0  0  1  0 -1
-1  2  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1514

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- Full drain: k+1 rounds of R1,R1,R2
theorem drain_full : ∀ k d e, ⟨k + 1, 2, 2 * k + 3, d, e⟩ [fm]⊢* ⟨0, 2, 1, d + k + 1, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- R2+R3 chain: each round does R2 then R3
theorem r2r3_chain : ∀ k b d e, ⟨1, b, 0, d + k, e⟩ [fm]⊢* ⟨1, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) d (e + 1)); ring_nf; finish

-- R3 drain: convert b to a
theorem r3_drain : ∀ k a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b e); ring_nf; finish

-- Combined phase: from (1, 0, 0, d, d) to (d+1, 0, 0, 0, 2*d)
-- R2+R3 chain d times, then final R3 drain
theorem r2r3_then_r3 : ∀ d, ⟨1, 0, 0, d, d⟩ [fm]⊢* ⟨d + 1, 0, 0, 0, 2 * d⟩ := by
  intro d
  have h1 := r2r3_chain d 0 0 d
  rw [show (0 + d : ℕ) = d from by ring,
      show d + d = 2 * d from by ring] at h1
  apply stepStar_trans h1
  have h2 := r3_drain d 1 0 (2 * d)
  rw [show (0 + d : ℕ) = d from by ring,
      show 1 + d = d + 1 from by ring] at h2
  exact h2

-- Main transition: (n+2, 0, 2n+2, 0, 0) ⊢⁺ (n+3, 0, 2n+4, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 2 * n + 4, 0, 0⟩ := by
  -- R5: (n+2, 0, 2n+2, 0, 0) -> (n+1, 2, 2n+3, 0, 1)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- Drain: (n+1, 2, 2n+3, 0, 1) ⊢* (0, 2, 1, n+1, n+2)
  apply stepStar_trans (drain_full n 0 1)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  -- R1: (0, 2, 1, n+1, n+2) -> (0, 1, 0, n+2, n+2)
  -- R3: (0, 1, 0, n+2, n+2) -> (1, 0, 0, n+2, n+2)
  step fm; step fm
  -- Combined: (1, 0, 0, n+2, n+2) ⊢* (n+3, 0, 0, 0, 2n+4)
  apply stepStar_trans (r2r3_then_r3 (n + 2))
  rw [show n + 2 + 1 = n + 3 from by ring,
      show 2 * (n + 2) = 2 * n + 4 from by ring]
  -- R4 chain: (n+3, 0, 0, 0, 2n+4) ⊢* (n+3, 0, 2n+4, 0, 0)
  have h := e_to_c (2 * n + 4) (a := n + 3) 0 (e := 0)
  simp at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 2 * n + 2, 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1514

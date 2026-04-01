import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1328: [63/10, 2/33, 121/2, 5/7, 28/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1328

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R1 chain: apply R1 k times.
theorem r1_chain : ∀ k b c d e, ⟨a + k, b, c + k, d, e⟩ [fm]⊢* ⟨a, b + 2 * k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) c (d + 1) e); ring_nf; finish

-- R2R1 chain: k (R2, R1) pairs.
theorem r2r1_chain : ∀ k b c d e, ⟨0, b + 1, c + k, d, e + k⟩ [fm]⊢* ⟨0, b + k + 1, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R2 drain: apply R2 k times (c=0).
theorem r2_drain : ∀ k a b d e, ⟨a, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b d e); ring_nf; finish

-- R3 drain: apply R3 k times (b=0, c=0).
theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2)); ring_nf; finish

-- R4 transfer: d to c (a=0, b=0).
theorem d_to_c : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- Main transition: (0, 0, n+2, 0, 3n+8) ⊢⁺ (0, 0, n+3, 0, 3n+11)
-- i.e., for m = n+2 >= 2: (0, 0, m, 0, 3m+2) ⊢⁺ (0, 0, m+1, 0, 3m+5)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0, 3 * n + 8⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 0, 3 * n + 11⟩ := by
  -- R5: (0, 0, n+2, 0, 3n+8) -> (2, 0, n+2, 1, 3n+7)
  rw [show 3 * n + 8 = (3 * n + 7) + 1 from by ring]
  step fm
  -- R1 x 2: (2, 0, n+2, 1, 3n+7) -> (0, 4, n, 3, 3n+7)
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show n + 2 = n + 2 from rfl]
  apply stepStar_trans (r1_chain 2 0 n 1 (3 * n + 7))
  -- Now at (0, 4, n, 3, 3n+7)
  -- R2R1 chain x n: (0, 4, n, 3, 3n+7) -> (0, n+4, 0, n+3, 2n+7)
  rw [show (0 + 2 * 2 : ℕ) = 3 + 1 from by ring,
      show (1 + 2 : ℕ) = 3 from by ring,
      show (n : ℕ) = 0 + n from by ring,
      show 3 * (0 + n) + 7 = (2 * n + 7) + n from by ring]
  apply stepStar_trans (r2r1_chain n 3 0 3 (2 * n + 7))
  -- Now at (0, n+4, 0, n+3, 2n+7)
  -- R2 drain x (n+4): (0, n+4, 0, n+3, 2n+7) -> (n+4, 0, 0, n+3, n+3)
  rw [show 3 + n + 1 = n + 4 from by ring,
      show (3 + n : ℕ) = n + 3 from by ring,
      show (n + 4 : ℕ) = 0 + (n + 4) from by ring,
      show 2 * n + 7 = (n + 3) + (n + 4) from by ring]
  apply stepStar_trans (r2_drain (n + 4) 0 0 (n + 3) (n + 3))
  -- Now at (n+4, 0, 0, n+3, n+3)
  -- R3 drain x (n+4): (n+4, 0, 0, n+3, n+3) -> (0, 0, 0, n+3, 3n+11)
  rw [show (0 + (n + 4) : ℕ) = 0 + (n + 4) from by ring]
  apply stepStar_trans (r3_drain (n + 4) 0 (n + 3) (n + 3))
  -- Now at (0, 0, 0, n+3, 3n+11)
  -- d_to_c x (n+3): (0, 0, 0, n+3, 3n+11) -> (0, 0, n+3, 0, 3n+11)
  rw [show n + 3 + 2 * (n + 4) = 3 * n + 11 from by ring,
      show (n + 3 : ℕ) = 0 + (n + 3) from by ring]
  apply stepStar_trans (d_to_c (n + 3) 0 0 (3 * n + 11))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 8⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 3 * n + 8⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1328

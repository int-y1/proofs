import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1329: [63/10, 2/33, 121/2, 5/7, 30/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1329

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c+1, d, e⟩
  | _ => none

-- R3 drain: apply R3 k times
theorem r3_drain : ∀ k, ∀ a d e, ⟨k + a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  · rw [show k + 1 + a = (k + a) + 1 from by ring]; step fm
    apply stepStar_trans (ih a d (e + 2)); ring_nf; finish

-- R4 drain: apply R4 k times
theorem r4_drain : ∀ k, ∀ c d e, ⟨0, 0, c, k + d, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show k + 1 + d = (k + d) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- R1R2 chain: k rounds of (R1, R2) then one final R1
theorem r1r2_chain : ∀ k, ∀ b c d e,
    ⟨1, b, c + k + 1, d, e + k⟩ [fm]⊢* ⟨0, b + k + 2, c, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp only [Nat.add_zero]; step fm; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R2 drain: apply R2 k times
theorem r2_drain : ∀ k, ∀ a b d e, ⟨a, k + b, 0, d, k + e⟩ [fm]⊢* ⟨k + a, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; exists 0
  · rw [show k + 1 + b = (k + b) + 1 from by ring,
        show k + 1 + e = (k + e) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b d e); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0⟩ := by
  -- First R3 step for ⊢⁺
  rw [show n + 2 = (n + 1) + 1 from by ring]; step fm
  -- State: (n+1, 0, 0, n+1, 2). R3 drain remaining n+1.
  rw [show n + 1 = n + 1 + 0 from by ring]
  apply stepStar_trans (r3_drain (n + 1) 0 (n + 1) 2)
  rw [show 2 + 2 * (n + 1) = 2 * n + 4 from by ring]
  -- R4 drain: (0, 0, 0, n+1, 2n+4) -> (0, 0, n+1, 0, 2n+4)
  rw [show n + 1 = n + 1 + 0 from by ring]
  apply stepStar_trans (r4_drain (n + 1) 0 0 (2 * n + 4))
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- R5 step: (0, 0, n+1, 0, 2n+4) -> (1, 1, n+2, 0, 2n+3)
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]; step fm
  -- R1R2 chain: (1, 1, n+2, 0, 2n+3) -> (0, n+4, 0, n+2, n+2)
  rw [show n + 1 + 1 = 0 + (n + 1) + 1 from by ring,
      show 2 * n + 3 = (n + 2) + (n + 1) from by ring]
  apply stepStar_trans (r1r2_chain (n + 1) 1 0 0 (n + 2))
  rw [show 1 + (n + 1) + 2 = n + 4 from by ring,
      show 0 + (n + 1) + 1 = n + 2 from by ring]
  -- R2 drain: (0, n+4, 0, n+2, n+2) -> (n+2, 2, 0, n+2, 0)
  rw [show n + 4 = (n + 2) + 2 from by ring,
      show n + 2 = (n + 2) + 0 from by ring]
  apply stepStar_trans (r2_drain (n + 2) 0 2 (n + 2) 0)
  rw [show (n + 2) + 0 = n + 2 from by ring]
  -- End: R3 step
  rw [show n + 2 = (n + 1) + 1 from by ring]; step fm
  -- R2 drain final: (n+1, 2, 0, n+2, 2) -> (n+3, 0, 0, n+2, 0)
  rw [show (2 : ℕ) = 2 + 0 from by ring, show (2 : ℕ) = 2 + 0 from by ring]
  apply stepStar_trans (r2_drain 2 (n + 1) 0 (n + 2) 0)
  rw [show 2 + (n + 1) = n + 3 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1329

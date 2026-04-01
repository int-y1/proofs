import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1325: [63/10, 2/33, 121/2, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1325

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R1/R2 chain: k rounds of (R1, R2) from (1, b, c+k, d, e+k) to (1, b+k, c, d+k, e).
theorem r1r2_chain : ∀ k, ∀ b c d e, ⟨1, b, c + k, d, e + k⟩ [fm]⊢* ⟨1, b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R3 drain: (j, 0, 0, d, e) -> (0, 0, 0, d, e + 2*j).
theorem r3_drain : ∀ j, ∀ d e, ⟨j, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro d e
  · exists 0
  · rw [show j + 1 = j + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 2)); ring_nf; finish

-- R4 chain: (0, 0, c, d+k, e) -> (0, 0, c+k, d, e).
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- Combined drain: (a+1, b, 0, d, 0) -> (0, 0, 0, d, b + 2*a + 2) by induction on b.
theorem drain_b : ∀ b, ∀ a d, ⟨a + 1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d, b + 2 * a + 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro a d
  match b with
  | 0 =>
    -- R3 drain only
    rw [show (0 : ℕ) + 2 * a + 2 = 0 + 2 * (a + 1) from by ring]
    exact r3_drain (a + 1) d 0
  | 1 =>
    -- R3, R2, then R3 drain
    step fm; step fm
    rw [show 1 + 2 * a + 2 = 0 + 2 * (a + 1) + 1 from by ring]
    apply stepStar_trans (r3_drain (a + 1) d 1); ring_nf; finish
  | b + 2 =>
    -- R3, R2, R2, then IH with b, a+1
    step fm; step fm; step fm
    rw [show b + 2 + 2 * a + 2 = b + 2 * (a + 1) + 2 from by ring]
    exact ih b (by omega) (a + 1) d

-- Inner transition: (1, 0, n+2, 0, n+2) ⊢* (0, 0, n+2, 0, n+4).
theorem inner_trans (n : ℕ) :
    ⟨1, 0, n + 2, 0, n + 2⟩ [fm]⊢* ⟨0, 0, n + 2, 0, n + 4⟩ := by
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r1r2_chain (n + 2) 0 0 0 0)
  rw [show (0 + (n + 2) : ℕ) = n + 2 from by ring]
  apply stepStar_trans (drain_b (n + 2) 0 (n + 2))
  rw [show n + 2 + 2 * 0 + 2 = n + 4 from by ring,
      show n + 2 = 0 + (n + 2) from by ring]
  exact r4_chain (n + 2) 0 0 (n + 4)

-- Main transition: C(n) = (0, 0, n+1, 0, n+3) ⊢⁺ C(n+1) = (0, 0, n+2, 0, n+4).
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 0, n + 3⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, n + 4⟩ := by
  rw [show n + 3 = (n + 2) + 1 from by ring]
  step fm
  exact inner_trans n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 1, 0, n + 3⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1325

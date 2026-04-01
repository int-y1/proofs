import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1299: [63/10, 121/2, 2/33, 5/7, 30/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1299

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: generalized
theorem r4_chain : ∀ k c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

-- R3+R1 interleaving chain
theorem r3_r1_chain : ∀ k b c d e, b ≥ 1 →
    ⟨0, b, c + k, d, e + k⟩ [fm]⊢* ⟨0, b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e hb
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    step fm
    step fm
    apply stepStar_trans (ih (b' + 2) c (d + 1) e (by omega))
    rw [show b' + 2 + k = b' + 1 + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]; finish

-- R3+R2 drain chain
theorem r3_r2_drain : ∀ k b e, ⟨0, b + k, 0, d, e + 1⟩ [fm]⊢* ⟨0, b, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih b (e + 1))
    rw [show e + 1 + k + 1 = e + (k + 1) + 1 from by ring]; finish

-- Main transition: (0, 0, 0, n, 2n+2) →⁺ (0, 0, 0, n+1, 2(n+1)+2)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, 2 * (n + 1) + 2⟩ := by
  -- Phase 1: R4 chain
  have phase1 : ⟨0, 0, 0, n, 2 * n + 2⟩ [fm]⊢* ⟨0, 0, n, 0, 2 * n + 2⟩ := by
    have := r4_chain n 0 0 (e := 2 * n + 2)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2+3: R5 then R1
  have phase23 : ⟨0, 0, n, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 3, n, 1, 2 * n + 1⟩ := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: R3+R1 chain for n rounds
  have phase4 : ⟨0, 3, n, 1, 2 * n + 1⟩ [fm]⊢* ⟨0, 3 + n, 0, 1 + n, n + 1⟩ := by
    have := r3_r1_chain n 3 0 1 (n + 1) (by omega)
    simp only [Nat.zero_add] at this
    rw [show 2 * n + 1 = n + 1 + n from by ring]
    exact this
  -- Phase 5: R3+R2 drain for n+3 rounds
  have phase5 : ⟨0, 3 + n, 0, 1 + n, n + 1⟩ [fm]⊢* ⟨0, 0, 0, n + 1, 2 * (n + 1) + 2⟩ := by
    have := r3_r2_drain (3 + n) 0 n (d := 1 + n)
    simp only [Nat.zero_add] at this
    rw [show n + 1 = n + 0 + 1 from by ring]
    apply stepStar_trans this
    rw [show n + (3 + n) + 1 = 2 * (n + 1) + 2 from by ring,
        show 1 + n = n + 1 from by ring]; finish
  -- Compose: phase1 (⊢*) + phase23 (⊢⁺) + phase4 (⊢*) + phase5 (⊢*)
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase23
      (stepStar_trans phase4 phase5))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, 2 * n + 2⟩) 0
  intro n; exists n + 1
  exact main_trans n

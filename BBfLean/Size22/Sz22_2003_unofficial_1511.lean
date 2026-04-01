import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1511: [7/15, 99/14, 2/3, 5/11, 1089/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 1 -1  0  0  0
 0  0  1  0 -1
-1  2  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1511

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- R2/R3 interleave: each round does R2 then R3.
theorem r2r3_chain : ∀ k b d e, ⟨1, b, 0, d + k, e⟩ [fm]⊢* ⟨1, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) d (e + 1))
    ring_nf; finish

-- R3 chain: move b to a (requires c = 0, d = 0).
theorem b_to_a : ∀ k a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a + 1) b e)
    ring_nf; finish

-- R4 chain: move e to c (requires b = 0, d = 0).
theorem e_to_c : ∀ k a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- Drain round: R1, R1, R2. Chain of k rounds.
theorem drain_chain : ∀ k a d e, ⟨a + k, 2, 2 * a + 2 * k, d, e⟩ [fm]⊢* ⟨a, 2, 2 * a, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show 2 * a + 2 * (k + 1) = (2 * a + 2 * k) + 1 + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

-- Main transition: (1, 0, 0, n+2, n+2) →⁺ (1, 0, 0, n+3, n+3).
theorem main_trans (n : ℕ) : ⟨1, 0, 0, n + 2, n + 2⟩ [fm]⊢⁺ ⟨1, 0, 0, n + 3, n + 3⟩ := by
  -- Phase 1: R2/R3 chain. (1, 0, 0, n+2, n+2) →* (1, n+2, 0, 0, 2n+4).
  have p1 : ⟨1, 0, 0, n + 2, n + 2⟩ [fm]⊢* ⟨1, n + 2, 0, 0, 2 * n + 4⟩ := by
    have := r2r3_chain (n + 2) 0 0 (n + 2)
    simp only [Nat.zero_add] at this
    convert this using 2
    ring_nf
  -- Phase 2: R3 chain. (1, n+2, 0, 0, 2n+4) →* (n+3, 0, 0, 0, 2n+4).
  have p2 : ⟨1, n + 2, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
    have := b_to_a (n + 2) 1 0 (2 * n + 4)
    simp only [Nat.zero_add] at this
    convert this using 2
    ring_nf
  -- Phase 3: R4 chain. (n+3, 0, 0, 0, 2n+4) →* (n+3, 0, 2n+4, 0, 0).
  have p3 : ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 2 * n + 4, 0, 0⟩ := by
    have := e_to_c (2 * n + 4) (n + 3) 0 0
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 4: R5 step. (n+3, 0, 2n+4, 0, 0) → (n+2, 2, 2n+4, 0, 2).
  have p4 : ⟨n + 3, 0, 2 * n + 4, 0, 0⟩ [fm]⊢⁺ ⟨n + 2, 2, 2 * n + 4, 0, 2⟩ := by
    rw [show n + 3 = (n + 2) + 1 from by omega]
    step fm; finish
  -- Phase 5: Drain. (n+2, 2, 2n+4, 0, 2) →* (1, 0, 0, n+3, n+3).
  have p5 : ⟨n + 2, 2, 2 * n + 4, 0, 2⟩ [fm]⊢* ⟨1, 0, 0, n + 3, n + 3⟩ := by
    -- Drain chain: (n+2, 2, 2n+4, 0, 2) →* (1, 2, 2, n+1, n+3).
    have d1 : ⟨n + 2, 2, 2 * n + 4, 0, 2⟩ [fm]⊢* ⟨1, 2, 2, n + 1, n + 3⟩ := by
      have := drain_chain (n + 1) 1 0 2
      simp only [Nat.zero_add] at this
      convert this using 2; ring_nf
    -- Final R1, R1: (1, 2, 2, n+1, n+3) →* (1, 0, 0, n+3, n+3).
    have d2 : ⟨1, 2, 2, n + 1, n + 3⟩ [fm]⊢* ⟨1, 0, 0, n + 3, n + 3⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from by omega]
      step fm; step fm; finish
    exact stepStar_trans d1 d2
  -- Compose all phases.
  apply stepStar_stepPlus_stepPlus (stepStar_trans p1 (stepStar_trans p2 p3))
  exact stepPlus_stepStar_stepPlus p4 p5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n + 2, n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

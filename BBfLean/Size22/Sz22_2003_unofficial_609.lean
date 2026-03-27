import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #609: [35/6, 121/2, 4/55, 3/7, 98/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_609

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3+R2+R2: each round converts 1 c into 3 e (requires e >= 1)
theorem c_drain : ∀ k, ∀ c e, ⟨0, 0, c + k, d, e + 1⟩ [fm]⊢* ⟨0, 0, c, d, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3+R1+R1 interleaved chain
theorem r3r1r1_chain : ∀ k, ∀ b c d e,
    ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + 1 + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by omega,
      show e + (k + 1) = (e + k) + 1 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Compose phases 3-6 as a single ⊢⁺ starting from after R4 drain
theorem phases_2_to_6 : ⟨0, 2 * n + 2, 0, 0, n * n + 2 * n + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 4, n * n + 4 * n + 6⟩ := by
  -- Phase 2: R5 + R1
  rw [show n * n + 2 * n + 3 = (n * n + 2 * n + 2) + 1 from by omega]
  step fm; step fm
  -- Phase 3: R3R1R1 chain: n rounds
  rw [show 2 * n + 1 = 1 + 2 * n from by omega,
      show n * n + 2 * n + 2 = (n * n + n + 2) + n from by omega]
  have h3 := r3r1r1_chain n 1 0 3 (n * n + n + 2)
  rw [show 0 + 1 = 1 from by omega, show 0 + 1 + n = n + 1 from by omega] at h3
  apply stepStar_trans h3
  -- Now at: (0, 1, n+1, 3+2n, n²+n+2)
  -- Phase 4: R3+R1 (last round with b=1)
  rw [show 3 + 2 * n = 2 * n + 3 from by omega,
      show n * n + n + 2 = (n * n + n + 1) + 1 from by omega]
  step fm; step fm
  -- Phase 5: R2
  step fm
  -- Phase 6: R3+R2+R2 drain: n+1 rounds
  rw [show 2 * n + 3 + 1 = 2 * n + 4 from by omega,
      show n + 1 = 0 + (n + 1) from by omega,
      show n * n + n + 1 + 2 = (n * n + n + 2) + 1 from by omega]
  apply stepStar_trans (c_drain (n + 1) 0 (n * n + n + 2))
  ring_nf; finish

-- Main transition
theorem main_trans : ⟨0, 0, 0, 2 * n + 2, n * n + 2 * n + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 4, n * n + 4 * n + 6⟩ := by
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by omega]
  apply stepStar_stepPlus_stepPlus (@d_to_b 0 0 (2 * n + 2) (n * n + 2 * n + 3))
  simp only [Nat.zero_add]
  exact phases_2_to_6

-- Transition for n=0: (0,0,0,0,2) →⁺ (0,0,0,2,3)
theorem trans_zero : ⟨0, 0, 0, 0, (2 : ℕ)⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 3⟩ := by
  execute fm 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n, n * n + 2⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, trans_zero⟩
  · refine ⟨n + 2, ?_⟩
    have h := @main_trans n
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
        show (n + 1) * (n + 1) + 2 = n * n + 2 * n + 3 from by ring,
        show 2 * (n + 2) = 2 * n + 4 from by ring,
        show (n + 2) * (n + 2) + 2 = n * n + 4 * n + 6 from by ring]
    exact h

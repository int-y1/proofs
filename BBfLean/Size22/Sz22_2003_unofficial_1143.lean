import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1143: [5/6, 44/35, 49/2, 9/11, 6/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1143

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+2*k, e)
theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+2*k, 0, d, e)
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- R2 drain: (a, 0, k, k, e) →* (a+2*k, 0, 0, 0, e+k)
theorem r2_drain : ∀ k, ⟨a, 0, k, k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

-- R1R1R2 chain: k rounds.
-- (2, 2*k+b, c, d+k, e) →* (2, b, c+k, d, e+k)
theorem r1r1r2_chain : ∀ k b c d e,
    ⟨2, 2 * k + b, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; ring_nf; exists 0
  · intro b c d e
    rw [show 2 * (k + 1) + b = (2 * k + b) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Full transition: (N+2, 0, 0, 0, N+1) →⁺ (2*N+4, 0, 0, 0, 2*N+3)
theorem main_trans : ⟨N + 2, 0, 0, 0, N + 1⟩ [fm]⊢⁺ ⟨2 * N + 4, 0, 0, 0, 2 * N + 3⟩ := by
  -- Phase 1: R3 chain
  have h1 : ⟨N + 2, 0, 0, 0, N + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * N + 4, N + 1⟩ := by
    rw [show N + 2 = 0 + (N + 2) from by ring]
    apply stepStar_trans (a_to_d (N + 2) (a := 0) (d := 0) (e := N + 1))
    ring_nf; finish
  -- Phase 2: R4 chain
  have h2 : ⟨0, 0, 0, 2 * N + 4, N + 1⟩ [fm]⊢* ⟨0, 2 * N + 2, 0, 2 * N + 4, 0⟩ := by
    rw [show N + 1 = 0 + (N + 1) from by ring]
    apply stepStar_trans (e_to_b (N + 1) (b := 0) (d := 2 * N + 4) (e := 0))
    ring_nf; finish
  -- Phase 3-5: R5, R1, R2
  have h3 : ⟨0, 2 * N + 2, 0, 2 * N + 4, 0⟩ [fm]⊢⁺ ⟨2, 2 * N + 2, 0, 2 * N + 2, 1⟩ := by
    rw [show 2 * N + 4 = (2 * N + 3) + 1 from by ring]
    execute fm 3
  -- Phase 6: R1R1R2 chain
  have h4 : ⟨2, 2 * N + 2, 0, 2 * N + 2, 1⟩ [fm]⊢* ⟨2, 0, N + 1, N + 1, N + 2⟩ := by
    have key := r1r1r2_chain (N + 1) 0 0 (N + 1) 1
    simp only [Nat.zero_add, Nat.add_zero] at key
    rw [show 2 * (N + 1) = 2 * N + 2 from by ring,
        show (N + 1) + (N + 1) = 2 * N + 2 from by ring,
        show 1 + (N + 1) = N + 2 from by ring] at key
    exact key
  -- Phase 7: R2 drain
  have h5 : ⟨2, 0, N + 1, N + 1, N + 2⟩ [fm]⊢* ⟨2 * N + 4, 0, 0, 0, 2 * N + 3⟩ := by
    have key := r2_drain (N + 1) (a := 2) (e := N + 2)
    rw [show 2 + 2 * (N + 1) = 2 * N + 4 from by ring,
        show N + 2 + (N + 1) = 2 * N + 3 from by ring] at key
    exact key
  -- Compose
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus
        (stepStar_stepPlus_stepPlus h2 h3) h4) h5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n + 2, 0, 0, 0, n + 1⟩) 0
  intro n; exists 2 * n + 2; exact main_trans

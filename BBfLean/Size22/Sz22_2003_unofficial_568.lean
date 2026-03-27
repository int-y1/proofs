import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #568: [35/3, 6/55, 1/5, 1331/2, 1/77, 5/11]

Vector representation:
```
 0 -1  1  1  0
 1  1 -1  0 -1
 0  0 -1  0  0
-1  0  0  0  3
 0  0  0 -1 -1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_568

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert a to 3e
theorem a_to_e : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+3*k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+3*k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- R5 repeated: annihilate d and e
theorem d_e_annihilate : ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- R2+R1 chain: each round adds 1 to a and d, consumes 1 from e
theorem r2r1_chain : ⟨a, 0, 1, d, e⟩ [fm]⊢* ⟨a+e, 0, 1, d+e, 0⟩ := by
  have many_step : ∀ e a d, ⟨a, 0, 1, d, e⟩ [fm]⊢* ⟨a+e, 0, 1, d+e, 0⟩ := by
    intro e; induction' e with e h <;> intro a d
    · exists 0
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step e a d

-- Full cycle: (n+1, 0, 0, n+1, 0) →⁺ (2*n+1, 0, 0, 2*n+1, 0)
theorem main_trans : ⟨n+1, 0, 0, n+1, 0⟩ [fm]⊢⁺ ⟨2*n+1, 0, 0, 2*n+1, 0⟩ := by
  -- First R4 step: (n+1, 0, 0, n+1, 0) → (n, 0, 0, n+1, 3)
  step fm
  -- Remaining R4 steps: (n, 0, 0, n+1, 3) →* (0, 0, 0, n+1, 3+3*n)
  have h1 := a_to_e (k := n) (a := 0) (d := n + 1) (e := 3)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- R5 phase: (0, 0, 0, n+1, 3+3*n) →* (0, 0, 0, 0, 2+2*n)
  rw [show 3 + 3 * n = (2 + 2 * n) + (n + 1) from by ring]
  have h2 := d_e_annihilate (k := n + 1) (d := 0) (e := 2 + 2 * n)
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- R6 step: (0, 0, 0, 0, 2+2*n) → (0, 0, 1, 0, 1+2*n)
  rw [show 2 + 2 * n = (1 + 2 * n) + 1 from by ring]
  step fm
  -- R2+R1 chain: (0, 0, 1, 0, 1+2*n) →* (1+2*n, 0, 1, 1+2*n, 0)
  have h3 := r2r1_chain (a := 0) (d := 0) (e := 1 + 2 * n)
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- R3 step: (1+2*n, 0, 1, 1+2*n, 0) → (1+2*n, 0, 0, 1+2*n, 0)
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 2, 0⟩) 0
  intro n; exists 2 * n + 1
  have h := @main_trans (n + 1)
  rw [show n + 1 + 1 = n + 2 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by ring] at h
  exact h

end Sz22_2003_unofficial_568

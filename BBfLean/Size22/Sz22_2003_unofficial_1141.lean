import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1141: [5/6, 44/35, 49/2, 9/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1141

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+2*k, e)
theorem r3_chain : ∀ k d, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2))
    ring_nf; finish

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+2*k, 0, d, e)
theorem r4_chain : ∀ k b, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

-- R2 chain: (a, 0, c+k, d+k, e) →* (a+2*k, 0, c, d, e+k)
theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- R2-R1-R1 loop: (0, 2k, n+1, n+1+2*k, n) →* (0, 0, n+1+k, n+1+k, n+k)
theorem r2r1r1_loop : ∀ k n, ⟨0, 2 * k, n + 1, n + 1 + 2 * k, n⟩ [fm]⊢*
    ⟨0, 0, n + 1 + k, n + 1 + k, n + k⟩ := by
  intro k; induction' k with k ih <;> intro n
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    rw [show n + 1 + (2 * k + 1 + 1) = n + 1 + 2 * k + 1 + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    rw [show n + 1 + 2 * k + 1 = (n + 1) + 1 + 2 * k from by ring]
    rw [show n + 1 + (k + 1) = (n + 1) + 1 + k from by ring]
    rw [show n + (k + 1) = (n + 1) + k from by ring]
    exact ih (n + 1)

-- Phase A-B: (e+2, 0, 0, 0, e+1) →* (0, 2*e+2, 0, 2*e+4, 0)
theorem phaseAB (e : ℕ) : ⟨e + 2, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨0, 2 * e + 2, 0, 2 * e + 4, 0⟩ := by
  have hA : ⟨0 + (e + 2), 0, 0, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 0 + 2 * (e + 2), e + 1⟩ :=
    r3_chain (e + 2) 0 (a := 0) (e := e + 1)
  have hB : ⟨0, 0, 0, 2 * e + 4, 0 + (e + 1)⟩ [fm]⊢* ⟨0, 0 + 2 * (e + 1), 0, 2 * e + 4, 0⟩ :=
    r4_chain (e + 1) 0 (d := 2 * e + 4) (e := 0)
  apply stepStar_trans
  · rw [show (e + 2 : ℕ) = 0 + (e + 2) from by ring]; exact hA
  rw [show 0 + 2 * (e + 2) = 2 * e + 4 from by ring]
  apply stepStar_trans
  · rw [show (e + 1 : ℕ) = 0 + (e + 1) from by ring]; exact hB
  rw [show 0 + 2 * (e + 1) = 2 * e + 2 from by ring]; finish

-- Phase D: (0, 2*e+2, 1, 2*e+3, 0) →* (0, 0, e+2, e+2, e+1)
theorem phaseD (e : ℕ) : ⟨0, 2 * e + 2, 1, 2 * e + 3, 0⟩ [fm]⊢* ⟨0, 0, e + 2, e + 2, e + 1⟩ := by
  have h : ⟨0, 2 * (e + 1), 0 + 1, 0 + 1 + 2 * (e + 1), 0⟩ [fm]⊢*
      ⟨0, 0, 0 + 1 + (e + 1), 0 + 1 + (e + 1), 0 + (e + 1)⟩ :=
    r2r1r1_loop (e + 1) 0
  rw [show 2 * e + 2 = 2 * (e + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * e + 3 = 0 + 1 + 2 * (e + 1) from by ring]
  apply stepStar_trans h
  ring_nf; finish

-- Phase E: (0, 0, e+2, e+2, e+1) →* (2*e+4, 0, 0, 0, 2*e+3)
theorem phaseE (e : ℕ) : ⟨0, 0, e + 2, e + 2, e + 1⟩ [fm]⊢* ⟨2 * e + 4, 0, 0, 0, 2 * e + 3⟩ := by
  have h : ⟨0, 0, 0 + (e + 2), 0 + (e + 2), e + 1⟩ [fm]⊢*
      ⟨0 + 2 * (e + 2), 0, 0, 0, e + 1 + (e + 2)⟩ :=
    r2_chain (e + 2) 0 0 0 (e + 1)
  rw [show (e + 2 : ℕ) = 0 + (e + 2) from by ring]
  apply stepStar_trans h
  ring_nf; finish

-- Phase C+D+E: (0, 2*e+2, 0, 2*e+4, 0) →⁺ (2*e+4, 0, 0, 0, 2*e+3)
theorem phaseCDE (e : ℕ) : ⟨0, 2 * e + 2, 0, 2 * e + 4, 0⟩ [fm]⊢⁺ ⟨2 * e + 4, 0, 0, 0, 2 * e + 3⟩ := by
  rw [show (2 * e + 4 : ℕ) = (2 * e + 3) + 1 from by ring]
  step fm  -- R5: (0, 2e+2, 1, 2e+3, 0)
  apply stepStar_trans (phaseD e)
  exact phaseE e

-- Main transition: (e+2, 0, 0, 0, e+1) →⁺ (2*e+4, 0, 0, 0, 2*e+3)
theorem main_trans (e : ℕ) : ⟨e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * e + 4, 0, 0, 0, 2 * e + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (phaseAB e)
  exact phaseCDE e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨e + 2, 0, 0, 0, e + 1⟩) 0
  intro e; exists (2 * e + 2)
  exact main_trans e

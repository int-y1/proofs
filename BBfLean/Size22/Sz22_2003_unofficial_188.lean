import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #188: [1/6, 2/35, 1375/2, 3/25, 98/11]

Vector representation:
```
-1 -1  0  0  0
 1  0 -1 -1  0
-1  0  3  0  1
 0  1 -2  0  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_188

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- R2 repeated: consume c and d simultaneously, build a
theorem r2_chain : ∀ k a c d, ⟨a, 0, c+k, d+k, e⟩ [fm]⊢* ⟨a+k, 0, c, d, e⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: convert a to c and e (when d=0, b=0)
theorem r3_chain : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: convert c to b (when a=0, d=0)
theorem r4_chain : ∀ k b c, ⟨0, b, c+2*k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R5+R1 interleaved: convert b and e to d (when a=0, c=0)
theorem r5r1_chain : ∀ k d e, ⟨0, k, 0, d, e+k⟩ [fm]⊢* ⟨0, 0, 0, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase AB: (a+1, 0, 0, d, e) →* (0, 0, 3*(a+1)+2*d, 0, e+a+1+d)
theorem phaseAB : ∀ d a e, ⟨a+1, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 3*(a+1)+2*d, 0, e+a+1+d⟩ := by
  intro d; induction' d using Nat.strongRecOn with d ih; intro a e
  rcases d with _ | _ | _ | d
  · -- d = 0: just R3 chain
    have h := r3_chain (a+1) 0 0 e
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- d = 1: R3, R2, then R3 chain
    step fm
    step fm
    have h := r3_chain (a+1) 0 2 (e+1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- d = 2: R3, R2, R2, then R3 chain
    step fm
    step fm
    step fm
    have h := r3_chain (a+2) 0 1 (e+1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- d ≥ 3: R3, R2×3 cycle, then IH
    step fm
    apply stepStar_trans (r2_chain 3 a 0 d (e := e+1))
    apply stepStar_trans (ih d (by omega) (a+2) (e+1))
    ring_nf; finish

-- Phase D (m ≥ 2): (0, m, 1, 0, m) →* (1, 0, 0, 2*m-1, 0)
theorem phaseD : ⟨0, n+2, 1, 0, n+2⟩ [fm]⊢* ⟨1, 0, 0, 2*n+3, 0⟩ := by
  step fm
  step fm
  step fm
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n+1, 1⟩)
  · have h := r5r1_chain n 1 1
    rw [show 1 + n = n + 1 from by ring, show 1 + 2 * n = 2 * n + 1 from by ring] at h
    exact h
  step fm
  finish

-- Main transition: (1, 0, 0, n+1, 0) →⁺ (1, 0, 0, 2*n+3, 0)
theorem main_trans : ⟨1, 0, 0, n+1, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2*n+3, 0⟩ := by
  -- Phase AB: (1, 0, 0, n+1, 0) →* (0, 0, 2*n+5, 0, n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*n+5, 0, n+2⟩)
  · have h := phaseAB (n+1) 0 0
    rw [show 3 * (0 + 1) + 2 * (n + 1) = 2 * n + 5 from by ring,
        show 0 + 0 + 1 + (n + 1) = n + 2 from by ring] at h
    exact h
  -- Phase C (r4_chain): (0, 0, 2*n+5, 0, n+2) →* (0, n+2, 1, 0, n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, n+2, 1, 0, n+2⟩)
  · have h := r4_chain (n+2) 0 1 (e := n+2)
    rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase D: (0, n+2, 1, 0, n+2) →⁺ (1, 0, 0, 2*n+3, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, n+2, 1, 0, (n+1)+1⟩ = some ⟨1, n+2, 1, 2, n+1⟩
    rfl
  step fm
  step fm
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n+1, 1⟩)
  · have h := r5r1_chain n 1 1
    rw [show 1 + n = n + 1 from by ring, show 1 + 2 * n = 2 * n + 1 from by ring] at h
    exact h
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  have h : c₀ [fm]⊢⁺ ⟨1, 0, 0, 1, 0⟩ := by
    show c₀ [fm]⊢⁺ ⟨1, 0, 0, 1, 0⟩
    execute fm 5
  apply stepPlus_not_halts_not_halts h
  apply progress_nonhalt_simple (C := fun n ↦ (⟨1, 0, 0, n+1, 0⟩ : Q)) (i₀ := 0)
  intro n
  exact ⟨2*n + 2, main_trans⟩

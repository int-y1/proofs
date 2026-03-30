import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #682: [35/6, 4/385, 55/2, 3/5, 4/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1 -1 -1
-1  0  1  0  1
 0  1 -1  0  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_682

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- Phase 1: R3+R2 chain.
theorem r3r2_chain : ∀ k, ∀ a d, ⟨a + 1, 0, n, d + k, 0⟩ [fm]⊢* ⟨a + k + 1, 0, n, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- Phase 2: R3 chain.
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

-- Phase 3: R4 chain.
theorem r4_chain : ∀ k, ∀ b c, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c)
    ring_nf; finish

-- Phase 4: R1+R1+R2 chain.
theorem r1r1r2_chain : ∀ k, ∀ c,
    ⟨2, 2 * k + 1, c + 1, c + 1, k⟩ [fm]⊢* ⟨2, 1, c + k + 1, c + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show (k : ℕ) + 1 = k + 0 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- Full phase 1: (1, 0, n+1, n+1, 0) →⁺ (n+2, 0, n+1, 0, 0)
theorem phase1 (n : ℕ) : ⟨1, 0, n + 1, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, n + 1, 0, 0⟩ := by
  rw [show n + 1 = (n + 0) + 1 from by ring]
  step fm; step fm
  have h := r3r2_chain (n := n + 1) n 1 0
  simp only [Nat.zero_add] at h
  rw [show 1 + n + 1 = n + 2 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Full phase 2: (n+2, 0, n+1, 0, 0) →* (0, 0, 2n+3, 0, n+2)
theorem phase2 (n : ℕ) : ⟨n + 2, 0, n + 1, 0, 0⟩ [fm]⊢* ⟨0, 0, 2 * n + 3, 0, n + 2⟩ := by
  have h := r3_chain (n + 2) 0 (n + 1) 0
  simp only [Nat.zero_add] at h
  rw [show n + 1 + (n + 2) = 2 * n + 3 from by ring] at h
  exact h

-- Full phase 3: (0, 0, 2n+3, 0, n+2) →* (0, 2n+3, 0, 0, n+2)
theorem phase3 (n : ℕ) : ⟨0, 0, 2 * n + 3, 0, n + 2⟩ [fm]⊢* ⟨0, 2 * n + 3, 0, 0, n + 2⟩ := by
  have h := r4_chain (e := n + 2) (2 * n + 3) 0 0
  simp only [Nat.zero_add] at h
  exact h

-- Full phase 4: (0, 2n+3, 0, 0, n+2) →⁺ (1, 0, n+2, n+2, 0)
theorem phase4 (n : ℕ) : ⟨0, 2 * n + 3, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨1, 0, n + 2, n + 2, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  rw [show n + 1 = n + 0 + 1 from by ring]
  step fm
  have h := r1r1r2_chain n 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf
  step fm
  ring_nf; finish

-- Main transition.
theorem main_trans (n : ℕ) : ⟨1, 0, n + 1, n + 1, 0⟩ [fm]⊢⁺ ⟨1, 0, n + 2, n + 2, 0⟩ :=
  stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus (phase1 n) (stepStar_trans (phase2 n) (phase3 n)))
    (stepPlus_stepStar (phase4 n))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 1, 0⟩)
  · execute fm 4
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n + 1, n + 1, 0⟩) 0
  intro n; exists n + 1; exact main_trans n

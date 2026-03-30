import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #677: [35/6, 3/385, 4/5, 77/2, 15/7]

Vector representation:
```
-1 -1  1  1  0
 0  1 -1 -1 -1
 2  0 -1  0  0
-1  0  0  1  1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_677

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+k)
theorem r4_chain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- R5+R2 chain: (0, b, 0, d+2*k, e+k) →* (0, b+2*k, 0, d, e)
theorem r5_r2_chain : ∀ k b d e, ⟨0, b, 0, d + 2 * k, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih b (d + 2) (e + 1))
    step fm; step fm; ring_nf; finish

-- R3+R1+R1 chain: (0, 2*k, c+1, d, 0) →* (0, 0, c+k+1, d+2*k, 0)
theorem r3r1r1_chain : ∀ k c d, ⟨0, 2 * k, c + 1, d, 0⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2))
    ring_nf; finish

-- R3 chain (e=0): (a, 0, c+k, d, 0) →* (a+2*k, 0, c, d, 0)
theorem r3_chain : ∀ k a, ⟨a, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2))
    ring_nf; finish

-- Full cycle: (n+2, 0, 0, n+1, 0) →⁺ (2*n+4, 0, 0, 2*n+3, 0)
theorem main_trans : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
  -- Phase 1: R4 x (n+2): → (0, 0, 0, 2n+3, n+2)
  have phase1 : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * n + 3, n + 2⟩ := by
    rw [show n + 2 = 0 + (n + 2) from by ring]
    apply stepStar_trans (r4_chain (n + 2) (n + 1) 0)
    ring_nf; finish
  -- Phase 2: R5+R2 x (n+1): → (0, 2n+2, 0, 1, 1)
  have phase2 : ⟨0, 0, 0, 2 * n + 3, n + 2⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, 1, 1⟩ := by
    rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
        show n + 2 = 1 + (n + 1) from by ring]
    apply stepStar_trans (r5_r2_chain (n + 1) 0 1 1)
    ring_nf; finish
  -- R5: (0, 2n+2, 0, 1, 1) → (0, 2n+3, 1, 0, 1)
  have phase2b : ⟨0, 2 * n + 2, 0, 1, 1⟩ [fm]⊢* ⟨0, 2 * n + 3, 1, 0, 1⟩ := by
    step fm; ring_nf; finish
  -- Mini-phase (4 steps): R3,R1,R1,R2: → (0, 2n+2, 1, 1, 0)
  have phase_mini : ⟨0, 2 * n + 3, 1, 0, 1⟩ [fm]⊢* ⟨0, 2 * n + 2, 1, 1, 0⟩ := by
    step fm; step fm; step fm; step fm; ring_nf; finish
  -- Phase 3: R3+R1+R1 x (n+1): → (0, 0, n+2, 2n+3, 0)
  have phase3 : ⟨0, 2 * n + 2, 1, 1, 0⟩ [fm]⊢* ⟨0, 0, n + 2, 2 * n + 3, 0⟩ := by
    rw [show 2 * n + 2 = 2 * (n + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r3r1r1_chain (n + 1) 0 1)
    ring_nf; finish
  -- Phase 4: R3 x (n+2): → (2n+4, 0, 0, 2n+3, 0)
  have phase4 : ⟨0, 0, n + 2, 2 * n + 3, 0⟩ [fm]⊢* ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
    rw [show n + 2 = 0 + (n + 2) from by ring]
    apply stepStar_trans (r3_chain (n + 2) 0 (c := 0) (d := 2 * n + 3))
    ring_nf; finish
  -- Compose: need ⊢⁺, so use the fact that at least one step is taken
  exact stepStar_stepPlus
    (stepStar_trans phase1 (stepStar_trans phase2 (stepStar_trans phase2b
      (stepStar_trans phase_mini (stepStar_trans phase3 phase4)))))
    (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exact ⟨2 * n + 2, main_trans⟩

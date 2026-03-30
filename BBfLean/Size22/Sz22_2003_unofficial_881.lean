import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #881: [4/15, 1029/2, 11/3, 5/539, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  3  0
 0 -1  0  0  1
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_881

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2 chain: drain a to b, add 3 to d per step
theorem r2_chain : ∀ k a b d e, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + k, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) (d + 3) e); ring_nf; finish

-- R3 chain: drain b to e
theorem r3_chain : ∀ k b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih b d (e + 1)); ring_nf; finish

-- R4 chain: drain e, reduce d by 2, add 1 to c per step
theorem r4_chain : ∀ k c d, ⟨0, 0, c, d + 2 * k, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    show ⟨0, 0, c, (d + 2 * k) + 2, k + 1⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R2+R1 interleaved chain
theorem r2r1_chain : ∀ k a c d, ⟨a + 2, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 2 + k, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show a + 2 = (a + 1) + 1 from by ring]
    step fm
    show ⟨a + 1, 0 + 1, (c + k) + 1, d + 3, 0⟩ [fm]⊢* _
    step fm
    show ⟨(a + 1) + 2, 0, c + k, d + 3, 0⟩ [fm]⊢* _
    apply stepStar_trans (ih (a + 1) c (d + 3))
    ring_nf; finish

-- Full cycle
theorem full_cycle (n : ℕ) : ⟨n + 2, 0, 0, 2 * (n + 1) * n, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 2 * (n + 2) * (n + 1), 0⟩ := by
  -- Phase 1: R2 chain (n+2 steps)
  have h1 := r2_chain (n + 2) 0 0 (2 * (n + 1) * n) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- Phase 2: R3 chain (n+2 steps)
  have h2 := r3_chain (n + 2) 0 (2 * (n + 1) * n + 3 * (n + 2)) 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- Phase 3: R4 chain (n+2 steps)
  have h3 : ⟨0, 0, 0, 2 * (n + 1) * n + 3 * (n + 2), n + 2⟩ [fm]⊢* ⟨0, 0, n + 2, 2 * n * n + 3 * n + 2, 0⟩ := by
    rw [show 2 * (n + 1) * n + 3 * (n + 2) = (2 * n * n + 3 * n + 2) + 2 * (n + 2) from by ring]
    have h := r4_chain (n + 2) 0 (2 * n * n + 3 * n + 2)
    simp only [Nat.zero_add] at h
    exact h
  apply stepStar_trans h3
  -- Phase 4: R5 step
  rw [show 2 * n * n + 3 * n + 2 = (2 * n * n + 3 * n + 1) + 1 from by ring]
  step fm
  -- Phase 5: R1 step
  show ⟨0, 0 + 1, (n + 1) + 1, 2 * n * n + 3 * n + 1, 0⟩ [fm]⊢* _
  step fm
  -- Phase 6: R2+R1 interleaved (n+1 rounds)
  show ⟨0 + 2, 0, n + 1, 2 * n * n + 3 * n + 1, 0⟩ [fm]⊢* _
  have h6 := r2r1_chain (n + 1) 0 0 (2 * n * n + 3 * n + 1)
  simp only [Nat.zero_add] at h6
  apply stepStar_trans h6
  rw [show 2 + (n + 1) = n + 3 from by ring,
      show 2 * n * n + 3 * n + 1 + 3 * (n + 1) = 2 * (n + 2) * (n + 1) from by ring]
  finish

-- ⊢⁺ via showing states differ
theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 2 * (n + 1) * n, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * (n + 2) * (n + 1), 0⟩ := by
  apply stepStar_stepPlus (full_cycle n)
  intro h
  have := (Prod.mk.inj h).1
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * (n + 1) * n, 0⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 2 * ((n + 1) + 1) * (n + 1) = 2 * (n + 2) * (n + 1) from by ring]
  exact main_trans n

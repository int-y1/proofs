import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #970: [4/15, 33/14, 5/2, 7/11, 66/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 1  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_970

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 2, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 + k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 0, n⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, n + 1⟩ := by
  rcases n with _ | n
  · -- n = 0: (0,0,1,0,0) -> R5 -> R3 -> R1 -> R3 drain -> (0,0,2,0,1)
    execute fm 5
  · -- n + 1 >= 1
    -- Phase 1: R4 drain: (0,0,n+2,0,n+1) ⊢* (0,0,n+2,n+1,0)
    have h1 : ⟨0, 0, n + 2, 0, n + 1⟩ [fm]⊢* ⟨0, 0, n + 2, n + 1, 0⟩ := by
      have := r4_drain (n + 1) (n + 2) 0
      rw [show 0 + (n + 1) = n + 1 from by ring] at this
      exact this
    -- Phase 2: R5: (0,0,n+2,n+1,0) -> (1,1,n+1,n+1,1)
    have h2 : ⟨0, 0, n + 2, n + 1, 0⟩ [fm]⊢⁺ ⟨1, 1, n + 1, n + 1, 1⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      apply step_stepPlus
      show fm ⟨0, 0, (n + 1) + 1, n + 1, 0⟩ = some ⟨1, 1, n + 1, n + 1, 1⟩
      unfold fm; simp only
    -- Phase 3: R1: (1,1,n+1,n+1,1) -> (3,0,n,n+1,1)
    have h3 : ⟨1, 1, n + 1, n + 1, 1⟩ [fm]⊢* ⟨3, 0, n, n + 1, 1⟩ := by
      rw [show n + 1 = n + 1 from rfl]
      step fm; ring_nf; finish
    -- Phase 4: R2+R1 chain n rounds: (3,0,n,n+1,1) ⊢* (n+3,0,0,1,n+1)
    have h4 : ⟨3, 0, n, n + 1, 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 1, n + 1⟩ := by
      have := r2r1_chain n 1 0 1 1
      simp only [show 1 + 2 = 3 from by ring,
          show 0 + n = n from by ring,
          show 1 + n = n + 1 from by ring,
          show 1 + 2 + n = n + 3 from by ring] at this
      exact this
    -- Phase 5: R2: (n+3,0,0,1,n+1) -> (n+2,1,0,0,n+2)
    have h5 : ⟨n + 3, 0, 0, 1, n + 1⟩ [fm]⊢* ⟨n + 2, 1, 0, 0, n + 2⟩ := by
      rw [show n + 3 = (n + 2) + 1 from by ring]
      step fm; ring_nf; finish
    -- Phase 6: R3 + R1: (n+2,1,0,0,n+2) -> (n+1,1,1,0,n+2) -> (n+3,0,0,0,n+2)
    have h6 : ⟨n + 2, 1, 0, 0, n + 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, n + 2⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm; step fm; ring_nf; finish
    -- Phase 7: R3 drain: (n+3,0,0,0,n+2) ⊢* (0,0,n+3,0,n+2)
    have h7 : ⟨n + 3, 0, 0, 0, n + 2⟩ [fm]⊢* ⟨0, 0, n + 3, 0, n + 2⟩ := by
      have := r3_drain (n + 3) 0 (n + 2)
      rw [show 0 + (n + 3) = n + 3 from by ring] at this
      exact this
    -- Compose all phases
    exact stepStar_stepPlus_stepPlus h1
      (stepPlus_stepStar_stepPlus h2
        (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 1, 0, n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, n + 1, 0, n⟩ [fm]⊢⁺ ⟨0, 0, (n + 1) + 1, 0, n + 1⟩
  rw [show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n

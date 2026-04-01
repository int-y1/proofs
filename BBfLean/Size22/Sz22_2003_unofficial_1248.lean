import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1248: [5/6, 77/2, 52/35, 3/13, 18/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 1  2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1248

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | _ => none

-- R4 repeated: move f to b
theorem f_to_b : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R3,R1,R1 chain: each round consumes 2 from b, 1 from d, adds 1 to c and f
theorem r3r1r1_chain : ∀ k b c d e f,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 1 + k, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e f)
    rw [show c + 1 + k = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + k + 2 = c + 1 + (k + 1) from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

-- R3,R2,R2 chain: each round consumes 1 from c, adds 1 to d, 2 to e, 1 to f
theorem r3r2r2_chain : ∀ k c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + k + 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 2) (f + 1))
    rw [show d + 1 + k + 1 = d + (k + 1) + 1 from by ring,
        show e + 2 + 2 * k = e + 2 * (k + 1) from by ring,
        show f + 1 + k = f + (k + 1) from by ring]
    finish

-- Full transition from one canonical state to the next
-- Canonical state n: (0, 0, 0, n+2, n²+3n+3, 2n+2)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, n * n + 3 * n + 3, 2 * n + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 3, n * n + 5 * n + 7, 2 * n + 4⟩ := by
  -- Phase 1: f_to_b (move f=2n+2 to b)
  -- (0,0,0,n+2,n²+3n+3,2n+2) →* (0,2n+2,0,n+2,n²+3n+3,0)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * n + 2) 0 (n + 2) (n * n + 3 * n + 3) 0)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 2: R5 (e≥1, f=0)
  -- (0,2n+2,0,n+2,n²+3n+3,0) → (1,2n+4,0,n+2,n²+3n+2,0)
  rw [show n * n + 3 * n + 3 = (n * n + 3 * n + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n + 2, 0, n + 2, (n * n + 3 * n + 2) + 1, 0⟩ : Q) [fm]⊢
      ⟨1, 2 * n + 4, 0, n + 2, n * n + 3 * n + 2, 0⟩)
  -- Phase 3: R1 (a=1,b≥1)
  -- (1,2n+4,0,n+2,n²+3n+2,0) → (0,2n+3,1,n+2,n²+3n+2,0)
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, (2 * n + 3) + 1, 0, n + 2, n * n + 3 * n + 2, 0⟩ : Q) [fm]⊢
      ⟨0, 2 * n + 3, 1, n + 2, n * n + 3 * n + 2, 0⟩))
  -- Phase 4: R3,R1,R1 chain (n+1 rounds)
  -- (0,2n+3,1,n+2,n²+3n+2,0) →* (0,1,n+2,1,n²+3n+2,n+1)
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
      show n + 2 = 1 + (n + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain (n + 1) 1 0 1 (n * n + 3 * n + 2) 0)
  rw [show 0 + 1 + (n + 1) = n + 2 from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  -- Phase 5: R3 (c=n+2≥1, d=1≥1)
  -- (0,1,n+2,1,n²+3n+2,n+1) → (2,1,n+1,0,n²+3n+2,n+2)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 1, (n + 1) + 1, 0 + 1, n * n + 3 * n + 2, n + 1⟩ : Q) [fm]⊢
      ⟨2, 1, n + 1, 0, n * n + 3 * n + 2, n + 2⟩))
  -- Phase 6: R1 (a=2,b=1)
  -- (2,1,n+1,0,n²+3n+2,n+2) → (1,0,n+2,0,n²+3n+2,n+2)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, 1, n + 1, 0, n * n + 3 * n + 2, n + 2⟩ : Q) [fm]⊢
      ⟨1, 0, n + 2, 0, n * n + 3 * n + 2, n + 2⟩))
  -- Phase 7: R2 (a=1,b=0)
  -- (1,0,n+2,0,n²+3n+2,n+2) → (0,0,n+2,1,n²+3n+3,n+2)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, n + 2, 0, n * n + 3 * n + 2, n + 2⟩ : Q) [fm]⊢
      ⟨0, 0, n + 2, 1, n * n + 3 * n + 3, n + 2⟩))
  -- Phase 8: R3,R2,R2 chain (n+2 rounds)
  -- (0,0,n+2,1,n²+3n+3,n+2) →* (0,0,0,n+3,n²+5n+7,2n+4)
  have phase8 : ⟨(0 : ℕ), (0 : ℕ), n + 2, 1, n * n + 3 * n + 3, n + 2⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), 0, n + 3, n * n + 5 * n + 7, 2 * n + 4⟩ := by
    have h := r3r2r2_chain (n + 2) 0 0 (n * n + 3 * n + 3) (n + 2)
    rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
        show 0 + (n + 2) = n + 2 from by ring,
        show n * n + 3 * n + 3 + 2 * (n + 2) = n * n + 5 * n + 7 from by ring,
        show n + 2 + (n + 2) = 2 * n + 4 from by ring] at h
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    exact h
  rw [show 0 + 1 + 2 * (n + (0 + 1)) + (0 + 1) = 2 * n + 4 from by ring]
  exact phase8

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 3, 2⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, n * n + 3 * n + 3, 2 * n + 2⟩) 0
  intro n; exists n + 1
  show ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, n * n + 3 * n + 3, 2 * n + 2⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, n + 1 + 2, (n + 1) * (n + 1) + 3 * (n + 1) + 3, 2 * (n + 1) + 2⟩
  have h := main_trans n
  rw [show n * n + 5 * n + 7 = (n + 1) * (n + 1) + 3 * (n + 1) + 3 from by ring,
      show 2 * n + 4 = 2 * (n + 1) + 2 from by ring,
      show n + 3 = n + 1 + 2 from by ring] at h
  exact h

end Sz22_2003_unofficial_1248

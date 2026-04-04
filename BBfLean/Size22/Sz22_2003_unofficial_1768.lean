import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1768: [9/10, 2401/2, 22/21, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  4  0
 1 -1  0 -1  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1768

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+4, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: move e to c.
theorem e_to_c : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

-- (R3,R1) interleave: k rounds.
theorem r3r1_chain : ∀ k b c d e,
    ⟨0, b + 1, c + k, d + 1 + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 1 + k, c, d + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + 1 + k = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 1) c d (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring,
        show b + 1 + 1 + k = b + 1 + (k + 1) from by ring]; finish

-- (R3,R2) drain: k rounds.
theorem r3r2_drain : ∀ k b d e,
    ⟨0, b + k, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d + 4 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + k + 4 = (d + 4) + k from by ring]
    apply stepStar_trans (ih b (d + 4) (e + 1))
    rw [show d + 4 + 4 * k = d + 4 * (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

-- Phase 1+2: (0,0,0,2*n+4,n) →* (0,1,n,2*n+3,0)
theorem phase12 (n : ℕ) : ⟨0, 0, 0, 2 * n + 4, n⟩ [fm]⊢* ⟨(0 : ℕ), 1, n, 2 * n + 3, 0⟩ := by
  have h1 := e_to_c n 0 (2 * n + 4) 0
  rw [show (0 : ℕ) + n = n from by ring] at h1
  apply stepStar_trans h1
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm; finish

-- Phase 3: (0,1,n,2*n+3,0) →* (0,n+1,0,n+3,n)
theorem phase3 (n : ℕ) : ⟨0, 1, n, 2 * n + 3, 0⟩ [fm]⊢* ⟨(0 : ℕ), n + 1, 0, n + 3, n⟩ := by
  have h := r3r1_chain n 0 0 (n + 2) 0
  rw [show (0 : ℕ) + 1 + n = n + 1 from by ring,
      show (n + 2 : ℕ) + 1 = n + 3 from by ring,
      show (0 : ℕ) + n = n from by ring,
      show (0 : ℕ) + 1 = 1 from by ring,
      show (n + 2 : ℕ) + 1 + n = 2 * n + 3 from by ring] at h
  exact h

-- Phase 4: (0,n+1,0,n+3,n) →* (0,0,0,4*n+6,2*n+1)
theorem phase4 (n : ℕ) : ⟨0, n + 1, 0, n + 3, n⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 4 * n + 6, 2 * n + 1⟩ := by
  have h := r3r2_drain (n + 1) 0 2 n
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring,
      show (2 : ℕ) + (n + 1) = n + 3 from by ring,
      show 2 + 4 * (n + 1) = 4 * n + 6 from by ring,
      show n + (n + 1) = 2 * n + 1 from by ring] at h
  exact h

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n + 4, n⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 4 * n + 6, 2 * n + 1⟩ := by
  apply stepStar_stepPlus
  · exact stepStar_trans (stepStar_trans (phase12 n) (phase3 n)) (phase4 n)
  · intro h; simp [Q] at h; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 4, n⟩) 0
  intro n; refine ⟨2 * n + 1, ?_⟩
  have h := main_trans n
  rw [show 4 * n + 6 = 2 * (2 * n + 1) + 4 from by ring] at h
  exact h

end Sz22_2003_unofficial_1768

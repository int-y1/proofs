import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1540: [7/30, 3/77, 605/3, 4/11, 21/2]

Vector representation:
```
-1 -1 -1  1  0
 0  1  0 -1 -1
 0 -1  1  0  2
 2  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1540

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4: transfer e to a (when b=0, d=0)
theorem e_to_a : ∀ k a, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a; exists 0
  · intro a; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (a + 2)); ring_nf; finish

-- R5R1 chain: alternating R5,R1 draining a,c and building d
theorem r5r1_chain : ∀ k, ∀ a c d,
    ⟨a + 2 * k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c d; exists 0
  · intro a c d
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- R3 drain: transfer b to c,e (when a=0, d=0)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 1) (e + 2)); ring_nf; finish

-- R2R2R3 chain: 3-step rounds (R2,R2,R3) with e cycling 2→1→0→2
theorem r2r2r3_chain : ∀ k, ∀ j C,
    ⟨0, j, C + j, 2 * k + 2, 2⟩ [fm]⊢* ⟨0, j + k + 1, C + j + k + 1, 0, 2⟩ := by
  intro k; induction' k with k ih
  · intro j C
    step fm; step fm; step fm; ring_nf; finish
  · intro j C
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (j + 1) C); ring_nf; finish

-- Compose phases for n≥1: (2, 0, 0, 2n+2, 0) ⊢⁺ (4n+8, 0, 2n+3, 0, 0)
theorem phases_succ (n : ℕ) :
    ⟨2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨4 * n + 8, 0, 2 * n + 3, 0, 0⟩ := by
  -- 6 special steps: (2, 0, 0, 2n+2, 0) → (0, 0, 1, 2n+2, 2)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- R2R2R3 chain: (0, 0, 1, 2n+2, 2) →* (0, n+1, n+2, 0, 2)
  rw [show (1 : ℕ) = 1 + 0 from by ring]
  apply stepStar_trans (r2r2r3_chain n 0 1)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 1 + 0 + n + 1 = n + 2 from by ring]
  -- R3 drain: (0, n+1, n+2, 0, 2) →* (0, 0, 2n+3, 0, 2n+4)
  apply stepStar_trans (r3_drain (n + 1) (n + 2) 2)
  rw [show n + 2 + (n + 1) = 2 * n + 3 from by ring,
      show 2 + 2 * (n + 1) = 2 * n + 4 from by ring,
      show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
  -- R4 chain: (0, 0, 2n+3, 0, 2n+4) →* (4n+8, 0, 2n+3, 0, 0)
  apply stepStar_trans (e_to_a (2 * n + 4) 0 (c := 2 * n + 3) (e := 0))
  ring_nf; finish

-- R5R1 chain variant: (2+2n, 0, n, 0, 0) →* (2, 0, 0, 2n, 0)
theorem r5r1_phase : ∀ n, ∀ d,
    ⟨2 * n + 2, 0, n, d, 0⟩ [fm]⊢* ⟨2, 0, 0, d + 2 * n, 0⟩ := by
  intro n; induction' n with n ih
  · intro d; exists 0
  · intro d
    rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 2)); ring_nf; finish

-- Main transition: (2n+2, 0, n, 0, 0) ⊢⁺ (4n+4, 0, 2n+1, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 2, 0, n, 0, 0⟩ [fm]⊢⁺ ⟨4 * n + 4, 0, 2 * n + 1, 0, 0⟩ := by
  rcases n with _ | n'
  · -- n=0: (2,0,0,0,0) ⊢⁺ (4,0,1,0,0)
    step fm; step fm; step fm; step fm
    step fm; step fm; step fm; step fm; finish
  · -- n≥1: R5R1 phase then phases_succ
    apply stepStar_stepPlus_stepPlus (r5r1_phase (n' + 1) 0)
    rw [show (0 + 2 * (n' + 1) : ℕ) = 2 * n' + 2 from by ring]
    have h := phases_succ n'
    rw [show 4 * n' + 8 = 4 * (n' + 1) + 4 from by ring,
        show 2 * n' + 3 = 2 * (n' + 1) + 1 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 2, 0, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, n, 0, 0⟩) 2
  intro n; exact ⟨2 * n + 1, by
    rw [show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1540

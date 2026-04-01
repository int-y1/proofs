import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1521: [7/15, 99/70, 22/3, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2 -1 -1  1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1521

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move e to c
theorem e_to_c : ∀ k, ∀ c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- R2R1R1 chain: (k+1, 0, 3*k+2, d+1, e) →* (1, 0, 2, d+1+k, e+k)
theorem r2r1r1_chain : ∀ k, ∀ d e, ⟨k + 1, 0, 3 * k + 2, d + 1, e⟩ [fm]⊢*
    ⟨1, 0, 2, d + 1 + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
        show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- Final drain: (1, 0, 2, d+1, e) →⁺ (1, 0, 0, d+1, e+2)
theorem final_drain : ⟨1, 0, 2, d + 1, e⟩ [fm]⊢⁺ ⟨1, 0, 0, d + 1, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- Inner loop: (a+1, 0, 0, j, e+1) →* (a+1+j, 0, 0, 0, e+1+2*j)
theorem inner_loop : ∀ j, ∀ a e, ⟨a + 1, 0, 0, j, e + 1⟩ [fm]⊢*
    ⟨a + 1 + j, 0, 0, 0, e + 1 + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  · step fm; step fm; step fm; step fm
    show ⟨a + 2, 0, 0, j, e + 1 + 1 + 1⟩ [fm]⊢* _
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring,
        show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 3*n+3) →⁺ (n+3, 0, 0, 0, 3*n+6)
theorem main_trans : ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 3 * n + 6⟩ := by
  -- Phase 1: e_to_c
  rw [show (3 * n + 3 : ℕ) = 0 + (3 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 3) (c := 0) (a := n + 2) (e := 0))
  rw [show 0 + (3 * n + 3) = (3 * n + 2) + 1 from by ring]
  -- R5 + R1
  step fm; step fm
  -- r2r1r1 chain + final drain + inner loop
  show ⟨n + 1, 0, 3 * n + 2, 2, 0⟩ [fm]⊢* _
  apply stepStar_trans (r2r1r1_chain n 1 0)
  show ⟨1, 0, 2, 1 + 1 + n, 0 + n⟩ [fm]⊢* _
  rw [show 1 + 1 + n = (n + 1) + 1 from by ring, show 0 + n = n from by ring]
  apply stepStar_trans (stepPlus_stepStar final_drain)
  show ⟨1, 0, 0, n + 2, n + 2⟩ [fm]⊢* _
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  apply stepStar_trans (inner_loop (n + 2) 0 (n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n => ⟨n + 2, 0, 0, 0, 3 * n + 3⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩

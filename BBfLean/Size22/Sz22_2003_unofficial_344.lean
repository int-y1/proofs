import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #344: [2/15, 1/14, 99/2, 49/33, 50/7]

Vector representation:
```
 1 -1 -1  0  0
-1  0  0 -1  0
-1  2  0  0  1
 0 -1  0  2 -1
 1  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_344

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

theorem rule4_chain (j b d e : ℕ) :
    ⟨0, b+j, 0, d, e+j⟩ [fm]⊢* ⟨0, b, 0, d+2*j, e⟩ := by
  induction j generalizing d with
  | zero => exists 0
  | succ j ih =>
    rw [show b + (j + 1) = (b + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    rw [show d + 2 * (j + 1) = (d + 2) + 2 * j from by ring]
    exact ih (d + 2)

theorem phase2_init (d : ℕ) :
    ⟨0, 1, 0, d+4, 0⟩ [fm]⊢* ⟨1, 0, 3, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem consume_d_loop (j c d : ℕ) :
    ⟨1, 0, c, d+2*j, 0⟩ [fm]⊢* ⟨1, 0, c+2*j, d, 0⟩ := by
  induction j generalizing c with
  | zero => exists 0
  | succ j ih =>
    rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring]
    step fm; step fm
    rw [show c + 2 * (j + 1) = (c + 2) + 2 * j from by ring]
    exact ih (c + 2)

theorem r3r1r1_loop (j a c e : ℕ) :
    ⟨a+1, 0, c+2*j, 0, e⟩ [fm]⊢* ⟨a+j+1, 0, c, 0, e+j⟩ := by
  induction j generalizing a e with
  | zero => exists 0
  | succ j ih =>
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + (j + 1) + 1 = (a + 1) + j + 1 from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    exact ih (a + 1) (e + 1)

theorem r3r1_tail (a e : ℕ) :
    ⟨a+1, 0, 1, 0, e⟩ [fm]⊢* ⟨a+1, 1, 0, 0, e+1⟩ := by
  step fm; step fm; ring_nf; finish

theorem r3_chain (j a b e : ℕ) :
    ⟨a+j, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+2*j, 0, 0, e+j⟩ := by
  induction j generalizing b e with
  | zero => exists 0
  | succ j ih =>
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    rw [show b + 2 * (j + 1) = (b + 2) + 2 * j from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    exact ih (b + 2) (e + 1)

theorem main_trans (n : ℕ) :
    ⟨0, 2*n+3, 0, 0, 2*n+2⟩ [fm]⊢⁺ ⟨0, 4*n+5, 0, 0, 4*n+4⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2*n+2)+1, 0, 0, (2*n+1)+1⟩ = some ⟨0, 2*n+2, 0, 2, 2*n+1⟩
    rfl
  apply stepStar_trans
  · have h := rule4_chain (2*n+1) 1 2 0
    rw [show 1 + (2*n+1) = 2*n+2 from by ring,
        show 0 + (2*n+1) = 2*n+1 from by ring,
        show 2 + 2*(2*n+1) = 4*n+4 from by ring] at h
    exact h
  apply stepStar_trans
  · exact phase2_init (4*n)
  apply stepStar_trans
  · have h := consume_d_loop (2*n) 3 0
    rw [show 0 + 2*(2*n) = 4*n from by ring,
        show 3 + 2*(2*n) = 4*n+3 from by ring] at h
    exact h
  apply stepStar_trans
  · have h := r3r1r1_loop (2*n+1) 0 1 0
    rw [show 1 + 2*(2*n+1) = 4*n+3 from by ring,
        show 0 + (2*n+1) + 1 = 2*n+2 from by ring,
        show 0 + (2*n+1) = 2*n+1 from by ring] at h
    exact h
  apply stepStar_trans
  · have h := r3r1_tail (2*n+1) (2*n+1)
    rw [show 2*n+1+1 = 2*n+2 from by ring,
        show 2*n+1+1 = 2*n+2 from by ring] at h
    exact h
  have h := r3_chain (2*n+2) 0 1 (2*n+2)
  rw [show 0 + (2*n+2) = 2*n+2 from by ring,
      show 1 + 2*(2*n+2) = 4*n+5 from by ring,
      show 2*n+2 + (2*n+2) = 4*n+4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2*n+3, 0, 0, 2*n+2⟩) 0
  intro n
  refine ⟨2*n+1, ?_⟩
  have h := main_trans n
  rw [show 4*n+5 = 2*(2*n+1)+3 from by ring,
      show 4*n+4 = 2*(2*n+1)+2 from by ring] at h
  exact h

end Sz22_2003_unofficial_344

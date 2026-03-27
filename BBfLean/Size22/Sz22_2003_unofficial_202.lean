import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #202: [1/6, 35/2, 28/55, 3/5, 242/21]

Vector representation:
```
-1 -1  0  0  0
-1  0  1  1  0
 2  0 -1  1 -1
 0  1 -1  0  0
 1 -1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_202

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Rule 3 + Rule 2 + Rule 2 loop: consume e, grow c and d.
theorem grow_c : ∀ k c D, ⟨(0 : ℕ), 0, c + 1, D, k⟩ [fm]⊢* ⟨0, 0, c + 1 + k, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c D
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Rule 4 loop: convert c to b.
theorem c_to_b : ∀ C b, ⟨(0 : ℕ), b, C + 1, D, 0⟩ [fm]⊢* ⟨0, b + C + 1, 0, D, 0⟩ := by
  intro C; induction' C with C ih <;> intro b
  · step fm; finish
  · step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Rule 5 + Rule 1 loop: drain b (odd), accumulate e.
theorem drain_b : ∀ m D e, ⟨(0 : ℕ), 2 * m + 1, 0, D + m + 1, e⟩ [fm]⊢* ⟨1, 0, 0, D, e + 2 * m + 2⟩ := by
  intro m; induction' m with m ih <;> intro D e
  · step fm; finish
  · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 from by ring,
        show D + (m + 1) + 1 = D + 1 + (m + 1) from by ring]
    step fm; step fm
    show ⟨(0 : ℕ), 2 * m + 1, 0, (D + 1) + m, e + 2⟩ [fm]⊢*
         ⟨1, 0, 0, D, e + 2 * (m + 1) + 2⟩
    rw [show (D + 1) + m = D + m + 1 from by ring]
    apply stepStar_trans (ih D (e + 2))
    ring_nf; finish

-- Define the recurring function for d
def f : ℕ → ℕ
  | 0 => 0
  | n + 1 => f n + 5 * n

-- The main cycle
theorem cycle (n : ℕ) : ⟨(1 : ℕ), 0, 0, f n, 2 * n⟩ [fm]⊢⁺ ⟨1, 0, 0, f (n + 1), 2 * (n + 1)⟩ := by
  show ⟨(1 : ℕ), 0, 0, f n, 2 * n⟩ [fm]⊢⁺ ⟨1, 0, 0, f n + 5 * n, 2 * n + 2⟩
  -- Phase 1: rule 2
  step fm
  -- Phase 2: grow_c
  apply stepStar_trans (grow_c (2 * n) 0 (f n + 1))
  rw [show (0 : ℕ) + 1 + 2 * n = 2 * n + 1 from by ring,
      show f n + 1 + 3 * (2 * n) = f n + 6 * n + 1 from by ring]
  -- Phase 3: c_to_b
  rw [show 2 * n + 1 = 2 * n + 0 + 1 from by ring]
  apply stepStar_trans (c_to_b (D := f n + 6 * n + 1) (2 * n) 0)
  rw [show (0 : ℕ) + 2 * n + 1 = 2 * n + 1 from by ring]
  -- Phase 4: drain_b
  rw [show f n + 6 * n + 1 = (f n + 5 * n) + n + 1 from by ring]
  apply stepStar_trans (drain_b n (f n + 5 * n) 0)
  ring_nf; finish

def C (n : ℕ) : Q := ⟨1, 0, 0, f n, 2 * n⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := C 0) (by exists 0)
  exact progress_nonhalt_simple C 0 (fun n ↦ ⟨n + 1, cycle n⟩)

end Sz22_2003_unofficial_202

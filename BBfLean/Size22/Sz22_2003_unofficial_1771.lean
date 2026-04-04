import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1771: [9/10, 275/21, 2/3, 7/11, 165/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  2 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1771

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (d + 1) e); ring_nf; finish

theorem b_to_a : ∀ k a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 1) b e); ring_nf; finish

theorem drain_c_d0 : ∀ c a b e, ⟨a, b + 1, c, 0, e⟩ [fm]⊢* ⟨a + b + 1 + c, 0, 0, 0, e⟩ := by
  intro c; induction' c with c ih <;> intro a b e
  · rw [show a + b + 1 + 0 = a + (b + 1) from by ring]
    rw [show b + 1 = 0 + (b + 1) from by ring]
    apply stepStar_trans (b_to_a (b + 1) a 0 e)
    ring_nf; finish
  · rcases a with _ | a
    · step fm; step fm
      apply stepStar_trans (ih 0 (b + 1) e)
      ring_nf; finish
    · step fm
      apply stepStar_trans (ih a (b + 2) e)
      ring_nf; finish

theorem r2r1r1_chain : ∀ k a b d e, ⟨a + 2 * k, b + 1, 0, d + k, e⟩ [fm]⊢*
    ⟨a, b + 1 + 3 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm -- R2
    step fm -- R1
    step fm -- R1
    apply stepStar_trans (ih a (b + 3) d (e + 1))
    ring_nf; finish

theorem last_round : ∀ a b e, ⟨a, b + 2, 0, 1, e⟩ [fm]⊢⁺ ⟨a + b + 3, 0, 0, 0, e + 1⟩ := by
  intro a b e
  step fm -- R2: (a, b+1, 2, 0, e+1)
  apply stepStar_trans (drain_c_d0 2 a b (e + 1))
  ring_nf; finish

theorem main_trans (a d : ℕ) :
    ⟨a + 2 * d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 3 * d + 4, 0, 0, d + 2, 0⟩ := by
  rw [show a + 2 * d + 2 = (a + 2 * d + 1) + 1 from by ring]
  step fm -- R5
  rw [show a + 2 * d + 1 = (a + 2 * d) + 1 from by ring]
  step fm -- R1
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show d + 1 = 1 + d from by ring]
  apply stepStar_trans (r2r1r1_chain d a 2 1 1)
  rw [show 2 + 1 + 3 * d = (3 * d + 1) + 2 from by ring,
      show 1 + d = d + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (last_round a (3 * d + 1) (d + 1)))
  rw [show a + (3 * d + 1) + 3 = a + 3 * d + 4 from by ring,
      show d + 1 + 1 = d + 2 from by ring,
      show (a + 3 * d + 4 : ℕ) = a + 3 * d + 4 from by ring,
      show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
  exact e_to_d (d + 2) (a + 3 * d + 4) 0 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 2 * d + 2, 0, 0, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  refine ⟨⟨a + d, d + 1⟩, ?_⟩
  show ⟨a + 2 * d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨(a + d) + 2 * (d + 1) + 2, 0, 0, (d + 1) + 1, 0⟩
  rw [show (a + d) + 2 * (d + 1) + 2 = a + 3 * d + 4 from by ring]
  exact main_trans a d

end Sz22_2003_unofficial_1771

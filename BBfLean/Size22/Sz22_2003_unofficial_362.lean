import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #362: [2/15, 3/14, 275/2, 7/5, 12/77]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 2  1  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_362

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ j c e,
    (⟨j, 0, c, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, c + 2 * j, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intro c e; simp; exists 0
  | succ j ih =>
    intro c e
    apply stepStar_trans
    · show ⟨j + 1, 0, c, 0, e⟩ [fm]⊢* ⟨j, 0, c + 2, 0, e + 1⟩
      step fm; ring_nf; finish
    apply stepStar_trans (ih (c + 2) (e + 1))
    rw [show c + 2 + 2 * j = c + 2 * (j + 1) from by ring,
        show e + 1 + j = e + (j + 1) from by ring]
    finish

theorem r4_chain : ∀ j d e,
    (⟨0, 0, j, d, e⟩ : Q) [fm]⊢* ⟨0, 0, 0, d + j, e⟩ := by
  intro j; induction j with
  | zero => intro d e; simp; exists 0
  | succ j ih =>
    intro d e
    apply stepStar_trans
    · show ⟨0, 0, j + 1, d, e⟩ [fm]⊢* ⟨0, 0, j, d + 1, e⟩
      step fm; ring_nf; finish
    apply stepStar_trans (ih (d + 1) e)
    rw [show d + 1 + j = d + (j + 1) from by ring]
    finish

theorem r5r2r2_one : ∀ b d e,
    (⟨0, b, 0, d + 3, e + 1⟩ : Q) [fm]⊢* ⟨0, b + 3, 0, d, e⟩ := by
  intro b d e
  step fm; step fm; step fm; ring_nf; finish

theorem r5r2r2_iter : ∀ j b d e,
    (⟨0, b, 0, d + 3 * j, e + j⟩ : Q) [fm]⊢* ⟨0, b + 3 * j, 0, d, e⟩ := by
  intro j; induction j with
  | zero => intro b d e; simp; exists 0
  | succ j ih =>
    intro b d e
    rw [show d + 3 * (j + 1) = (d + 3) + 3 * j from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    apply stepStar_trans (ih b (d + 3) (e + 1))
    apply stepStar_trans (r5r2r2_one (b + 3 * j) d e)
    rw [show b + 3 * j + 3 = b + 3 * (j + 1) from by ring]
    finish

theorem r5r2_tail2 : ∀ b e,
    (⟨0, b, 0, 2, e + 1⟩ : Q) [fm]⊢* ⟨1, b + 2, 0, 0, e⟩ := by
  intro b e
  step fm; step fm; ring_nf; finish

theorem r5_tail1 : ∀ b e,
    (⟨0, b, 0, 1, e + 1⟩ : Q) [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  intro b e
  step fm; ring_nf; finish

theorem r3_r1r1 : ∀ b e,
    (⟨1, b + 2, 0, 0, e⟩ : Q) [fm]⊢* ⟨2, b, 0, 0, e + 1⟩ := by
  intro b e
  step fm; step fm; step fm; ring_nf; finish

theorem r3r1r1_one : ∀ a b e,
    (⟨a + 1, b + 2, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 2, b, 0, 0, e + 1⟩ := by
  intro a b e
  step fm; step fm; step fm; ring_nf; finish

theorem r3r1r1_iter : ∀ j a b e,
    (⟨a + 1, b + 2 * j, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 1 + j, b, 0, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intro a b e; simp; exists 0
  | succ j ih =>
    intro a b e
    rw [show b + 2 * (j + 1) = (b + 2) + 2 * j from by ring]
    apply stepStar_trans (ih a (b + 2) e)
    -- Goal: (a+1+j, b+2, 0, 0, e+j) ⊢* (a+1+(j+1), b, 0, 0, e+(j+1))
    -- Use r3r1r1_one with a' = a+j, i.e. a'+1 = a+j+1 = a+1+j
    rw [show a + 1 + j = (a + j) + 1 from by ring,
        show a + 1 + (j + 1) = (a + j) + 2 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    exact r3r1r1_one (a + j) b (e + j)

-- Main transition using pair (k, e) to avoid quadratic arithmetic
-- C(k, e) = (3k+1, 0, 0, 0, e)
-- Proves C(k, e) ⊢⁺ C(k+1, e + 8k + 3) = (3k+4, 0, 0, 0, e + 8k + 3)
theorem main_trans (k e : ℕ) :
    (⟨3 * k + 1, 0, 0, 0, e⟩ : Q) [fm]⊢⁺
    ⟨3 * k + 4, 0, 0, 0, e + 8 * k + 3⟩ := by
  -- Phase 1: first R3 step + remaining R3 chain
  apply step_stepStar_stepPlus
  · show fm ⟨3 * k + 1, 0, 0, 0, e⟩ = some ⟨3 * k, 0, 2, 0, e + 1⟩; rfl
  apply stepStar_trans
  · have h := r3_chain (3 * k) 2 (e + 1)
    rw [show 2 + 2 * (3 * k) = 6 * k + 2 from by ring,
        show e + 1 + 3 * k = e + 3 * k + 1 from by ring] at h
    exact h
  -- Phase 2: R4 chain
  apply stepStar_trans
  · have h := r4_chain (6 * k + 2) 0 (e + 3 * k + 1)
    rw [show 0 + (6 * k + 2) = 6 * k + 2 from by ring] at h
    exact h
  -- Phase 3: R5R2R2 loop (2k iterations)
  -- d = 6k+2 = 2 + 3*(2k), e' = e+3k+1 = (e+k+1) + 2k
  apply stepStar_trans
  · have h := r5r2r2_iter (2 * k) 0 2 (e + k + 1)
    rw [show 2 + 3 * (2 * k) = 6 * k + 2 from by ring,
        show e + k + 1 + 2 * k = e + 3 * k + 1 from by ring,
        show 0 + 3 * (2 * k) = 6 * k from by ring] at h
    exact h
  -- Phase 4: R5R2 tail (d=2): (0, 6k, 0, 2, e+k+1) -> (1, 6k+2, 0, 0, e+k)
  apply stepStar_trans
  · have h := r5r2_tail2 (6 * k) (e + k)
    convert h using 2
  -- Phase 5: R3 + R1R1: (1, 6k+2, 0, 0, e+k) -> (2, 6k, 0, 0, e+k+1)
  apply stepStar_trans (r3_r1r1 (6 * k) (e + k))
  -- Phase 6: R3R1R1 loop (3k times)
  -- (2, 6k, 0, 0, e+k+1) -> (3k+2, 0, 0, 0, e+4k+1)
  apply stepStar_trans
  · have h := r3r1r1_iter (3 * k) 1 0 (e + k + 1)
    rw [show 0 + 2 * (3 * k) = 6 * k from by ring,
        show 1 + 1 + 3 * k = 3 * k + 2 from by ring,
        show e + k + 1 + 3 * k = e + 4 * k + 1 from by ring] at h
    exact h
  -- Phase 7: R3 chain (3k+2 steps)
  -- (3k+2, 0, 0, 0, e+4k+1) -> (0, 0, 6k+4, 0, e+7k+3)
  apply stepStar_trans
  · have h := r3_chain (3 * k + 2) 0 (e + 4 * k + 1)
    rw [show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring,
        show e + 4 * k + 1 + (3 * k + 2) = e + 7 * k + 3 from by ring] at h
    exact h
  -- Phase 8: R4 chain
  apply stepStar_trans
  · have h := r4_chain (6 * k + 4) 0 (e + 7 * k + 3)
    rw [show 0 + (6 * k + 4) = 6 * k + 4 from by ring] at h
    exact h
  -- Phase 9: R5R2R2 loop (2k+1 iterations)
  -- d = 6k+4 = 1 + 3*(2k+1), e' = e+7k+3 = (e+5k+2) + (2k+1)
  apply stepStar_trans
  · have h := r5r2r2_iter (2 * k + 1) 0 1 (e + 5 * k + 2)
    rw [show 1 + 3 * (2 * k + 1) = 6 * k + 4 from by ring,
        show e + 5 * k + 2 + (2 * k + 1) = e + 7 * k + 3 from by ring,
        show 0 + 3 * (2 * k + 1) = 6 * k + 3 from by ring] at h
    exact h
  -- Phase 10: R5 tail (d=1): (0, 6k+3, 0, 1, e+5k+2) -> (2, 6k+4, 0, 0, e+5k+1)
  apply stepStar_trans
  · have h := r5_tail1 (6 * k + 3) (e + 5 * k + 1)
    rw [show e + 5 * k + 1 + 1 = e + 5 * k + 2 from by ring,
        show 6 * k + 3 + 1 = 6 * k + 4 from by ring] at h
    exact h
  -- Phase 11: R3R1R1 loop (3k+2 times)
  -- (2, 6k+4, 0, 0, e+5k+1) -> (3k+4, 0, 0, 0, e+8k+3)
  have h := r3r1r1_iter (3 * k + 2) 1 0 (e + 5 * k + 1)
  rw [show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring,
      show 1 + 1 + (3 * k + 2) = 3 * k + 4 from by ring,
      show e + 5 * k + 1 + (3 * k + 2) = e + 8 * k + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  change ¬halts fm ⟨1, 0, 0, 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, e⟩ ↦ ⟨3 * k + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨k, e⟩
  exact ⟨⟨k + 1, e + 8 * k + 3⟩, main_trans k e⟩

end Sz22_2003_unofficial_362

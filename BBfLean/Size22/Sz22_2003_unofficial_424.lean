import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #424: [27/10, 55/21, 22/3, 7/11, 15/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  1
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_424

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer e to d
theorem e_to_d : ∀ j a d,
    ⟨a, 0, 0, d, j⟩ [fm]⊢* (⟨a, 0, 0, d + j, 0⟩ : Q) := by
  intro j; induction j with
  | zero => intro a d; exists 0
  | succ j ih =>
    intro a d
    step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R1 step: (a+1, b, c+1, d, e) -> (a, b+3, c, d, e)
theorem r1_step (a b c d e : ℕ) :
    ⟨a + 1, b, c + 1, d, e⟩ [fm]⊢ (⟨a, b + 3, c, d, e⟩ : Q) := rfl

-- R2 step when a=0: (0, b+1, c, d+1, e) -> (0, b, c+1, d, e+1)
theorem r2_step (b c d e : ℕ) :
    ⟨0, b + 1, c, d + 1, e⟩ [fm]⊢ (⟨0, b, c + 1, d, e + 1⟩ : Q) := rfl

-- R2 step when c=0: (a, b+1, 0, d+1, e) -> (a, b, 1, d, e+1)
theorem r2_step_c0 (a b d e : ℕ) :
    ⟨a, b + 1, 0, d + 1, e⟩ [fm]⊢ (⟨a, b, 1, d, e + 1⟩ : Q) := by
  show fm ⟨a, b + 1, 0, d + 1, e⟩ = some ⟨a, b, 1, d, e + 1⟩
  cases a <;> rfl

-- R5 step: (a+1, 0, 0, d, 0) -> (a, 1, 1, d, 0)
theorem r5_step (a d : ℕ) :
    ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢ (⟨a, 1, 1, d, 0⟩ : Q) := by
  show fm ⟨a + 1, 0, 0, d, 0⟩ = some ⟨a, 1, 1, d, 0⟩
  cases d <;> rfl

-- R1,R2 one pair: (a+1, b, 1, d+1, e) -> (a, b+3, 0, d+1, e) -> (a, b+2, 1, d, e+1)
theorem r1_r2_one (a b d e : ℕ) :
    ⟨a + 1, b, 1, d + 1, e⟩ [fm]⊢* (⟨a, b + 2, 1, d, e + 1⟩ : Q) := by
  apply stepStar_trans (c₂ := ⟨a, b + 3, 0, d + 1, e⟩)
  · exact step_stepStar (r1_step a b 0 (d + 1) e)
  · apply step_stepStar
    have h := r2_step_c0 a (b + 2) d e
    simp only [(by ring : b + 2 + 1 = b + 3)] at h
    exact h

-- R1,R2 loop j iterations
theorem r1_r2_loop : ∀ j a b d e,
    ⟨a + j, b, 1, d + j, e⟩ [fm]⊢* (⟨a, b + 2 * j, 1, d, e + j⟩ : Q) := by
  intro j; induction j with
  | zero => intro a b d e; ring_nf; exists 0
  | succ j ih =>
    intro a b d e
    rw [show a + (j + 1) = (a + j) + 1 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    apply stepStar_trans (r1_r2_one (a + j) b (d + j) e)
    apply stepStar_trans (ih a (b + 2) d (e + 1))
    ring_nf; finish

-- R2 chain: (0, b+j, c, d+j, e) ->* (0, b, c+j, d, e+j)
theorem r2_chain : ∀ j b c d e,
    ⟨0, b + j, c, d + j, e⟩ [fm]⊢* (⟨0, b, c + j, d, e + j⟩ : Q) := by
  intro j; induction j with
  | zero => intro b c d e; ring_nf; exists 0
  | succ j ih =>
    intro b c d e
    rw [show b + (j + 1) = (b + j) + 1 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    apply stepStar_trans (c₂ := ⟨0, b + j, c + 1, d + j, e + 1⟩)
    · exact step_stepStar (r2_step (b + j) c (d + j) e)
    · apply stepStar_trans (ih b (c + 1) d (e + 1))
      ring_nf; finish

-- R3,R1 one step: (0, b+1, c+1, 0, e) -> (0, b+3, c, 0, e+1)
theorem r3_r1_one (b c e : ℕ) :
    ⟨0, b + 1, c + 1, 0, e⟩ [fm]⊢* (⟨0, b + 3, c, 0, e + 1⟩ : Q) := by
  step fm; step fm
  ring_nf; finish

-- R3,R1 loop j times: (0, b+j, j, 0, e) ->* (0, b+3*j, 0, 0, e+j)
theorem r3_r1_loop : ∀ j b e,
    ⟨0, b + j, j, 0, e⟩ [fm]⊢* (⟨0, b + 3 * j, 0, 0, e + j⟩ : Q) := by
  intro j; induction j with
  | zero => intro b e; ring_nf; exists 0
  | succ j ih =>
    intro b e
    rw [show b + (j + 1) = (b + j) + 1 from by ring]
    apply stepStar_trans (r3_r1_one (b + j) j e)
    rw [show b + j + 3 = (b + 3) + j from by ring]
    apply stepStar_trans (ih (b + 3) (e + 1))
    ring_nf; finish

-- R3 chain: (a, j, 0, 0, e) ->* (a+j, 0, 0, 0, e+j)
theorem r3_chain : ∀ j a e,
    ⟨a, j, 0, 0, e⟩ [fm]⊢* (⟨a + j, 0, 0, 0, e + j⟩ : Q) := by
  intro j; induction j with
  | zero => intro a e; ring_nf; exists 0
  | succ j ih =>
    intro a e
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, 2n) ⊢⁺ (3n+3, 0, 0, 0, 6n+4)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ (⟨3 * n + 3, 0, 0, 0, 6 * n + 4⟩ : Q) := by
  -- Phase A: e_to_d
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_d (2 * n) (n + 1) 0
    simp only [(by ring : 0 + 2 * n = 2 * n)] at h
    exact h
  -- Phase B: R5
  apply step_stepStar_stepPlus
  · exact r5_step n (2 * n)
  -- Phase C: R1,R2 loop n times
  apply stepStar_trans
  · have h := r1_r2_loop n 0 1 n 0
    simp only [(by ring : 0 + n = n),
               (by ring : n + n = 2 * n),
               (by ring : 1 + 2 * n = 2 * n + 1)] at h
    exact h
  -- Phase D: R2 chain n times
  apply stepStar_trans
  · have h := r2_chain n (n + 1) 1 0 n
    simp only [(by ring : (n + 1) + n = 2 * n + 1),
               (by ring : 0 + n = n),
               (by ring : 1 + n = n + 1),
               (by ring : n + n = 2 * n)] at h
    exact h
  -- Phase E: R3,R1 loop (n+1) times
  apply stepStar_trans
  · have h := r3_r1_loop (n + 1) 0 (2 * n)
    simp only [(by ring : 0 + (n + 1) = n + 1),
               (by ring : 0 + 3 * (n + 1) = 3 * n + 3),
               (by ring : 2 * n + (n + 1) = 3 * n + 1)] at h
    exact h
  -- Phase F: R3 chain
  have h := r3_chain (3 * n + 3) 0 (3 * n + 1)
  simp only [(by ring : 0 + (3 * n + 3) = 3 * n + 3),
             (by ring : 3 * n + 1 + (3 * n + 3) = 6 * n + 4)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 0
  intro n
  exact ⟨3 * n + 2, by rw [show 3 * n + 2 + 1 = 3 * n + 3 from by ring,
    show 2 * (3 * n + 2) = 6 * n + 4 from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_424

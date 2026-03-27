import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #365: [2/15, 3/98, 15125/2, 7/5, 2/11]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -2  0
-1  0  3  0  2
 0  0 -1  1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_365

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Rule 3 chain: (j, 0, c, d, e) ⊢* (0, 0, c+3j, d, e+2j) when d ≤ 1
-- With d=0:
theorem r3_chain_d0 : ∀ j c e,
    (⟨j, 0, c, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, c + 3 * j, 0, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro c e; simp; exists 0
  | succ j ih =>
    intro c e
    apply stepStar_trans
    · show ⟨j + 1, 0, c, 0, e⟩ [fm]⊢* ⟨j, 0, c + 3, 0, e + 2⟩
      step fm; ring_nf; finish
    apply stepStar_trans (ih (c + 3) (e + 2))
    rw [show c + 3 + 3 * j = c + 3 * (j + 1) from by ring,
        show e + 2 + 2 * j = e + 2 * (j + 1) from by ring]
    finish

-- Rule 3 chain with d=1:
theorem r3_chain_d1 : ∀ j c e,
    (⟨j, 0, c, 1, e⟩ : Q) [fm]⊢* ⟨0, 0, c + 3 * j, 1, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro c e; simp; exists 0
  | succ j ih =>
    intro c e
    apply stepStar_trans
    · show ⟨j + 1, 0, c, 1, e⟩ [fm]⊢* ⟨j, 0, c + 3, 1, e + 2⟩
      step fm; ring_nf; finish
    apply stepStar_trans (ih (c + 3) (e + 2))
    rw [show c + 3 + 3 * j = c + 3 * (j + 1) from by ring,
        show e + 2 + 2 * j = e + 2 * (j + 1) from by ring]
    finish

-- Rule 4 chain: (0, 0, j, d, e) ⊢* (0, 0, 0, d+j, e)
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

-- Rule 5 + Rule 2 pair: (0, b, 0, d+2, e+1) ⊢* (0, b+1, 0, d, e)
theorem r5r2_pair : ∀ b d e,
    (⟨0, b, 0, d + 2, e + 1⟩ : Q) [fm]⊢* ⟨0, b + 1, 0, d, e⟩ := by
  intro b d e
  step fm; step fm; ring_nf; finish

-- Iterate R5+R2 pairs: (0, 0, 0, 2j+r, e+j) ⊢* (0, j, 0, r, e) for r ∈ {0,1}
theorem r5r2_iter_r1 : ∀ j b e,
    (⟨0, b, 0, 2 * j + 1, e + j⟩ : Q) [fm]⊢* ⟨0, b + j, 0, 1, e⟩ := by
  intro j; induction j with
  | zero => intro b e; simp; exists 0
  | succ j ih =>
    intro b e
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring,
        show e + (j + 1) = e + j + 1 from by ring]
    apply stepStar_trans (r5r2_pair b (2 * j + 1) (e + j))
    apply stepStar_trans (ih (b + 1) e)
    rw [show b + 1 + j = b + (j + 1) from by ring]
    finish

theorem r5r2_iter_r0 : ∀ j b e,
    (⟨0, b, 0, 2 * j, e + j⟩ : Q) [fm]⊢* ⟨0, b + j, 0, 0, e⟩ := by
  intro j; induction j with
  | zero => intro b e; simp; exists 0
  | succ j ih =>
    intro b e
    rw [show 2 * (j + 1) = 2 * j + 2 from by ring,
        show e + (j + 1) = e + j + 1 from by ring]
    apply stepStar_trans (r5r2_pair b (2 * j) (e + j))
    apply stepStar_trans (ih (b + 1) e)
    rw [show b + 1 + j = b + (j + 1) from by ring]
    finish

-- Mini-cycle: R3 + 3×R1 with d ≤ 1
-- (a+1, b+3, 0, 0, e) ⊢* (a+3, b, 0, 0, e+2)
theorem r3r1_cycle_d0 : ∀ a b e,
    (⟨a + 1, b + 3, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 3, b, 0, 0, e + 2⟩ := by
  intro a b e
  step fm; step fm; step fm; step fm; ring_nf; finish

-- (a+1, b+3, 0, 1, e) ⊢* (a+3, b, 0, 1, e+2)
theorem r3r1_cycle_d1 : ∀ a b e,
    (⟨a + 1, b + 3, 0, 1, e⟩ : Q) [fm]⊢* ⟨a + 3, b, 0, 1, e + 2⟩ := by
  intro a b e
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Iterate mini-cycles with d=0
theorem r3r1_iter_d0 : ∀ j a b e,
    (⟨a + 1, b + 3 * j, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 1 + 2 * j, b, 0, 0, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro a b e; simp; exists 0
  | succ j ih =>
    intro a b e
    rw [show b + 3 * (j + 1) = (b + 3) + 3 * j from by ring]
    apply stepStar_trans (ih a (b + 3) e)
    rw [show a + 1 + 2 * j = (a + 2 * j) + 1 from by ring,
        show a + 1 + 2 * (j + 1) = (a + 2 * j) + 3 from by ring,
        show e + 2 * (j + 1) = (e + 2 * j) + 2 from by ring]
    exact r3r1_cycle_d0 (a + 2 * j) b (e + 2 * j)

-- Iterate mini-cycles with d=1
theorem r3r1_iter_d1 : ∀ j a b e,
    (⟨a + 1, b + 3 * j, 0, 1, e⟩ : Q) [fm]⊢* ⟨a + 1 + 2 * j, b, 0, 1, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro a b e; simp; exists 0
  | succ j ih =>
    intro a b e
    rw [show b + 3 * (j + 1) = (b + 3) + 3 * j from by ring]
    apply stepStar_trans (ih a (b + 3) e)
    rw [show a + 1 + 2 * j = (a + 2 * j) + 1 from by ring,
        show a + 1 + 2 * (j + 1) = (a + 2 * j) + 3 from by ring,
        show e + 2 * (j + 1) = (e + 2 * j) + 2 from by ring]
    exact r3r1_cycle_d1 (a + 2 * j) b (e + 2 * j)

-- Tail with b=1, d=1: (a+1, 1, 0, 1, e) -> R3,R1,R3 -> (a, 0, 5, 1, e+4) -> r3_chain_d1
-- (a+1, 1, 0, 1, e) ⊢* (0, 0, 3*a+5, 1, e+2*a+4)
theorem r3r1_tail_d1 : ∀ a e,
    (⟨a + 1, 1, 0, 1, e⟩ : Q) [fm]⊢* ⟨0, 0, 3 * a + 5, 1, e + 2 * a + 4⟩ := by
  intro a e
  -- R3: (a, 1, 3, 1, e+2), R1: (a+1, 0, 2, 1, e+2), R3: (a, 0, 5, 1, e+4)
  apply stepStar_trans
  · show ⟨a + 1, 1, 0, 1, e⟩ [fm]⊢* ⟨a, 0, 5, 1, e + 4⟩
    step fm; step fm; step fm; ring_nf; finish
  -- r3_chain_d1(a): (a, 0, 5, 1, e+4) -> (0, 0, 5+3a, 1, e+4+2a)
  have h := r3_chain_d1 a 5 (e + 4)
  rw [show 5 + 3 * a = 3 * a + 5 from by ring,
      show e + 4 + 2 * a = e + 2 * a + 4 from by ring] at h
  exact h

-- Main transition: (2k+1, 0, 0, 0, e) ⊢⁺ (2k+3, 0, 0, 0, e + 6k + 2)
theorem main_trans (k e : ℕ) :
    (⟨2 * k + 1, 0, 0, 0, e⟩ : Q) [fm]⊢⁺
    ⟨2 * k + 3, 0, 0, 0, e + 6 * k + 2⟩ := by
  -- Phase 1: first R3 step
  apply step_stepStar_stepPlus
  · show fm ⟨2 * k + 1, 0, 0, 0, e⟩ = some ⟨2 * k, 0, 3, 0, e + 2⟩; rfl
  -- Remaining R3 chain: (2k, 0, 3, 0, e+2) -> (0, 0, 3+6k, 0, e+2+4k)
  apply stepStar_trans
  · have h := r3_chain_d0 (2 * k) 3 (e + 2)
    rw [show 3 + 3 * (2 * k) = 6 * k + 3 from by ring,
        show e + 2 + 2 * (2 * k) = e + 4 * k + 2 from by ring] at h
    exact h
  -- Phase 2: R4 chain (6k+3): (0, 0, 6k+3, 0, e+4k+2) -> (0, 0, 0, 6k+3, e+4k+2)
  apply stepStar_trans
  · have h := r4_chain (6 * k + 3) 0 (e + 4 * k + 2)
    rw [show 0 + (6 * k + 3) = 6 * k + 3 from by ring] at h
    exact h
  -- Phase 3: R5+R2 loop (3k+1 pairs): d=6k+3=2(3k+1)+1, e'=e+4k+2=(e+k+1)+(3k+1)
  -- (0, 0, 0, 6k+3, e+4k+2) -> (0, 3k+1, 0, 1, e+k+1)
  apply stepStar_trans
  · have h := r5r2_iter_r1 (3 * k + 1) 0 (e + k + 1)
    rw [show 2 * (3 * k + 1) + 1 = 6 * k + 3 from by ring,
        show e + k + 1 + (3 * k + 1) = e + 4 * k + 2 from by ring,
        show 0 + (3 * k + 1) = 3 * k + 1 from by ring] at h
    exact h
  -- Phase 4: R5: (0, 3k+1, 0, 1, e+k+1) -> (1, 3k+1, 0, 1, e+k)
  apply stepStar_trans
  · show ⟨0, 3 * k + 1, 0, 1, e + k + 1⟩ [fm]⊢* ⟨1, 3 * k + 1, 0, 1, e + k⟩
    step fm; ring_nf; finish
  -- Phase 5: r3r1_iter_d1(k): (1, 3k+1, 0, 1, e+k) -> (2k+1, 1, 0, 1, e+3k)
  apply stepStar_trans
  · have h := r3r1_iter_d1 k 0 1 (e + k)
    rw [show 0 + 1 = 1 from by ring,
        show 1 + 3 * k = 3 * k + 1 from by ring,
        show 0 + 1 + 2 * k = 2 * k + 1 from by ring,
        show e + k + 2 * k = e + 3 * k from by ring] at h
    exact h
  -- Phase 6: r3r1_tail_d1(2k): (2k+1, 1, 0, 1, e+3k) -> (0, 0, 6k+5, 1, e+7k+4)
  apply stepStar_trans
  · have h := r3r1_tail_d1 (2 * k) (e + 3 * k)
    rw [show 2 * k + 1 = 2 * k + 1 from by ring,
        show 3 * (2 * k) + 5 = 6 * k + 5 from by ring,
        show e + 3 * k + 2 * (2 * k) + 4 = e + 7 * k + 4 from by ring] at h
    exact h
  -- Phase 7: R4 chain (6k+5): (0, 0, 6k+5, 1, e+7k+4) -> (0, 0, 0, 6k+6, e+7k+4)
  apply stepStar_trans
  · have h := r4_chain (6 * k + 5) 1 (e + 7 * k + 4)
    rw [show 1 + (6 * k + 5) = 6 * k + 6 from by ring] at h
    exact h
  -- Phase 8: R5+R2 loop (3k+3 pairs): d=6k+6=2(3k+3), e'=e+7k+4=(e+4k+1)+(3k+3)
  -- (0, 0, 0, 6k+6, e+7k+4) -> (0, 3k+3, 0, 0, e+4k+1)
  apply stepStar_trans
  · have h := r5r2_iter_r0 (3 * k + 3) 0 (e + 4 * k + 1)
    rw [show 2 * (3 * k + 3) = 6 * k + 6 from by ring,
        show e + 4 * k + 1 + (3 * k + 3) = e + 7 * k + 4 from by ring,
        show 0 + (3 * k + 3) = 3 * k + 3 from by ring] at h
    exact h
  -- Phase 9: R5: (0, 3k+3, 0, 0, e+4k+1) -> (1, 3k+3, 0, 0, e+4k)
  apply stepStar_trans
  · show ⟨0, 3 * k + 3, 0, 0, e + 4 * k + 1⟩ [fm]⊢* ⟨1, 3 * k + 3, 0, 0, e + 4 * k⟩
    step fm; ring_nf; finish
  -- Phase 10: r3r1_iter_d0(k+1): (1, 3(k+1), 0, 0, e+4k) -> (2k+3, 0, 0, 0, e+6k+2)
  have h := r3r1_iter_d0 (k + 1) 0 0 (e + 4 * k)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
      show 0 + 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
      show e + 4 * k + 2 * (k + 1) = e + 6 * k + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  change ¬halts fm ⟨1, 0, 0, 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, e⟩ ↦ ⟨2 * k + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨k, e⟩
  exact ⟨⟨k + 1, e + 6 * k + 2⟩, main_trans k e⟩

end Sz22_2003_unofficial_365

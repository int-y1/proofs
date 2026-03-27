import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #207: [1/6, 4/35, 55/2, 1323/11, 5/3]

Vector representation:
```
-1 -1  0  0  0
 2  0 -1 -1  0
-1  0  1  0  1
 0  3  0  2 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_207

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+3, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 step helper (step fm can't handle symbolic c with d=0, e=symbolic)
private theorem r3_step (c e : ℕ) : fm ⟨1, 0, c, 0, e⟩ = some ⟨0, 0, c + 1, 0, e + 1⟩ := by
  simp [fm]

-- R4 repeated: drain e (when a=0, c=0)
theorem r4_drain : ∀ k B D e, ⟨0, B, 0, D, e + k⟩ [fm]⊢* ⟨0, B + 3 * k, 0, D + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro B D e; simp; exists 0
  | succ k ih =>
    intro B D e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- One round of (R5,R2,R1,R1): (0, B+3, 0, D+1, 0) ⊢^4 (0, B, 0, D, 0)
private theorem bd_one (B D : ℕ) : ⟨0, B + 3, 0, D + 1, 0⟩ [fm]⊢* ⟨0, B, 0, D, 0⟩ := by
  rw [show B + 3 = (B + 2) + 1 from by ring]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- (R5,R2,R1,R1) cycle repeated
theorem bd_drain : ∀ k B D, ⟨0, B + 3 * k, 0, D + k, 0⟩ [fm]⊢* ⟨0, B, 0, D, 0⟩ := by
  intro k; induction k with
  | zero => intro B D; simp; exists 0
  | succ k ih =>
    intro B D
    rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    apply stepStar_trans (ih (B + 3) (D + 1))
    exact bd_one B D

-- Zigzag: R2+R3 repeated
theorem zigzag : ∀ j k D, ⟨k, 0, 1, D + j, k⟩ [fm]⊢* ⟨k + j, 0, 1, D, k + j⟩ := by
  intro j; induction j with
  | zero => intro k D; simp; exists 0
  | succ j ih =>
    intro k D
    rw [show D + (j + 1) = (D + j) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (k + 1) D)
    ring_nf; finish

-- R3 repeated: drain a into c and e (when b=0, d=0)
theorem a_to_ce : ∀ j a c e, ⟨a + j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + j, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intro a c e; simp; exists 0
  | succ j ih =>
    intro a c e
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

-- 7-step countdown cycle: from (c+1)+k down to c+1
theorem countdown : ∀ k c E, ⟨0, 0, (c + 1) + k, 0, E + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 0, E + 1⟩ := by
  intro k; induction k with
  | zero => intro c E; simp; exists 0
  | succ k ih =>
    intro c E
    rw [show (c + 1) + (k + 1) = ((c + k) + 1) + 1 from by ring]
    step fm  -- R4
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    step fm  -- R2
    step fm  -- R1: now at (1, 0, c+k, 0, E)
    -- R3: use simp [fm] since step fm can't handle symbolic c+k
    apply stepStar_trans (c₂ := ⟨0, 0, c + k + 1, 0, E + 1⟩)
    · exact step_stepStar (r3_step (c + k) E)
    rw [show c + k + 1 = (c + 1) + k from by ring]
    exact ih c E

-- Main transition: C(n) = (0, 0, 1, 0, n+2) ⊢⁺ C(2n+2) = (0, 0, 1, 0, 2n+4)
theorem main_trans (n : ℕ) : ⟨0, 0, 1, 0, n + 2⟩ [fm]⊢⁺ ⟨0, 0, 1, 0, 2 * n + 4⟩ := by
  -- Phase 1: 4 steps to (0, 1, 0, 1, n+1)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm  -- R4: (0, 3, 1, 2, n+1)
  step fm  -- R2: (2, 3, 0, 1, n+1)
  step fm  -- R1: (1, 2, 0, 1, n+1)
  step fm  -- R1: (0, 1, 0, 1, n+1)
  -- Phase 2: R4 drain (n+1) times
  apply stepStar_trans (c₂ := ⟨0, 3 * n + 4, 0, 2 * n + 3, 0⟩)
  · have h := r4_drain (n + 1) 1 1 0
    rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring,
        show 1 + 3 * (n + 1) = 3 * n + 4 from by ring,
        show 1 + 2 * (n + 1) = 2 * n + 3 from by ring] at h
    exact h
  -- Phase 3: bd_drain (n+1) rounds
  apply stepStar_trans (c₂ := ⟨0, 1, 0, n + 2, 0⟩)
  · have h := bd_drain (n + 1) 1 (n + 2)
    rw [show 1 + 3 * (n + 1) = 3 * n + 4 from by ring,
        show (n + 2) + (n + 1) = 2 * n + 3 from by ring] at h
    exact h
  -- Phase 4: R5
  step fm
  -- Phase 5: Zigzag: (0, 0, 1, n+2, 0) ⊢* (n+2, 0, 1, 0, n+2)
  apply stepStar_trans (c₂ := ⟨n + 2, 0, 1, 0, n + 2⟩)
  · have h := zigzag (n + 2) 0 0
    rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring] at h
    exact h
  -- Phase 6: a_to_ce: (n+2, 0, 1, 0, n+2) ⊢* (0, 0, n+3, 0, 2n+4)
  apply stepStar_trans (c₂ := ⟨0, 0, n + 3, 0, 2 * n + 4⟩)
  · have h := a_to_ce (n + 2) 0 1 (n + 2)
    rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
        show 1 + (n + 2) = n + 3 from by ring,
        show (n + 2) + (n + 2) = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 7: Countdown: (0, 0, n+3, 0, 2n+4) ⊢* (0, 0, 1, 0, 2n+4)
  have h := countdown (n + 2) 0 (2 * n + 3)
  rw [show (0 : ℕ) + 1 + (n + 2) = n + 3 from by ring,
      show 2 * n + 3 + 1 = 2 * n + 4 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 1, 0, n + 2⟩) 0
  intro n
  exact ⟨2 * n + 2, main_trans n⟩

end Sz22_2003_unofficial_207

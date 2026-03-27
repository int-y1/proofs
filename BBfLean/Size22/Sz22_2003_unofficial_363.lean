import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #363: [2/15, 3/154, 175/2, 121/5, 6/11]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -1 -1
-1  0  2  1  0
 0  0 -1  0  2
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_363

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: c → e (when a=0, b=0)
theorem c_to_e : ∀ k d e, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), 0, d, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3 repeated: a → c,d (when b=0, e=0)
theorem a_to_cd : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + 2 * k, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R2 repeated: a,d,e → b (when c=0)
-- (a+k, b, 0, d+k, e+k) ⊢* (a, b+k, 0, d, e)
theorem r2_chain : ∀ k a b d e, ⟨a + k, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a, b + k, (0 : ℕ), d, e⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Alternating R5,R2 phase: (0, 0, 0, d, e) with d steps
-- Each pair: R5 gives (1,1,0,d,e-1), then R2 gives (0,2,0,d-1,e-2)
-- After k pairs: (0, 2k, 0, d-k, e-2k)
theorem r5r2_pairs : ∀ k b d e, ⟨0, b, 0, d + k, e + 2 * k⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, (0 : ℕ), d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = e + 2 * k + 1 + 1 from by ring]
    -- R5: (0, b, 0, (d+k)+1, e+2k+1+1) -> (1, b+1, 0, (d+k)+1, e+2k+1)
    step fm
    -- R2: (1, b+1, 0, (d+k)+1, e+2k+1) -> (0, b+2, 0, d+k, e+2k)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (d + k) + 1 = d + k + 1 from by ring,
        show e + 2 * k + 1 = e + 2 * k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R1 repeated: b,c → a
-- (a, b+k, c+k, d, e) ⊢* (a+k, b, c, d, e)
theorem r1_chain : ∀ k a b c d e, ⟨a, b + k, c + k, d, e⟩ [fm]⊢* ⟨a + k, b, c, d, e⟩ := by
  intro k; induction k with
  | zero => intro a b c d e; exists 0
  | succ k ih =>
    intro a b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _ _)
    ring_nf; finish

-- (R1, R1, R3) single step: (a, b+2, 2, d, 0) ⊢* (a+1, b, 2, d+1, 0)
theorem r1r1r3_step (a b d : ℕ) : ⟨a, b + 2, 2, d, 0⟩ [fm]⊢* ⟨a + 1, b, (2 : ℕ), d + 1, (0 : ℕ)⟩ := by
  rw [show b + 2 = (b + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

theorem r1r1r3_loop : ∀ k a b d, ⟨a, b + 2 * k, 2, d, 0⟩ [fm]⊢* ⟨a + k, b, (2 : ℕ), d + k, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    apply stepStar_trans (r1r1r3_step _ _ _)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main cycle: (0, 0, 2*(n+1), 2*n+1, 0) ⊢⁺ (0, 0, 4*(n+1), 4*n+3, 0)
-- i.e., (0, 0, 2n+2, 2n+1, 0) ⊢⁺ (0, 0, 4n+4, 4n+3, 0)
theorem main_cycle (n : ℕ) :
    ⟨0, 0, 2 * (n + 1), 2 * n + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * (n + 1), 4 * n + 3, 0⟩ := by
  -- Phase 1: R4 * (2n+2): (0,0,2n+2,2n+1,0) -> (0,0,0,2n+1,4n+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2 * n + 1, 4 * (n + 1)⟩)
  · have h := c_to_e (2 * (n + 1)) (2 * n + 1) 0
    rw [show (0 : ℕ) + 2 * (2 * (n + 1)) = 4 * (n + 1) from by ring] at h
    exact h
  -- Phase 2: (R5,R2) * (2n+1) pairs: (0,0,0,2n+1,4n+4) -> (0,4n+2,0,0,2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 4 * n + 2, 0, 0, 2⟩)
  · have h := r5r2_pairs (2 * n + 1) 0 0 2
    rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring,
        show (2 : ℕ) + 2 * (2 * n + 1) = 4 * n + 4 from by ring,
        show (0 : ℕ) + 2 * (2 * n + 1) = 4 * n + 2 from by ring] at h
    rw [show 4 * (n + 1) = 4 * n + 4 from by ring]
    exact h
  -- Phase 3: R5: (0,4n+2,0,0,2) -> (1,4n+3,0,0,1)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 4 * n + 3, 0, 0, 1⟩)
  · rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]; simp [fm]
  -- Phase 4: R3: (1,4n+3,0,0,1) -> (0,4n+3,2,1,1)
  apply stepStar_trans (c₂ := ⟨0, 4 * n + 3, 2, 1, 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- Phase 5: R1,R1: (0,4n+3,2,1,1) -> (2,4n+1,0,1,1)
  apply stepStar_trans (c₂ := ⟨2, 4 * n + 1, 0, 1, 1⟩)
  · have h := r1_chain 2 0 (4 * n + 1) 0 1 1
    rw [show (4 * n + 1) + 2 = 4 * n + 3 from by ring,
        show (0 : ℕ) + 2 = 2 from by ring] at h
    exact h
  -- R2: (2,4n+1,0,1,1) -> (1,4n+2,0,0,0)
  apply stepStar_trans (c₂ := ⟨1, 4 * n + 2, 0, 0, 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show 4 * n + 1 = (4 * n + 1) from rfl,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 6: R3: (1,4n+2,0,0,0) -> (0,4n+2,2,1,0)
  apply stepStar_trans (c₂ := ⟨0, 4 * n + 2, 2, 1, 0⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- Phase 7: (R1,R1,R3) * (2n) loop: (0,4n+2,2,1,0) -> (2n,2,2,2n+1,0)
  apply stepStar_trans (c₂ := ⟨2 * n, 2, 2, 2 * n + 1, 0⟩)
  · have h := r1r1r3_loop (2 * n) 0 2 1
    rw [show (2 : ℕ) + 2 * (2 * n) = 4 * n + 2 from by ring,
        show (0 : ℕ) + 2 * n = 2 * n from by ring,
        show (1 : ℕ) + 2 * n = 2 * n + 1 from by ring] at h
    exact h
  -- Phase 8: R1,R1: (2n,2,2,2n+1,0) -> (2n+2,0,0,2n+1,0)
  apply stepStar_trans (c₂ := ⟨2 * n + 2, 0, 0, 2 * n + 1, 0⟩)
  · have h := r1_chain 2 (2 * n) 0 0 (2 * n + 1) 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 9: R3 * (2n+2): (2n+2,0,0,2n+1,0) -> (0,0,4n+4,4n+3,0)
  · have h := a_to_cd (2 * n + 2) 0 (2 * n + 1)
    rw [show (0 : ℕ) + 2 * (2 * n + 2) = 4 * n + 4 from by ring,
        show 2 * n + 1 + (2 * n + 2) = 4 * n + 3 from by ring] at h
    rw [show 4 * (n + 1) = 4 * n + 4 from by ring]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * (n + 1), 2 * n + 1, 0⟩) 0
  intro n
  exact ⟨2 * n + 1, by
    show ⟨0, 0, 2 * (n + 1), 2 * n + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * n + 1 + 1), 2 * (2 * n + 1) + 1, 0⟩
    rw [show 2 * (2 * n + 1 + 1) = 4 * (n + 1) from by ring,
        show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
    exact main_cycle n⟩

end Sz22_2003_unofficial_363

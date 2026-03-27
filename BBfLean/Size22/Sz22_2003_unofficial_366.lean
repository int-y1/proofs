import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #366: [2/15, 539/3, 63/2, 5/539, 3/7]

Vector representation:
```
 1 -1 -1  0  0
 0 -1  0  2  1
-1  2  0  1  0
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_366

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 loop: (0,0,c,d+2k,k) ⊢* (0,0,c+k,d,0)
theorem r4_loop : ∀ k c d, (⟨0, 0, c, d + 2 * k, k⟩ : Q) [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; simp; exists 0
  | succ k ih =>
    intro c d
    rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (c + 1) d

-- R5+R1+R3: (0,0,c+1,d+1,0) ⊢* (0,2,c,d+1,0)
theorem r5_r1_r3 (c d : ℕ) : (⟨0, 0, c + 1, d + 1, 0⟩ : Q) [fm]⊢* ⟨0, 2, c, d + 1, 0⟩ := by
  step fm; step fm; step fm; finish

-- Inner loop step: (a,2,c+2,d,0) ⊢* (a+1,2,c,d+1,0)
theorem inner_step (a c d : ℕ) : (⟨a, 2, c + 2, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 2, c, d + 1, 0⟩ := by
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm; step fm
  rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
  step fm; finish

-- Inner loop (even): (a,2,2k,d,0) ⊢* (a+k,2,0,d+k,0)
theorem inner_even : ∀ k a d, (⟨a, 2, 2 * k, d, 0⟩ : Q) [fm]⊢* ⟨a + k, 2, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (inner_step a (2 * k) d)
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (a + 1) (d + 1)

-- Tail for odd: (a,2,1,d,0) ⊢* (a,2,0,d+3,1)
theorem inner_tail (a d : ℕ) : (⟨a, 2, 1, d, 0⟩ : Q) [fm]⊢* ⟨a, 2, 0, d + 3, 1⟩ := by
  step fm; step fm; step fm; finish

-- Inner loop (odd): (a,2,2k+1,d,0) ⊢* (a+k,2,0,d+k+3,1)
theorem inner_odd : ∀ k a d, (⟨a, 2, 2 * k + 1, d, 0⟩ : Q) [fm]⊢* ⟨a + k, 2, 0, d + k + 3, 1⟩ := by
  intro k; induction k with
  | zero =>
    intro a d; simp
    exact inner_tail a d
  | succ k ih =>
    intro a d
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans (inner_step a (2 * k + 1) d)
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + (k + 1) + 3 = (d + 1) + k + 3 from by ring]
    exact ih (a + 1) (d + 1)

-- Drain step: (a+1,2,0,d,e) ⊢* (a,2,0,d+5,e+2)
theorem drain_step (a d e : ℕ) : (⟨a + 1, 2, 0, d, e⟩ : Q) [fm]⊢* ⟨a, 2, 0, d + 5, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- Drain: (a,2,0,d,e) ⊢* (0,2,0,d+5*a,e+2*a)
theorem drain : ∀ a d e, (⟨a, 2, 0, d, e⟩ : Q) [fm]⊢* ⟨0, 2, 0, d + 5 * a, e + 2 * a⟩ := by
  intro a; induction a with
  | zero => intro d e; simp; exists 0
  | succ a ih =>
    intro d e
    apply stepStar_trans (drain_step a d e)
    rw [show d + 5 * (a + 1) = (d + 5) + 5 * a from by ring,
        show e + 2 * (a + 1) = (e + 2) + 2 * a from by ring]
    exact ih (d + 5) (e + 2)

-- Final R2x2: (0,2,0,d,e) ⊢⁺ (0,0,0,d+4,e+2)
theorem final_r2 (d e : ℕ) : (⟨0, 2, 0, d, e⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, d + 4, e + 2⟩ := by
  step fm; step fm; finish

-- Cycle for odd e (e = 2k+1):
theorem cycle_odd (k d : ℕ) (hd : d ≥ 2 * (2 * k + 1) + 1) :
    (⟨0, 0, 0, d, 2 * k + 1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, d + (2 * k + 1) + 1, (2 * k + 1) + 1⟩ := by
  set e := 2 * k + 1
  set r := d - 2 * e
  have hdr : d = r + 2 * e := by omega
  -- Phase 1: R4 loop
  rw [hdr]
  apply stepStar_stepPlus_stepPlus (r4_loop e 0 r)
  rw [show (0 : ℕ) + e = e from by ring]
  -- Phase 2: R5+R1+R3
  rw [show e = (e - 1) + 1 from by omega, show r = (r - 1) + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (r5_r1_r3 (e - 1) (r - 1))
  rw [show (r - 1) + 1 = r from by omega, show e - 1 = 2 * k from by omega]
  -- Phase 3: inner_even
  apply stepStar_stepPlus_stepPlus (inner_even k 0 r)
  rw [show (0 : ℕ) + k = k from by ring]
  -- Phase 4: drain
  apply stepStar_stepPlus_stepPlus (drain k (r + k) 0)
  -- Phase 5: final R2
  have h5 := final_r2 (r + k + 5 * k) (0 + 2 * k)
  rw [show r + k + 5 * k + 4 = r + 2 * e + e + 1 from by omega,
      show 0 + 2 * k + 2 = e + 1 from by omega] at h5
  exact h5

-- Cycle for even e (e = 2k+2):
theorem cycle_even (k d : ℕ) (hd : d ≥ 2 * (2 * k + 2) + 1) :
    (⟨0, 0, 0, d, 2 * k + 2⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, d + (2 * k + 2) + 1, (2 * k + 2) + 1⟩ := by
  set e := 2 * k + 2
  set r := d - 2 * e
  have hdr : d = r + 2 * e := by omega
  -- Phase 1: R4 loop
  rw [hdr]
  apply stepStar_stepPlus_stepPlus (r4_loop e 0 r)
  rw [show (0 : ℕ) + e = e from by ring]
  -- Phase 2: R5+R1+R3
  rw [show e = (e - 1) + 1 from by omega, show r = (r - 1) + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (r5_r1_r3 (e - 1) (r - 1))
  rw [show (r - 1) + 1 = r from by omega, show e - 1 = 2 * k + 1 from by omega]
  -- Phase 3: inner_odd
  apply stepStar_stepPlus_stepPlus (inner_odd k 0 r)
  rw [show (0 : ℕ) + k = k from by ring]
  -- Phase 4: drain
  apply stepStar_stepPlus_stepPlus (drain k (r + k + 3) 1)
  -- Phase 5: final R2
  have h5 := final_r2 (r + k + 3 + 5 * k) (1 + 2 * k)
  rw [show r + k + 3 + 5 * k + 4 = r + 2 * e + e + 1 from by omega,
      show 1 + 2 * k + 2 = e + 1 from by omega] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 2⟩) (by execute fm 3)
  refine progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = (⟨0, 0, 0, d, e⟩ : Q) ∧ e ≥ 2 ∧ d ≥ 2 * e + 1) ?_
    ⟨5, 2, rfl, by omega, by omega⟩
  intro q ⟨d, e, hq, he, hd⟩; subst hq
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- e = m + m (even), m >= 1
    rcases m with _ | k
    · omega
    · -- e = (k+1) + (k+1)
      subst hm
      refine ⟨⟨0, 0, 0, d + ((k + 1) + (k + 1)) + 1, ((k + 1) + (k + 1)) + 1⟩,
        ⟨d + ((k + 1) + (k + 1)) + 1, ((k + 1) + (k + 1)) + 1, rfl, by omega, by omega⟩, ?_⟩
      rw [show (k + 1) + (k + 1) = 2 * k + 2 from by ring]
      exact cycle_even k d (by omega)
  · -- e = m + m + 1 (odd)
    rcases m with _ | k
    · omega
    · -- e = (k+1) + (k+1) + 1
      subst hm
      refine ⟨⟨0, 0, 0, d + ((k + 1) + (k + 1) + 1) + 1, ((k + 1) + (k + 1) + 1) + 1⟩,
        ⟨d + ((k + 1) + (k + 1) + 1) + 1, ((k + 1) + (k + 1) + 1) + 1, rfl, by omega, by omega⟩, ?_⟩
      rw [show (k + 1) + (k + 1) + 1 = 2 * (k + 1) + 1 from by ring]
      exact cycle_odd (k + 1) d (by omega)

end Sz22_2003_unofficial_366

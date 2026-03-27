import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #275: [14/15, 3/77, 125/7, 11/25, 21/2]

Vector representation:
```
 1 -1 -1  1  0
 0  1  0 -1 -1
 0  0  3 -1  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_275

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Rule 3 repeated: d → c
theorem d_to_c (a : ℕ) : ∀ k c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; simp; exists 0
  | succ k ih =>
    intro c; step fm
    apply stepStar_trans (ih (c + 3))
    ring_nf; finish

-- Rule 4 repeated: c → e (odd c)
theorem c_to_e (a : ℕ) : ∀ k e, ⟨a, 0, 2 * k + 1, 0, e⟩ [fm]⊢* ⟨a, 0, 1, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro e; simp; exists 0
  | succ k ih =>
    intro e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

-- R5 then R1
theorem r5_r1 (a e : ℕ) : ⟨a + 1, 0, 1, 0, e⟩ [fm]⊢⁺ ⟨a + 1, 0, 0, 2, e⟩ := by
  step fm; step fm; finish

-- R5,R2 drain pairs
theorem drain_r5_r2 (a : ℕ) : ∀ k b, ⟨a + k, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro b; simp; exists 0
  | succ k ih =>
    intro b
    rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

-- Full drain with R5 at end
theorem drain_r5_r2_r5 (a : ℕ) : ∀ k b, ⟨a + k + 1, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + 2 * k + 1, 0, 1, 0⟩ := by
  intro k; induction k with
  | zero => intro b; step fm; finish
  | succ k ih =>
    intro b
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring, show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

-- Full drain: (n+1, 0, 0, 2, n+2) →* (0, 2n+3, 0, 1, 0)
theorem full_drain (n : ℕ) : ⟨n + 1, 0, 0, 2, n + 2⟩ [fm]⊢* ⟨0, 2 * n + 3, 0, 1, 0⟩ := by
  step fm; step fm
  rw [show n + 1 = 0 + n + 1 from by ring]
  apply stepStar_trans (drain_r5_r2_r5 0 n 2)
  ring_nf; finish

-- Build-up cycle: R3, R1, R1, R1
theorem build_cycle (a b d : ℕ) : ⟨a, b + 3, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 3, b, 0, d + 3, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Build-up cycles iterated
theorem build_cycles :
    ∀ k a d b, ⟨a, b + 3 * k, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 3 * k, b, 0, d + 1 + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d b; simp; exists 0
  | succ k ih =>
    intro a d b
    rw [show b + 3 * (k + 1) = b + 3 * k + 3 from by ring]
    apply stepStar_trans (stepPlus_stepStar (build_cycle _ _ _))
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 2) b)
    ring_nf; finish

-- build_full_mod0: (0, 3k+3, 3, 0, 0) →⁺ (3k+3, 0, 0, 2k+3, 0)
theorem build_full_mod0 (k : ℕ) :
    ⟨0, 3 * k + 3, 3, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 3, 0, 0, 2 * k + 3, 0⟩ := by
  step fm; step fm; step fm
  have h := build_cycles k 3 2 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- build_full_mod1: (0, 3k+4, 3, 0, 0) →⁺ (3k+4, 0, 2, 2k+3, 0)
theorem build_full_mod1 (k : ℕ) :
    ⟨0, 3 * k + 4, 3, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 4, 0, 2, 2 * k + 3, 0⟩ := by
  step fm; step fm; step fm
  -- Goal: (3, 3*k+1, 0, 3, 0) ⊢* (3*k+4, 0, 2, 2*k+3, 0)
  -- build_cycles 3 2 k 1: (3, 1+3*k, 0, 2+1, 0) →* (3+3*k, 1, 0, 2+1+2*k, 0)
  -- But goal has (3, 3*k+1, ...) and h has (3, 1+3*k, ...). Need to rw.
  rw [show 3 * k + 1 = 1 + 3 * k from by ring]
  have h := build_cycles k 3 2 1
  apply stepStar_trans h
  -- Now at (3+3k, 1, 0, 3+2k, 0). Need R3 then R1.
  rw [show 2 + 1 + 2 * k = (2 + 2 * k) + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Main transition: C(m+1) ⊢⁺ C(4(m+1)+1)
-- where C(n) = (3n, 0, 0, 2n+1, 0)
theorem main_trans (m : ℕ) :
    ⟨3 * (m + 1), 0, 0, 2 * (m + 1) + 1, 0⟩ [fm]⊢⁺
    ⟨3 * (4 * (m + 1) + 1), 0, 0, 2 * (4 * (m + 1) + 1) + 1, 0⟩ := by
  rw [show 3 * (m + 1) = 3 * m + 3 from by ring,
      show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
      show 3 * (4 * (m + 1) + 1) = 12 * m + 15 from by ring,
      show 2 * (4 * (m + 1) + 1) + 1 = 8 * m + 11 from by ring]
  -- Phase 1: d_to_c
  apply stepStar_stepPlus_stepPlus
  · have := d_to_c (3 * m + 3) (2 * m + 3) 0
    rw [show 0 + 3 * (2 * m + 3) = 6 * m + 9 from by ring] at this; exact this
  -- Phase 2: c_to_e
  apply stepStar_stepPlus_stepPlus
  · rw [show 6 * m + 9 = 2 * (3 * m + 4) + 1 from by ring]
    have := c_to_e (3 * m + 3) (3 * m + 4) 0
    rw [show 0 + (3 * m + 4) = 3 * m + 4 from by ring] at this; exact this
  -- Phase 3: r5_r1
  apply stepPlus_stepStar_stepPlus
  · rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]; exact r5_r1 _ _
  -- Phase 4: full_drain
  rw [show (3 * m + 2) + 1 = (3 * m + 2) + 1 from rfl,
      show 3 * m + 4 = (3 * m + 2) + 2 from by ring]
  apply stepStar_trans (full_drain (3 * m + 2))
  rw [show 2 * (3 * m + 2) + 3 = 6 * m + 7 from by ring]
  -- Phase 5: R3
  step fm
  -- Phase 6: build_full_mod1
  rw [show 6 * m + 7 = 3 * (2 * m + 1) + 4 from by ring]
  apply stepStar_trans (stepPlus_stepStar (build_full_mod1 (2 * m + 1)))
  rw [show 3 * (2 * m + 1) + 4 = 6 * m + 7 from by ring,
      show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring]
  -- Phase 7: d_to_c
  apply stepStar_trans
  · have := d_to_c (6 * m + 7) (4 * m + 5) 2
    rw [show 2 + 3 * (4 * m + 5) = 12 * m + 17 from by ring] at this; exact this
  -- Phase 8: c_to_e
  rw [show 12 * m + 17 = 2 * (6 * m + 8) + 1 from by ring]
  apply stepStar_trans
  · have := c_to_e (6 * m + 7) (6 * m + 8) 0
    rw [show 0 + (6 * m + 8) = 6 * m + 8 from by ring] at this; exact this
  -- Phase 9: r5_r1
  rw [show 6 * m + 7 = (6 * m + 6) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r5_r1 _ _))
  -- Phase 10: full_drain
  rw [show 6 * m + 8 = (6 * m + 6) + 2 from by ring]
  apply stepStar_trans (full_drain (6 * m + 6))
  rw [show 2 * (6 * m + 6) + 3 = 12 * m + 15 from by ring]
  -- Phase 11: R3
  step fm
  -- Phase 12: build_full_mod0
  rw [show 12 * m + 15 = 3 * (4 * m + 4) + 3 from by ring]
  apply stepStar_trans (stepPlus_stepStar (build_full_mod0 (4 * m + 4)))
  rw [show 3 * (4 * m + 4) + 3 = 12 * m + 15 from by ring,
      show 2 * (4 * m + 4) + 3 = 8 * m + 11 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0⟩)
  · execute fm 15
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * (n + 1), 0, 0, 2 * (n + 1) + 1, 0⟩) 0
  intro n
  exact ⟨4 * (n + 1), main_trans n⟩

end Sz22_2003_unofficial_275

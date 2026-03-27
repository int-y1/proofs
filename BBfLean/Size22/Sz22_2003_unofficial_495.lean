import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #495: [28/15, 3/22, 25/2, 121/7, 14/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_495

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k d, ⟨0, 0, c, d + k, 0⟩ [fm]⊢* ⟨0, 0, c, d, 2 * k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d; rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1)); step fm; ring_nf; finish

theorem r2r1_chain : ∀ n a d e, ⟨a + 1, 0, n, d, n + e⟩ [fm]⊢* ⟨a + n + 1, 0, 0, d + n, e⟩ := by
  intro n; induction n with
  | zero => intro a d e; simp only [Nat.zero_add]; ring_nf; exists 0
  | succ n ih =>
    intro a d e; rw [show (n + 1 : ℕ) + e = (n + e) + 1 from by ring]
    step fm; step fm; rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 1) e); ring_nf; finish

theorem r2_drain : ∀ k a j, ⟨a + k, j, 0, d, k⟩ [fm]⊢* ⟨a, j + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a j; ring_nf; exists 0
  | succ k ih =>
    intro a j; rw [show a + (k + 1) = (a + k) + 1 from by ring, show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih a (j + 1)); ring_nf; finish

theorem block_even : ∀ k a d, ⟨a + 1, 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; ring_nf; exists 0
  | succ k ih =>
    intro a d; rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm; rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 2)); ring_nf; finish

theorem block_odd : ∀ k a d, ⟨a + 1, 2 * k + 1, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 1, d + 2 * k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; step fm; step fm; ring_nf; finish
  | succ k ih =>
    intro a d; rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm; rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 2)); ring_nf; finish

theorem r3_chain : ∀ k a c, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; exists 0
  | succ k ih =>
    intro a c; rw [show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a + 1) c); step fm; ring_nf; finish

-- Even case: d = j + 2m
theorem trans_even (j m : ℕ) :
    ⟨0, 0, 2 * j + 2 * m + 1, j + 2 * m, 0⟩ [fm]⊢⁺
    ⟨0, 0, 4 * j + 6 * m + 2, 2 * j + 4 * m + 1, 0⟩ := by
  -- Phase 1: R4 + R5 (gives ⊢⁺ via stepStar_step_stepPlus + stepPlus_stepStar)
  -- R4: (0, 0, 2j+2m+1, j+2m, 0) ⊢* (0, 0, 2j+2m+1, 0, 2j+4m)
  rw [show j + 2 * m = 0 + (j + 2 * m) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (j + 2 * m) 0)
  -- Now ⊢⁺ from (0, 0, 2j+2m+1, 0, 2(j+2m))
  -- R5+R2R1: use r5_r2r1 which gives ⊢*
  -- Need to convert ⊢⁺ to ⊢ + ⊢* form
  -- Actually, ⊢⁺ means we need at least one more step.
  -- Let me do the R5 step to get ⊢⁺
  rw [show 2 * j + 2 * m + 1 = (2 * j + 2 * m) + 1 from by ring,
      show 2 * (j + 2 * m) = (2 * j + 2 * m) + 2 * m from by ring]
  -- Goal: (0, 0, (2j+2m)+1, 0, (2j+2m)+2m) ⊢⁺ target
  -- R5: step fm
  apply stepPlus_stepStar_stepPlus
  · -- ⊢⁺ via one step
    step fm; finish
  -- After R5: (1, 0, 2j+2m, 1, (2j+2m)+2m)
  -- R2R1 chain: 2j+2m rounds
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r2r1_chain (2 * j + 2 * m) 0 1 (2 * m))
  simp only [Nat.zero_add]; rw [show 1 + (2 * j + 2 * m) = 2 * j + 2 * m + 1 from by ring]
  -- R2 drain
  rw [show 2 * j + 2 * m + 1 = (2 * j + 1) + 2 * m from by ring]
  apply stepStar_trans (r2_drain (2 * m) (2 * j + 1) 0)
  simp only [Nat.zero_add]
  -- block_even
  rw [show 2 * j + 1 + 2 * m = 2 * j + 2 * m + 1 from by ring]
  apply stepStar_trans (block_even m (2 * j) (2 * j + 2 * m + 1))
  -- R3 chain
  rw [show 2 * j + 3 * m + 1 = 0 + (2 * j + 3 * m + 1) from by ring]
  apply stepStar_trans (r3_chain (2 * j + 3 * m + 1) 0 0 (d := 2 * j + 2 * m + 1 + 2 * m))
  simp only [Nat.zero_add]; ring_nf; finish

-- Odd case: d = j + 2m + 1
theorem trans_odd (j m : ℕ) :
    ⟨0, 0, 2 * j + 2 * m + 2, j + 2 * m + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 4 * j + 6 * m + 5, 2 * j + 4 * m + 3, 0⟩ := by
  -- Phase 1: R4
  rw [show j + 2 * m + 1 = 0 + (j + 2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (j + 2 * m + 1) 0)
  -- Phase 2: R5
  rw [show 2 * j + 2 * m + 2 = (2 * j + 2 * m + 1) + 1 from by ring,
      show 2 * (j + 2 * m + 1) = (2 * j + 2 * m + 1) + (2 * m + 1) from by ring]
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  -- Phase 3: R2R1 chain
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r2r1_chain (2 * j + 2 * m + 1) 0 1 (2 * m + 1))
  simp only [Nat.zero_add]; rw [show 1 + (2 * j + 2 * m + 1) = 2 * j + 2 * m + 2 from by ring]
  -- Phase 4: R2 drain
  rw [show 2 * j + 2 * m + 2 = (2 * j + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (r2_drain (2 * m + 1) (2 * j + 1) 0)
  simp only [Nat.zero_add]
  -- Phase 5: block_odd
  rw [show 2 * j + 1 + (2 * m + 1) = 2 * j + 2 * m + 2 from by ring]
  apply stepStar_trans (block_odd m (2 * j) (2 * j + 2 * m + 2))
  -- Phase 6: R3 chain
  rw [show 2 * j + 3 * m + 2 = 0 + (2 * j + 3 * m + 2) from by ring]
  apply stepStar_trans (r3_chain (2 * j + 3 * m + 2) 0 1 (d := 2 * j + 2 * m + 2 + (2 * m + 1)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 6, 3, 0⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ j d, q = ⟨0, 0, d + j + 1, d, 0⟩ ∧ d ≥ 1 ∧ j ≤ d)
  · intro q ⟨j, d, hq, hd, hj⟩; subst hq
    rcases Nat.even_or_odd (d - j) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hd_val : d = j + 2 * m := by omega
      subst hd_val
      simp only [show j + 2 * m + j + 1 = 2 * j + 2 * m + 1 from by ring] at *
      exact ⟨⟨0, 0, 4 * j + 6 * m + 2, 2 * j + 4 * m + 1, 0⟩,
             ⟨j + (j + 2 * m), 2 * j + 4 * m + 1, by ring_nf, by omega, by omega⟩,
             trans_even j m⟩
    · have hd_val : d = j + 2 * m + 1 := by omega
      subst hd_val
      simp only [show j + 2 * m + 1 + j + 1 = 2 * j + 2 * m + 2 from by ring] at *
      exact ⟨⟨0, 0, 4 * j + 6 * m + 5, 2 * j + 4 * m + 3, 0⟩,
             ⟨j + (j + 2 * m + 1), 2 * j + 4 * m + 3, by ring_nf, by omega, by omega⟩,
             trans_odd j m⟩
  · exact ⟨2, 3, by ring_nf, by omega, by omega⟩

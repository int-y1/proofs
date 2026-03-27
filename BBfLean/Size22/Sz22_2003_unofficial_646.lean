import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #646: [35/6, 143/2, 52/55, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  1
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_646

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, n + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, n, e, f⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, n + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, n, e, f⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R1,R1,R3 chain: each round uses b-=2, e-=1, c+=1, d+=2, f+=1
theorem r113_chain :
    ∀ k, ∀ c d e f, ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢*
      ⟨(2 : ℕ), b, c + k, d + 2 * k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (c + 1) (d + 2) e (f + 1))
  ring_nf; finish

-- R3,R2,R2 drain with e+1 form
theorem r3r2r2_drain :
    ∀ k, ∀ c e f, ⟨0, 0, c + k, d, e + 1, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k + 1, f + 3 * k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
  apply stepStar_trans (h c (e + 1) (f + 3))
  ring_nf; finish

-- Transition for n=0: (0,0,0,0,1,1) →⁺ (0,0,0,1,2,5)
theorem trans_n0 : ⟨0, 0, 0, 0, 1, (1 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 1, 2, 5⟩ := by
  execute fm 7

-- Odd transition: n=2m+1 → n+1=2m+2
theorem trans_odd (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 2 * m + 2, 4 * m * m + 10 * m + 5⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * m + 2, 2 * m + 3, 4 * m * m + 14 * m + 11⟩ := by
  -- Phase 1: R4 chain (2m+1 times)
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (n := 0) (k := 2 * m + 1))
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3
  rw [show 4 * m * m + 10 * m + 5 = (4 * m * m + 10 * m + 3) + 1 + 1 from by ring]
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm; step fm
  -- Phase 3: r113_chain (m rounds)
  rw [show (2 * m + 2 : ℕ) = 2 + 2 * m from by ring]
  rw [show (2 * m + 1 : ℕ) = (m + 1) + m from by ring]
  apply stepStar_trans (r113_chain m 0 0 (m + 1) (4 * m * m + 10 * m + 5))
  simp only [Nat.zero_add]
  -- Phase 4: R1, R1
  rw [show 4 * m * m + 10 * m + 5 + m = 4 * m * m + 11 * m + 5 from by ring]
  step fm; step fm
  -- Phase 5: r3r2r2_drain (m+2 rounds)
  rw [show m + 1 + 1 = 0 + (m + 2) from by ring]
  rw [show (m + 1 : ℕ) = m + 1 from rfl]
  apply stepStar_trans (r3r2r2_drain (m + 2) 0 m (4 * m * m + 11 * m + 5))
  ring_nf; finish

-- Even transition: n=2(m+1) → n+1=2m+3
theorem trans_even (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 3, 4 * m * m + 14 * m + 11⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * m + 3, 2 * m + 4, 4 * m * m + 18 * m + 19⟩ := by
  -- Phase 1: R4 chain (2m+2 times)
  rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (n := 0) (k := 2 * m + 2))
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3
  rw [show 4 * m * m + 14 * m + 11 = (4 * m * m + 14 * m + 9) + 1 + 1 from by ring]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm; step fm
  -- Phase 3: r113_chain (m rounds)
  rw [show (2 * m + 3 : ℕ) = 3 + 2 * m from by ring]
  rw [show (2 * m + 2 : ℕ) = (m + 2) + m from by ring]
  apply stepStar_trans (r113_chain m 0 0 (m + 2) (4 * m * m + 14 * m + 11))
  simp only [Nat.zero_add]
  -- Phase 4: R1, R1, R3, R1, R2 (5 steps)
  rw [show 4 * m * m + 14 * m + 11 + m = 4 * m * m + 15 * m + 11 from by ring]
  step fm; step fm; step fm; step fm; step fm
  -- Phase 5: r3r2r2_drain (m+2 rounds)
  suffices h : ⟨0, 0, 0 + (m + 2), 2 * m + 3, (m + 1) + 1, 4 * m * m + 15 * m + 13⟩ [fm]⊢*
      ⟨(0 : ℕ), 0, 0, 2 * m + 3, 2 * m + 4, 4 * m * m + 18 * m + 19⟩ by
    convert h using 2; all_goals ring_nf
  apply stepStar_trans (r3r2r2_drain (m + 2) 0 (m + 1) (4 * m * m + 15 * m + 13))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨0, 0, 0, 2 * k, 2 * k + 1, 4 * k * k + 6 * k + 1⟩ ∨
                        q = ⟨0, 0, 0, 2 * k + 1, 2 * k + 2, 4 * k * k + 10 * k + 5⟩)
  · intro c ⟨k, hq⟩
    rcases hq with rfl | rfl
    · -- Even case: n = 2k
      rcases k with _ | k
      · -- k=0, n=0
        exact ⟨_, ⟨0, Or.inr rfl⟩, trans_n0⟩
      · -- k+1, n=2(k+1)
        exact ⟨⟨0, 0, 0, 2 * k + 3, 2 * k + 4, 4 * k * k + 18 * k + 19⟩,
          ⟨k + 1, Or.inr (by congr 1; ring_nf)⟩,
          by have := trans_even k; convert this using 2; all_goals ring_nf⟩
    · -- Odd case: n = 2k+1
      exact ⟨⟨0, 0, 0, 2 * k + 2, 2 * k + 3, 4 * k * k + 14 * k + 11⟩,
        ⟨k + 1, Or.inl (by congr 1; ring_nf)⟩,
        by have := trans_odd k; convert this using 2⟩
  · exact ⟨0, Or.inl rfl⟩

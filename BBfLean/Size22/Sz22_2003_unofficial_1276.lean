import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1276: [54/35, 5/33, 7/3, 1331/2, 3/11]

Vector representation:
```
 1  3 -1 -1  0
 0 -1  1  0 -1
 0 -1  0  1  0
-1  0  0  0  3
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1276

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih a d (e + 3)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [Nat.add_succ b k]; step fm
    apply stepStar_trans (ih a b (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e,
    ⟨a, b + 1, 0, d + k, e + k⟩ [fm]⊢* ⟨a + k, b + 2 * k + 1, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [Nat.add_succ d k, Nat.add_succ e k]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d e); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b c e,
    ⟨a, b + k, c, 0, e + k⟩ [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [Nat.add_succ b k, Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih a b (c + 1) e); ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a b c,
    ⟨a, b + 1, c + k, 0, 0⟩ [fm]⊢* ⟨a + k, b + 2 * k + 1, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [Nat.add_succ c k]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2) c); ring_nf; finish

-- Common opening: R4 drain + R5 + R2 + R1
-- (a+1, 0, 0, d+1, 0) ⊢⁺ (1, 3, 0, d, 3a+1)
theorem opening :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨1, 3, 0, d, 3 * a + 1⟩ := by
  step fm
  apply stepStar_trans
  · have := r4_chain a 0 (d + 1) 3; rwa [Nat.zero_add] at this
  rw [show 3 + 3 * a = (3 * a + 2) + 1 from by ring]
  step fm
  rw [show 3 * a + 2 = (3 * a + 1) + 1 from by ring]
  step fm; step fm; finish

-- Case 1: 3a+1 ≤ d
theorem main_case1 (h : 3 * a + 1 ≤ d) :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨3 * a + 2, 0, 0, d + 3 * a + 4, 0⟩ := by
  apply stepPlus_stepStar_stepPlus opening
  apply stepStar_trans
  · have := r2r1_chain (3 * a + 1) 1 2 (d - (3 * a + 1)) 0
    rw [show 2 + 1 = 3 from by ring,
        show d - (3 * a + 1) + (3 * a + 1) = d from by omega,
        show 0 + (3 * a + 1) = 3 * a + 1 from by ring] at this
    exact this
  rw [show 1 + (3 * a + 1) = 3 * a + 2 from by ring,
      show 2 + 2 * (3 * a + 1) + 1 = 6 * a + 5 from by ring]
  apply stepStar_trans
  · have := r3_chain (6 * a + 5) (3 * a + 2) 0 (d - (3 * a + 1))
    rwa [Nat.zero_add] at this
  rw [show d - (3 * a + 1) + (6 * a + 5) = d + 3 * a + 4 from by omega]
  finish

-- Case 2: d < 3a+1, with a ≤ d
theorem main_case2 (h1 : d < 3 * a + 1) (h2 : a ≤ d) :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨3 * a + 2, 0, 0, d + 3 * a + 4, 0⟩ := by
  apply stepPlus_stepStar_stepPlus opening
  -- R2R1 chain with k = d
  apply stepStar_trans
  · have := r2r1_chain d 1 2 0 (3 * a + 1 - d)
    rw [show 2 + 1 = 3 from by ring,
        show 0 + d = d from by ring,
        show (3 * a + 1 - d) + d = 3 * a + 1 from by omega] at this
    exact this
  rw [show 1 + d = d + 1 from by ring,
      show 2 + 2 * d + 1 = 2 * d + 3 from by ring]
  -- R2 drain: 3a+1-d steps
  apply stepStar_trans
  · have := r2_drain (3 * a + 1 - d) (d + 1) (3 * d + 2 - 3 * a) 0 0
    rw [show (3 * d + 2 - 3 * a) + (3 * a + 1 - d) = 2 * d + 3 from by omega,
        show 0 + (3 * a + 1 - d) = 3 * a + 1 - d from by omega] at this
    exact this
  -- R3R1 chain: 3a+1-d pairs
  apply stepStar_trans
  · have := r3r1_chain (3 * a + 1 - d) (d + 1) (3 * d + 1 - 3 * a) 0
    rw [show (3 * d + 1 - 3 * a) + 1 = 3 * d + 2 - 3 * a from by omega,
        show 0 + (3 * a + 1 - d) = 3 * a + 1 - d from by omega] at this
    exact this
  rw [show (d + 1) + (3 * a + 1 - d) = 3 * a + 2 from by omega,
      show (3 * d + 1 - 3 * a) + 2 * (3 * a + 1 - d) + 1 = d + 3 * a + 4 from by omega]
  -- R3 chain
  apply stepStar_trans
  · have := r3_chain (d + 3 * a + 4) (3 * a + 2) 0 0
    rwa [Nat.zero_add] at this
  finish

-- Main transition under invariant a ≤ d
theorem main_trans (h : a ≤ d) :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨3 * a + 2, 0, 0, d + 3 * a + 4, 0⟩ := by
  by_cases h2 : 3 * a + 1 ≤ d
  · exact main_case1 h2
  · exact main_case2 (by omega) h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 3, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 1, 0, 0, d + 1, 0⟩ ∧ a ≤ d)
  · intro c ⟨a, d, hq, hle⟩
    subst hq
    exact ⟨⟨3 * a + 2, 0, 0, d + 3 * a + 4, 0⟩,
           ⟨3 * a + 1, d + 3 * a + 3, by ring_nf, by omega⟩,
           main_trans hle⟩
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1276

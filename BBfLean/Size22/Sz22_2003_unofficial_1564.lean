import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1564: [7/45, 242/15, 3/11, 175/2, 11/7]

Vector representation:
```
 0 -2 -1  1  0
 1 -1 -1  0  2
 0  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1564

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | _ => none

-- R3 chain (c=0): transfer e to b
theorem r3_chain : ∀ k, ∀ a b d e,
    ⟨a, b, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d e)
    ring_nf; finish

-- R4 chain (b=0, e=0): drain a, build c and d
theorem r4_chain : ∀ k, ∀ a c d,
    ⟨a + k, (0 : ℕ), c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (d + 1))
    ring_nf; finish

-- R3+R2 chain (b=0): drain c while building a and e
theorem r3r2_chain : ∀ k, ∀ a c d e,
    ⟨a, (0 : ℕ), c + k, d, e + 1⟩ [fm]⊢* ⟨a + k, 0, c, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    ring_nf; finish

-- R4+R1+R1 macro chain
theorem r4r1r1_chain : ∀ k, ∀ a b d,
    ⟨a + k + 1, b + 4 * k, (0 : ℕ), d, 0⟩ [fm]⊢* ⟨a + 1, b, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k) + 2 + 2 from by ring]
    step fm  -- R4
    step fm  -- R1
    step fm  -- R1
    rw [show d + 1 + 1 + 1 = (d + 3) from by ring]
    apply stepStar_trans (ih a b (d + 3))
    ring_nf; finish

-- Phase 1 body (after R5): R3, R2, then r3r2_chain
theorem phase1_body : ∀ c d,
    ⟨(0 : ℕ), 0, c + 2, d, 1⟩ [fm]⊢* ⟨c + 2, 0, 0, d, c + 3⟩ := by
  intro c d
  step fm  -- R3: (0, 1, c+2, d, 0)
  step fm  -- R2: (1, 0, c+1, d, 2)
  -- Now state is (1, 0, c+1, d, 2). r3r2_chain needs (a, 0, c'+k, d', e'+1).
  -- a=1, c'=0, k=c+1, d'=d, e'=1. So e'+1=2. ✓
  rw [show c + 1 = 0 + (c + 1) from by ring]
  have h := r3r2_chain (c + 1) 1 0 d 1
  rw [show 1 + (c + 1) + 1 = c + 3 from by ring,
      show 1 + (c + 1) = c + 2 from by ring] at h
  exact h

-- Phase 2: R3 chain (c=0, so R3 has priority)
theorem phase2 : ∀ c d,
    ⟨c + 2, (0 : ℕ), 0, d, c + 3⟩ [fm]⊢* ⟨c + 2, c + 3, 0, d, 0⟩ := by
  intro c d
  have h := r3_chain (c + 3) (c + 2) 0 d 0
  rw [show 0 + (c + 3) = c + 3 from by ring] at h
  exact h

-- b=3 step: (a+1, 3, 0, d, 0) -> (a+1, 2, 0, d+2, 0)
-- R4, R1, R2, R3, R3
theorem b3_to_b2 : ∀ a d,
    ⟨a + 1, (3 : ℕ), 0, d, 0⟩ [fm]⊢* ⟨a + 1, 2, 0, d + 2, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; finish

-- b=1 step: (a+1, 1, 0, d, 0) -> (a+2, 3, 0, d+1, 0)
-- R4, R2, R3, R2, R3, R3, R3
theorem b1_to_b3 : ∀ a d,
    ⟨a + 1, (1 : ℕ), 0, d, 0⟩ [fm]⊢* ⟨a + 2, 3, 0, d + 1, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- b=2 tail: (a+1, 2, 0, d, 0) -> (0, 0, 2a+1, d+a+2, 0)
-- R4, R1 -> (a, 0, 1, d+2, 0) then a R4s
theorem b2_tail : ∀ a d,
    ⟨a + 1, (2 : ℕ), 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 1, d + a + 2, 0⟩ := by
  intro a d
  step fm  -- R4: (a, 2, 2, d+1, 0)
  step fm  -- R1: (a, 0, 1, d+1+1, 0)
  rw [show a = 0 + a from by ring,
      show d + 1 + 1 = d + 2 from by ring,
      show 2 * (0 + a) + 1 = 2 * a + 1 from by ring,
      show d + (0 + a) + 2 = d + a + 2 from by ring]
  have h := r4_chain a 0 1 (d + 2)
  rw [show 1 + 2 * a = 2 * a + 1 from by ring,
      show (d + 2) + a = d + a + 2 from by ring] at h
  exact h

-- b=0 tail: (a, 0, 0, d, 0) -> (0, 0, 2a, d+a, 0)
-- a R4s
theorem b0_tail : ∀ a d,
    ⟨a, (0 : ℕ), 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a, d + a, 0⟩ := by
  intro a d
  rw [show a = 0 + a from by ring,
      show 2 * (0 + a) = 2 * a from by ring,
      show d + (0 + a) = d + a from by ring]
  have h := r4_chain a 0 0 d
  rw [show 0 + 2 * a = 2 * a from by ring] at h
  exact h

-- Case c%4=0 (c=4m)
theorem trans_mod0 (m d : ℕ) :
    ⟨(0 : ℕ), 0, 4 * m + 2, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 3, d + 6 * m + 5, 0⟩ := by
  step fm
  apply stepStar_trans (phase1_body (4 * m) d)
  apply stepStar_trans (phase2 (4 * m) d)
  rw [show 4 * m + 2 = 3 * m + 1 + m + 1 from by ring,
      show 4 * m + 3 = 3 + 4 * m from by ring]
  apply stepStar_trans (r4r1r1_chain m (3 * m + 1) 3 d)
  rw [show 3 * m + 1 + 1 = 3 * m + 2 from by ring]
  apply stepStar_trans (b3_to_b2 (3 * m + 1) (d + 3 * m))
  rw [show 3 * m + 1 + 1 = 3 * m + 2 from by ring]
  apply stepStar_trans (b2_tail (3 * m + 1) (d + 3 * m + 2))
  ring_nf; finish

-- Case c%4=1 (c=4m+1)
theorem trans_mod1 (m d : ℕ) :
    ⟨(0 : ℕ), 0, 4 * m + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 4, d + 6 * m + 5, 0⟩ := by
  step fm
  apply stepStar_trans (phase1_body (4 * m + 1) d)
  apply stepStar_trans (phase2 (4 * m + 1) d)
  rw [show 4 * m + 1 + 2 = 3 * m + 1 + (m + 1) + 1 from by ring,
      show 4 * m + 1 + 3 = 0 + 4 * (m + 1) from by ring]
  apply stepStar_trans (r4r1r1_chain (m + 1) (3 * m + 1) 0 d)
  rw [show 3 * m + 1 + 1 = 3 * m + 2 from by ring,
      show d + 3 * (m + 1) = d + 3 * m + 3 from by ring]
  apply stepStar_trans (b0_tail (3 * m + 2) (d + 3 * m + 3))
  ring_nf; finish

-- Case c%4=2 (c=4m+2)
theorem trans_mod2 (m d : ℕ) :
    ⟨(0 : ℕ), 0, 4 * m + 4, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 7, d + 6 * m + 11, 0⟩ := by
  step fm
  apply stepStar_trans (phase1_body (4 * m + 2) d)
  apply stepStar_trans (phase2 (4 * m + 2) d)
  rw [show 4 * m + 2 + 2 = 3 * m + 2 + (m + 1) + 1 from by ring,
      show 4 * m + 2 + 3 = 1 + 4 * (m + 1) from by ring]
  apply stepStar_trans (r4r1r1_chain (m + 1) (3 * m + 2) 1 d)
  rw [show 3 * m + 2 + 1 = 3 * m + 3 from by ring,
      show d + 3 * (m + 1) = d + 3 * m + 3 from by ring]
  apply stepStar_trans (b1_to_b3 (3 * m + 2) (d + 3 * m + 3))
  rw [show 3 * m + 2 + 2 = 3 * m + 4 from by ring]
  apply stepStar_trans (b3_to_b2 (3 * m + 3) (d + 3 * m + 4))
  rw [show 3 * m + 3 + 1 = 3 * m + 4 from by ring]
  apply stepStar_trans (b2_tail (3 * m + 3) (d + 3 * m + 6))
  ring_nf; finish

-- Case c%4=3 (c=4m+3)
theorem trans_mod3 (m d : ℕ) :
    ⟨(0 : ℕ), 0, 4 * m + 5, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 7, d + 6 * m + 8, 0⟩ := by
  step fm
  apply stepStar_trans (phase1_body (4 * m + 3) d)
  apply stepStar_trans (phase2 (4 * m + 3) d)
  rw [show 4 * m + 3 + 2 = 3 * m + 3 + (m + 1) + 1 from by ring,
      show 4 * m + 3 + 3 = 2 + 4 * (m + 1) from by ring]
  apply stepStar_trans (r4r1r1_chain (m + 1) (3 * m + 3) 2 d)
  rw [show 3 * m + 3 + 1 = 3 * m + 4 from by ring,
      show d + 3 * (m + 1) = d + 3 * m + 3 from by ring]
  apply stepStar_trans (b2_tail (3 * m + 3) (d + 3 * m + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c + 2, d + 1, 0⟩)
  · intro q ⟨c, d, hq⟩; subst hq
    obtain ⟨r, s, hs, rfl⟩ : ∃ r s, s < 4 ∧ c = 4 * r + s := by
      exact ⟨c / 4, c % 4, Nat.mod_lt c (by omega), by omega⟩
    rcases s with _ | _ | _ | _ | s
    · exact ⟨_, ⟨6 * r + 1, d + 6 * r + 4, rfl⟩, trans_mod0 r d⟩
    · exact ⟨_, ⟨6 * r + 2, d + 6 * r + 4, rfl⟩, trans_mod1 r d⟩
    · exact ⟨_, ⟨6 * r + 5, d + 6 * r + 10, rfl⟩, trans_mod2 r d⟩
    · exact ⟨_, ⟨6 * r + 5, d + 6 * r + 7, rfl⟩, trans_mod3 r d⟩
    · omega
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1564

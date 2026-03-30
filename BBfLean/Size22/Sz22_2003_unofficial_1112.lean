import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1112: [5/6, 4/35, 539/2, 3/7, 98/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1112

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- R3 chain: drain a to d and e.
theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 1))
    ring_nf; finish

-- R4 chain: drain d to b.
theorem d_to_b : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Interleave round (8 steps).
theorem interleave_round : ⟨0, b + 5, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  finish

-- Interleave chain: k rounds.
theorem interleave_chain : ∀ k b c e, ⟨0, b + 5 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 5 * (k + 1) = (b + 5) + 5 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 5) c (e + 1))
    apply stepStar_trans (interleave_round (b := b) (c := c + 3 * k) (e := e))
    ring_nf; finish

-- Remainder r=1.
theorem remainder_1 : ⟨0, 1, c + 1, 0, e + 1⟩ [fm]⊢* ⟨4, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Remainder r=2.
theorem remainder_2 : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢* ⟨3, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Remainder r=3.
theorem remainder_3 : ⟨0, 3, c, 0, e + 1⟩ [fm]⊢* ⟨2, 0, c + 1, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Remainder r=4.
theorem remainder_4 : ⟨0, 4, c, 0, e + 1⟩ [fm]⊢* ⟨1, 0, c + 2, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- R3+R2+R2 chain: k rounds.
theorem r3r2r2_chain : ∀ k a e, ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

-- R5+R2+R2: for the r=0 case.
theorem r5r2r2 : ⟨0, 0, c + 2, 0, e + 1⟩ [fm]⊢* ⟨5, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- Main transition for each mod-5 case.
-- We prove (a, 0, 0, 0, e) →⁺ (a', 0, 0, 0, e') by composing phases.

-- Helper: the full cycle uses this pattern for all cases:
-- 1. R3 drain a: (a, 0, 0, 0, e) →* (0, 0, 0, 2a, a+e)
-- 2. R4 drain d to b: (0, 0, 0, 2a, a+e) →* (0, 2a, 0, 0, a+e)
-- 3. Interleave chain
-- 4. Remainder
-- 5. R3R2R2 chain or R5R2R2 + R3R2R2

theorem case_mod5_1 : ∀ m e, ⟨5 * m + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨9 * m + 3, 0, 0, 0, 6 * m + e⟩ := by
  intro m e
  -- At least 1 step since 5*m+1 ≠ 9*m+3 or 0 ≠ 6*m+e (for all m, e).
  -- Phase 1+2: (5*m+1, 0, 0, 0, e) →* (0, 10*m+2, 0, 0, 5*m+1+e)
  have phase12 : ⟨5 * m + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 10 * m + 2, 0, 0, 5 * m + 1 + e⟩ := by
    rw [show 5 * m + 1 = 0 + (5 * m + 1) from by ring]
    apply stepStar_trans (r3_drain (5 * m + 1) 0 0 e)
    rw [show 0 + 2 * (5 * m + 1) = 0 + (10 * m + 2) from by ring,
        show e + (5 * m + 1) = 5 * m + 1 + e from by ring]
    have h := d_to_b (10 * m + 2) 0 0 (5 * m + 1 + e)
    simpa using h
  -- Phase 3: interleave (2m rounds)
  have phase3 : ⟨0, 10 * m + 2, 0, 0, 5 * m + 1 + e⟩ [fm]⊢* ⟨0, 2, 6 * m, 0, 3 * m + 1 + e⟩ := by
    rw [show (10 * m + 2 : ℕ) = 2 + 5 * (2 * m) from by ring,
        show 5 * m + 1 + e = (3 * m + 1 + e) + 2 * m from by ring]
    apply stepStar_trans (interleave_chain (2 * m) 2 0 (3 * m + 1 + e))
    rw [show 0 + 3 * (2 * m) = 6 * m from by ring]
    finish
  -- Phase 4: remainder r=2
  have phase4 : ⟨0, 2, 6 * m, 0, 3 * m + 1 + e⟩ [fm]⊢* ⟨3, 0, 6 * m, 0, 3 * m + e⟩ := by
    rw [show 3 * m + 1 + e = (3 * m + e) + 1 from by ring]
    exact remainder_2
  -- Phase 5: R3R2R2 chain (3m rounds)
  have phase5 : ⟨3, 0, 6 * m, 0, 3 * m + e⟩ [fm]⊢* ⟨9 * m + 3, 0, 0, 0, 6 * m + e⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from by ring, show 6 * m = 2 * (3 * m) from by ring]
    apply stepStar_trans (r3r2r2_chain (3 * m) 2 (3 * m + e))
    ring_nf; finish
  apply stepStar_stepPlus
  · exact stepStar_trans phase12 (stepStar_trans phase3 (stepStar_trans phase4 phase5))
  · intro h; simp [Q] at h; omega

theorem case_mod5_2 : ∀ m e, ⟨5 * m + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨9 * m + 4, 0, 0, 0, 6 * m + e + 2⟩ := by
  intro m e
  have phase12 : ⟨5 * m + 2, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 10 * m + 4, 0, 0, 5 * m + 2 + e⟩ := by
    rw [show 5 * m + 2 = 0 + (5 * m + 2) from by ring]
    apply stepStar_trans (r3_drain (5 * m + 2) 0 0 e)
    rw [show 0 + 2 * (5 * m + 2) = 0 + (10 * m + 4) from by ring,
        show e + (5 * m + 2) = 5 * m + 2 + e from by ring]
    have h := d_to_b (10 * m + 4) 0 0 (5 * m + 2 + e)
    simpa using h
  have phase3 : ⟨0, 10 * m + 4, 0, 0, 5 * m + 2 + e⟩ [fm]⊢* ⟨0, 4, 6 * m, 0, 3 * m + 2 + e⟩ := by
    rw [show (10 * m + 4 : ℕ) = 4 + 5 * (2 * m) from by ring,
        show 5 * m + 2 + e = (3 * m + 2 + e) + 2 * m from by ring]
    apply stepStar_trans (interleave_chain (2 * m) 4 0 (3 * m + 2 + e))
    rw [show 0 + 3 * (2 * m) = 6 * m from by ring]
    finish
  have phase4 : ⟨0, 4, 6 * m, 0, 3 * m + 2 + e⟩ [fm]⊢* ⟨1, 0, 6 * m + 2, 0, 3 * m + 1 + e⟩ := by
    rw [show 3 * m + 2 + e = (3 * m + 1 + e) + 1 from by ring]
    exact remainder_4
  have phase5 : ⟨1, 0, 6 * m + 2, 0, 3 * m + 1 + e⟩ [fm]⊢* ⟨9 * m + 4, 0, 0, 0, 6 * m + e + 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring, show 6 * m + 2 = 2 * (3 * m + 1) from by ring]
    apply stepStar_trans (r3r2r2_chain (3 * m + 1) 0 (3 * m + 1 + e))
    ring_nf; finish
  apply stepStar_stepPlus
  · exact stepStar_trans phase12 (stepStar_trans phase3 (stepStar_trans phase4 phase5))
  · intro h; simp [Q] at h; omega

theorem case_mod5_3 : ∀ m e, ⟨5 * m + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨9 * m + 7, 0, 0, 0, 6 * m + e + 2⟩ := by
  intro m e
  have phase12 : ⟨5 * m + 3, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 10 * m + 6, 0, 0, 5 * m + 3 + e⟩ := by
    rw [show 5 * m + 3 = 0 + (5 * m + 3) from by ring]
    apply stepStar_trans (r3_drain (5 * m + 3) 0 0 e)
    rw [show 0 + 2 * (5 * m + 3) = 0 + (10 * m + 6) from by ring,
        show e + (5 * m + 3) = 5 * m + 3 + e from by ring]
    have h := d_to_b (10 * m + 6) 0 0 (5 * m + 3 + e)
    simpa using h
  have phase3 : ⟨0, 10 * m + 6, 0, 0, 5 * m + 3 + e⟩ [fm]⊢* ⟨0, 1, 6 * m + 3, 0, 3 * m + 2 + e⟩ := by
    rw [show (10 * m + 6 : ℕ) = 1 + 5 * (2 * m + 1) from by ring,
        show 5 * m + 3 + e = (3 * m + 2 + e) + (2 * m + 1) from by ring]
    apply stepStar_trans (interleave_chain (2 * m + 1) 1 0 (3 * m + 2 + e))
    rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
    finish
  have phase4 : ⟨0, 1, 6 * m + 3, 0, 3 * m + 2 + e⟩ [fm]⊢* ⟨4, 0, 6 * m + 2, 0, 3 * m + 1 + e⟩ := by
    rw [show 6 * m + 3 = (6 * m + 2) + 1 from by ring,
        show 3 * m + 2 + e = (3 * m + 1 + e) + 1 from by ring]
    exact remainder_1
  have phase5 : ⟨4, 0, 6 * m + 2, 0, 3 * m + 1 + e⟩ [fm]⊢* ⟨9 * m + 7, 0, 0, 0, 6 * m + e + 2⟩ := by
    rw [show (4 : ℕ) = 3 + 1 from by ring, show 6 * m + 2 = 2 * (3 * m + 1) from by ring]
    apply stepStar_trans (r3r2r2_chain (3 * m + 1) 3 (3 * m + 1 + e))
    ring_nf; finish
  apply stepStar_stepPlus
  · exact stepStar_trans phase12 (stepStar_trans phase3 (stepStar_trans phase4 phase5))
  · intro h; simp [Q] at h; omega

theorem case_mod5_4 : ∀ m e, ⟨5 * m + 4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨9 * m + 8, 0, 0, 0, 6 * m + e + 4⟩ := by
  intro m e
  have phase12 : ⟨5 * m + 4, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 10 * m + 8, 0, 0, 5 * m + 4 + e⟩ := by
    rw [show 5 * m + 4 = 0 + (5 * m + 4) from by ring]
    apply stepStar_trans (r3_drain (5 * m + 4) 0 0 e)
    rw [show 0 + 2 * (5 * m + 4) = 0 + (10 * m + 8) from by ring,
        show e + (5 * m + 4) = 5 * m + 4 + e from by ring]
    have h := d_to_b (10 * m + 8) 0 0 (5 * m + 4 + e)
    simpa using h
  have phase3 : ⟨0, 10 * m + 8, 0, 0, 5 * m + 4 + e⟩ [fm]⊢* ⟨0, 3, 6 * m + 3, 0, 3 * m + 3 + e⟩ := by
    rw [show (10 * m + 8 : ℕ) = 3 + 5 * (2 * m + 1) from by ring,
        show 5 * m + 4 + e = (3 * m + 3 + e) + (2 * m + 1) from by ring]
    apply stepStar_trans (interleave_chain (2 * m + 1) 3 0 (3 * m + 3 + e))
    rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
    finish
  have phase4 : ⟨0, 3, 6 * m + 3, 0, 3 * m + 3 + e⟩ [fm]⊢* ⟨2, 0, 6 * m + 4, 0, 3 * m + 2 + e⟩ := by
    rw [show 3 * m + 3 + e = (3 * m + 2 + e) + 1 from by ring]
    exact remainder_3
  have phase5 : ⟨2, 0, 6 * m + 4, 0, 3 * m + 2 + e⟩ [fm]⊢* ⟨9 * m + 8, 0, 0, 0, 6 * m + e + 4⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring, show 6 * m + 4 = 2 * (3 * m + 2) from by ring]
    apply stepStar_trans (r3r2r2_chain (3 * m + 2) 1 (3 * m + 2 + e))
    ring_nf; finish
  apply stepStar_stepPlus
  · exact stepStar_trans phase12 (stepStar_trans phase3 (stepStar_trans phase4 phase5))
  · intro h; simp [Q] at h; omega

theorem case_mod5_0 : ∀ m e, ⟨5 * (m + 1), 0, 0, 0, e⟩ [fm]⊢⁺ ⟨9 * m + 11, 0, 0, 0, 6 * m + e + 4⟩ := by
  intro m e
  have phase12 : ⟨5 * (m + 1), 0, 0, 0, e⟩ [fm]⊢* ⟨0, 10 * m + 10, 0, 0, 5 * m + 5 + e⟩ := by
    rw [show 5 * (m + 1) = 0 + (5 * m + 5) from by ring]
    apply stepStar_trans (r3_drain (5 * m + 5) 0 0 e)
    rw [show 0 + 2 * (5 * m + 5) = 0 + (10 * m + 10) from by ring,
        show e + (5 * m + 5) = 5 * m + 5 + e from by ring]
    have h := d_to_b (10 * m + 10) 0 0 (5 * m + 5 + e)
    simpa using h
  have phase3 : ⟨0, 10 * m + 10, 0, 0, 5 * m + 5 + e⟩ [fm]⊢* ⟨0, 0, 6 * m + 6, 0, 3 * m + 3 + e⟩ := by
    rw [show (10 * m + 10 : ℕ) = 0 + 5 * (2 * m + 2) from by ring,
        show 5 * m + 5 + e = (3 * m + 3 + e) + (2 * m + 2) from by ring]
    apply stepStar_trans (interleave_chain (2 * m + 2) 0 0 (3 * m + 3 + e))
    rw [show 0 + 3 * (2 * m + 2) = 6 * m + 6 from by ring]
    finish
  have phase4 : ⟨0, 0, 6 * m + 6, 0, 3 * m + 3 + e⟩ [fm]⊢* ⟨5, 0, 6 * m + 4, 0, 3 * m + 2 + e⟩ := by
    rw [show 6 * m + 6 = (6 * m + 4) + 2 from by ring,
        show 3 * m + 3 + e = (3 * m + 2 + e) + 1 from by ring]
    exact r5r2r2
  have phase5 : ⟨5, 0, 6 * m + 4, 0, 3 * m + 2 + e⟩ [fm]⊢* ⟨9 * m + 11, 0, 0, 0, 6 * m + e + 4⟩ := by
    rw [show (5 : ℕ) = 4 + 1 from by ring, show 6 * m + 4 = 2 * (3 * m + 2) from by ring]
    apply stepStar_trans (r3r2r2_chain (3 * m + 2) 4 (3 * m + 2 + e))
    ring_nf; finish
  apply stepStar_stepPlus
  · exact stepStar_trans phase12 (stepStar_trans phase3 (stepStar_trans phase4 phase5))
  · intro h; simp [Q] at h; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    obtain ⟨m, rfl | rfl | rfl | rfl | rfl⟩ :
        ∃ m, a = 5 * m + 1 ∨ a = 5 * m + 2 ∨ a = 5 * m + 3 ∨ a = 5 * m + 4 ∨ a = 5 * (m + 1) :=
      ⟨(a - 1) / 5, by omega⟩
    · exact ⟨_, ⟨9 * m + 3, 6 * m + e, rfl, by omega⟩, case_mod5_1 m e⟩
    · exact ⟨_, ⟨9 * m + 4, 6 * m + e + 2, rfl, by omega⟩, case_mod5_2 m e⟩
    · exact ⟨_, ⟨9 * m + 7, 6 * m + e + 2, rfl, by omega⟩, case_mod5_3 m e⟩
    · exact ⟨_, ⟨9 * m + 8, 6 * m + e + 4, rfl, by omega⟩, case_mod5_4 m e⟩
    · exact ⟨_, ⟨9 * m + 11, 6 * m + e + 4, rfl, by omega⟩, case_mod5_0 m e⟩
  · exact ⟨3, 0, rfl, by omega⟩

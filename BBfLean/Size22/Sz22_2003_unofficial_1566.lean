import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1566: [7/45, 242/5, 25/77, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  2
 0  0  2 -1 -1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1566

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R5+R1 chain (odd b drain): k+1 rounds, each R5 then R1.
theorem r5r1_odd : ∀ k, ∀ a d,
    ⟨a + k + 1 + 1, (2 * k + 1) + 2, 0, d, 0⟩ [fm]⊢*
    ⟨a + 1, 1, 0, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; finish
  · rw [show a + (k + 1) + 1 + 1 = (a + k + 1 + 1) + 1 from by ring,
        show (2 * (k + 1) + 1) + 2 = ((2 * k + 1) + 2) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- R5+R1 chain (even b drain): m+1 rounds, each R5 then R1.
theorem r5r1_even : ∀ m, ∀ a d,
    ⟨a + m + 1, (2 * m) + 2, 0, d, 0⟩ [fm]⊢*
    ⟨a, 0, 0, d + 2 * m + 2, 0⟩ := by
  intro m; induction' m with m ih <;> intro a d
  · step fm; step fm; finish
  · rw [show a + (m + 1) + 1 = (a + m + 1) + 1 from by ring,
        show (2 * (m + 1)) + 2 = ((2 * m) + 2) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- R3+R2+R2 chain with b=0: k+1 rounds.
theorem r3r2r2_b0 : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d + k + 1, e + 1⟩ [fm]⊢*
    ⟨a + 2 * k + 2, 0, 0, d, e + 3 * k + 4⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; step fm; step fm; finish
  · rw [show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 3)); ring_nf; finish

-- R3+R2+R2 chain with b=1: k+1 rounds.
theorem r3r2r2_b1 : ∀ k, ∀ a d e,
    ⟨a, 1, 0, d + k + 1, e + 1⟩ [fm]⊢*
    ⟨a + 2 * k + 2, 1, 0, d, e + 3 * k + 4⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; step fm; step fm; finish
  · rw [show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 3)); ring_nf; finish

-- R4 drain: transfer e to b.
theorem r4_drain : ∀ k, ∀ a b,
    ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm; apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- Odd half-step: (k+a+2, 2k+3, 0, 0, 0) ⊢⁺ (a+4k+7, 6k+12, 0, 0, 0)
theorem odd_step (a k : ℕ) :
    ⟨k + a + 2, 2 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 7, 6 * k + 12, 0, 0, 0⟩ := by
  -- Phase 1: R5+R1 (k+1 rounds)
  have p1 : ⟨k + a + 2, 2 * k + 3, 0, 0, 0⟩ [fm]⊢* ⟨a + 1, 1, 0, 2 * k + 2, 0⟩ := by
    rw [show k + a + 2 = a + k + 1 + 1 from by ring,
        show 2 * k + 3 = (2 * k + 1) + 2 from by ring]
    have h := r5r1_odd k a 0
    rw [show (0 : ℕ) + 2 * k + 2 = 2 * k + 2 from by ring] at h
    exact h
  -- Phase 2: R5, R2
  have p2 : ⟨a + 1, 1, 0, 2 * k + 2, 0⟩ [fm]⊢⁺ ⟨a + 1, 1, 0, 2 * k + 3, 2⟩ := by
    step fm; step fm; finish
  -- Phase 3: R3+R2+R2 with b=1 (2k+3 rounds via chain param 2k+2)
  have p3 : ⟨a + 1, 1, 0, 2 * k + 3, 2⟩ [fm]⊢* ⟨a + 4 * k + 7, 1, 0, 0, 6 * k + 11⟩ := by
    rw [show 2 * k + 3 = 0 + (2 * k + 2) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    have h := r3r2r2_b1 (2 * k + 2) (a + 1) 0 1
    rw [show a + 1 + 2 * (2 * k + 2) + 2 = a + 4 * k + 7 from by ring,
        show 1 + 3 * (2 * k + 2) + 4 = 6 * k + 11 from by ring] at h
    exact h
  -- Phase 4: R4 drain
  have p4 : ⟨a + 4 * k + 7, 1, 0, 0, 6 * k + 11⟩ [fm]⊢* ⟨a + 4 * k + 7, 6 * k + 12, 0, 0, 0⟩ := by
    have h := r4_drain (6 * k + 11) (a + 4 * k + 7) 1
    rw [show 1 + (6 * k + 11) = 6 * k + 12 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2 (stepStar_trans p3 p4))

-- Even half-step: (a+4k+7, 6k+12, 0, 0, 0) ⊢⁺ (a+13k+27, 18k+41, 0, 0, 0)
theorem even_step (a k : ℕ) :
    ⟨a + 4 * k + 7, 6 * k + 12, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 13 * k + 27, 18 * k + 41, 0, 0, 0⟩ := by
  -- Phase 5: R5+R1 (3k+6 rounds, even drain)
  have p5 : ⟨a + 4 * k + 7, 6 * k + 12, 0, 0, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 6 * k + 12, 0⟩ := by
    rw [show (6 * k + 12 : ℕ) = (2 * (3 * k + 5)) + 2 from by ring,
        show a + 4 * k + 7 = (a + k + 1) + (3 * k + 5) + 1 from by ring]
    have h := r5r1_even (3 * k + 5) (a + k + 1) 0
    simp at h; exact h
  -- Phase 6: R5, R2
  have p6 : ⟨a + k + 1, 0, 0, 6 * k + 12, 0⟩ [fm]⊢⁺ ⟨a + k + 1, 0, 0, 6 * k + 13, 2⟩ := by
    rw [show a + k + 1 = (a + k) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 7: R3+R2+R2 with b=0 (6k+13 rounds via chain param 6k+12)
  have p7 : ⟨a + k + 1, 0, 0, 6 * k + 13, 2⟩ [fm]⊢* ⟨a + 13 * k + 27, 0, 0, 0, 18 * k + 41⟩ := by
    rw [show 6 * k + 13 = 0 + (6 * k + 12) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    have h := r3r2r2_b0 (6 * k + 12) (a + k + 1) 0 1
    rw [show a + k + 1 + 2 * (6 * k + 12) + 2 = a + 13 * k + 27 from by ring,
        show 1 + 3 * (6 * k + 12) + 4 = 18 * k + 41 from by ring] at h
    exact h
  -- Phase 8: R4 drain
  have p8 : ⟨a + 13 * k + 27, 0, 0, 0, 18 * k + 41⟩ [fm]⊢* ⟨a + 13 * k + 27, 18 * k + 41, 0, 0, 0⟩ := by
    have h := r4_drain (18 * k + 41) (a + 13 * k + 27) 0
    rw [show (0 : ℕ) + (18 * k + 41) = 18 * k + 41 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus p5
    (stepPlus_stepStar_stepPlus p6 (stepStar_trans p7 p8))

-- Combined two-step transition.
theorem main_trans (a k : ℕ) :
    ⟨k + a + 2, 2 * k + 3, 0, 0, 0⟩ [fm]⊢⁺
    ⟨(9 * k + 19) + (4 * k + a + 6) + 2, 2 * (9 * k + 19) + 3, 0, 0, 0⟩ := by
  have h1 := odd_step a k
  have h2 := even_step a k
  rw [show a + 13 * k + 27 = (9 * k + 19) + (4 * k + a + 6) + 2 from by ring,
      show 18 * k + 41 = 2 * (9 * k + 19) + 3 from by ring] at h2
  exact stepPlus_trans h1 h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 5, 0, 0, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, k⟩ ↦ ⟨k + a + 2, 2 * k + 3, 0, 0, 0⟩) ⟨0, 1⟩
  intro ⟨a, k⟩; exact ⟨⟨4 * k + a + 6, 9 * k + 19⟩, main_trans a k⟩

end Sz22_2003_unofficial_1566

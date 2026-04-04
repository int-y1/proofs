import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1605: [77/15, 14/3, 9/22, 5/49, 33/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  1  0
-1  2  0  0 -1
 0  0  1 -2  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1605

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c d, ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

theorem climb : ∀ k, ∀ a d, ⟨a + 1, 0, 0, d, k + 1⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; step fm; finish
  rw [show (k + 1) + 1 = k + 1 + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 1) (d + 2))
  ring_nf; finish

theorem drain_even : ∀ k, ∀ a d e, ⟨a + k, 0, 2 * k, d, e + 1⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show (2 * k + 1) + 1 = (2 * k) + 1 + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (d + 2) (e + 1))
  ring_nf; finish

theorem drain_odd : ∀ k, ∀ a d e, ⟨a + k + 1, 0, 2 * k + 1, d, e + 1⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 2 * k + 2, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · rw [show a + 0 + 1 = a + 1 from by ring, show 2 * 0 + 1 = 0 + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish
  rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring]
  step fm
  rw [show (2 * k + 2) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm
  rw [show (2 * k + 1) + 1 = (2 * k) + 1 + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (d + 2) (e + 1))
  ring_nf; finish

-- Case n ≡ 1 mod 4: n = 4i+1
-- (4i+2, 0, 0, 12i+3, 0) ⊢⁺ (4i+3, 0, 0, 12i+6, 0)
theorem trans1 (i : ℕ) :
    ⟨4 * i + 2, 0, 0, 12 * i + 3, 0⟩ [fm]⊢⁺ ⟨4 * i + 3, 0, 0, 12 * i + 6, 0⟩ := by
  -- Build ⊢* then upgrade. First step is R4.
  apply step_stepStar_stepPlus
  · -- First step: R4 on (4i+2, 0, 0, (12i+1)+2, 0) -> (4i+2, 0, 1, 12i+1, 0)
    rw [show 12 * i + 3 = (12 * i + 1) + 2 from by ring]
    show fm ⟨4 * i + 2, 0, 0, (12 * i + 1) + 2, 0⟩ = some ⟨4 * i + 2, 0, 1, 12 * i + 1, 0⟩
    simp [fm]
  -- Now ⊢*: (4i+2, 0, 1, 12i+1, 0) ⊢* (4i+3, 0, 0, 12i+6, 0)
  -- R4 chain: 12i+1 = 1 + 2*6i
  apply stepStar_trans (c₂ := ⟨4 * i + 2, 0, 6 * i + 1, 1, 0⟩)
  · rw [show 12 * i + 1 = 1 + 2 * (6 * i) from by ring,
        show 6 * i + 1 = 1 + 6 * i from by ring]
    exact r4_chain (6 * i) (4 * i + 2) 1 1
  -- R5+R1: ((4i+1)+1, 0, (6i)+1, 1, 0) -> (4i+1, 0, 6i, 2, 2)
  apply stepStar_trans (c₂ := ⟨4 * i + 1, 0, 6 * i, 2, 2⟩)
  · rw [show 4 * i + 2 = (4 * i + 1) + 1 from by ring,
        show 6 * i + 1 = (6 * i) + 1 from by ring]
    step fm; step fm; finish
  -- drain_even(3i, i+1, 2, 1)
  apply stepStar_trans (c₂ := ⟨i + 1, 0, 0, 2 + 2 * (3 * i), 1 + 3 * i + 1⟩)
  · rw [show 4 * i + 1 = (i + 1) + 3 * i from by ring,
        show 6 * i = 2 * (3 * i) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact drain_even (3 * i) (i + 1) 2 1
  -- climb(3i+1, i, ...)
  rw [show i + 1 = i + 1 from rfl,
      show 1 + 3 * i + 1 = (3 * i + 1) + 1 from by ring]
  apply stepStar_trans (climb (3 * i + 1) i (2 + 2 * (3 * i)))
  ring_nf; finish

-- Case n ≡ 3 mod 4: n = 4i+3
-- (4i+4, 0, 0, 12i+9, 0) ⊢⁺ (4i+5, 0, 0, 12i+12, 0)
theorem trans3 (i : ℕ) :
    ⟨4 * i + 4, 0, 0, 12 * i + 9, 0⟩ [fm]⊢⁺ ⟨4 * i + 5, 0, 0, 12 * i + 12, 0⟩ := by
  apply step_stepStar_stepPlus
  · rw [show 12 * i + 9 = (12 * i + 7) + 2 from by ring]
    show fm ⟨4 * i + 4, 0, 0, (12 * i + 7) + 2, 0⟩ = some ⟨4 * i + 4, 0, 1, 12 * i + 7, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * i + 4, 0, 6 * i + 4, 1, 0⟩)
  · rw [show 12 * i + 7 = 1 + 2 * (6 * i + 3) from by ring,
        show 6 * i + 4 = 1 + (6 * i + 3) from by ring]
    exact r4_chain (6 * i + 3) (4 * i + 4) 1 1
  apply stepStar_trans (c₂ := ⟨4 * i + 3, 0, 6 * i + 3, 2, 2⟩)
  · rw [show 4 * i + 4 = (4 * i + 3) + 1 from by ring,
        show 6 * i + 4 = (6 * i + 3) + 1 from by ring]
    step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨i + 2, 0, 0, 2 + 2 * (3 * i + 1) + 2, 1 + (3 * i + 1) + 1⟩)
  · rw [show 4 * i + 3 = (i + 1) + (3 * i + 1) + 1 from by ring,
        show 6 * i + 3 = 2 * (3 * i + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact drain_odd (3 * i + 1) (i + 1) 2 1
  rw [show i + 2 = (i + 1) + 1 from by ring,
      show 1 + (3 * i + 1) + 1 = (3 * i + 2) + 1 from by ring]
  apply stepStar_trans (climb (3 * i + 2) (i + 1) (2 + 2 * (3 * i + 1) + 2))
  ring_nf; finish

-- Case n ≡ 2 mod 4: n = 4i+2
-- (4i+3, 0, 0, 12i+6, 0) ⊢⁺ (4i+4, 0, 0, 12i+9, 0)
theorem trans2 (i : ℕ) :
    ⟨4 * i + 3, 0, 0, 12 * i + 6, 0⟩ [fm]⊢⁺ ⟨4 * i + 4, 0, 0, 12 * i + 9, 0⟩ := by
  apply step_stepStar_stepPlus
  · rw [show 12 * i + 6 = (12 * i + 4) + 2 from by ring]
    show fm ⟨4 * i + 3, 0, 0, (12 * i + 4) + 2, 0⟩ = some ⟨4 * i + 3, 0, 1, 12 * i + 4, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * i + 3, 0, 6 * i + 3, 0, 0⟩)
  · rw [show 12 * i + 4 = 0 + 2 * (6 * i + 2) from by ring,
        show 6 * i + 3 = 1 + (6 * i + 2) from by ring]
    exact r4_chain (6 * i + 2) (4 * i + 3) 1 0
  apply stepStar_trans (c₂ := ⟨4 * i + 2, 0, 6 * i + 2, 1, 2⟩)
  · rw [show 4 * i + 3 = (4 * i + 2) + 1 from by ring,
        show 6 * i + 3 = (6 * i + 2) + 1 from by ring]
    step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨i + 1, 0, 0, 1 + 2 * (3 * i + 1), 1 + (3 * i + 1) + 1⟩)
  · rw [show 4 * i + 2 = (i + 1) + (3 * i + 1) from by ring,
        show 6 * i + 2 = 2 * (3 * i + 1) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact drain_even (3 * i + 1) (i + 1) 1 1
  rw [show 1 + (3 * i + 1) + 1 = (3 * i + 2) + 1 from by ring]
  apply stepStar_trans (climb (3 * i + 2) i (1 + 2 * (3 * i + 1)))
  ring_nf; finish

-- Case n ≡ 0 mod 4: n = 4(i+1)
-- (4i+5, 0, 0, 12i+12, 0) ⊢⁺ (4i+6, 0, 0, 12i+15, 0)
theorem trans0 (i : ℕ) :
    ⟨4 * i + 5, 0, 0, 12 * i + 12, 0⟩ [fm]⊢⁺ ⟨4 * i + 6, 0, 0, 12 * i + 15, 0⟩ := by
  apply step_stepStar_stepPlus
  · rw [show 12 * i + 12 = (12 * i + 10) + 2 from by ring]
    show fm ⟨4 * i + 5, 0, 0, (12 * i + 10) + 2, 0⟩ = some ⟨4 * i + 5, 0, 1, 12 * i + 10, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * i + 5, 0, 6 * i + 6, 0, 0⟩)
  · rw [show 12 * i + 10 = 0 + 2 * (6 * i + 5) from by ring,
        show 6 * i + 6 = 1 + (6 * i + 5) from by ring]
    exact r4_chain (6 * i + 5) (4 * i + 5) 1 0
  apply stepStar_trans (c₂ := ⟨4 * i + 4, 0, 6 * i + 5, 1, 2⟩)
  · rw [show 4 * i + 5 = (4 * i + 4) + 1 from by ring,
        show 6 * i + 6 = (6 * i + 5) + 1 from by ring]
    step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨i + 2, 0, 0, 1 + 2 * (3 * i + 2) + 2, 1 + (3 * i + 2) + 1⟩)
  · rw [show 4 * i + 4 = (i + 1) + (3 * i + 2) + 1 from by ring,
        show 6 * i + 5 = 2 * (3 * i + 2) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact drain_odd (3 * i + 2) (i + 1) 1 1
  rw [show i + 2 = (i + 1) + 1 from by ring,
      show 1 + (3 * i + 2) + 1 = (3 * i + 3) + 1 from by ring]
  apply stepStar_trans (climb (3 * i + 3) (i + 1) (1 + 2 * (3 * i + 2) + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fun q ↦ ∃ i, q = ⟨4 * i + 2, 0, 0, 12 * i + 3, 0⟩ ∨
                                         q = ⟨4 * i + 3, 0, 0, 12 * i + 6, 0⟩ ∨
                                         q = ⟨4 * i + 4, 0, 0, 12 * i + 9, 0⟩ ∨
                                         q = ⟨4 * i + 5, 0, 0, 12 * i + 12, 0⟩)
  · intro q ⟨i, hq⟩
    rcases hq with hq | hq | hq | hq
    · exact ⟨_, ⟨i, Or.inr (Or.inl rfl)⟩, hq ▸ trans1 i⟩
    · exact ⟨_, ⟨i, Or.inr (Or.inr (Or.inl rfl))⟩, hq ▸ trans2 i⟩
    · exact ⟨_, ⟨i, Or.inr (Or.inr (Or.inr rfl))⟩, hq ▸ trans3 i⟩
    · refine ⟨_, ⟨i + 1, Or.inl ?_⟩, hq ▸ trans0 i⟩
      change (4 * i + 6, 0, 0, 12 * i + 15, 0) = (4 * (i + 1) + 2, 0, 0, 12 * (i + 1) + 3, 0)
      ring_nf
  · exact ⟨0, Or.inl rfl⟩

end Sz22_2003_unofficial_1605

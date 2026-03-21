import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #5: [1/15, 98/3, 9/77, 5/7, 847/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  2  0 -1 -1
 0  0  1 -1  0
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_5

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R4 repeated: d → c
theorem d_to_c : ∀ k c, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- Drain rounds: a, c → e
theorem drain_round : ∀ k, ∀ a c e, ⟨a + k, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm
  step fm
  rw [show c + 2 * k + 2 = (c + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a c (e + 1))
  ring_nf; finish

-- R3/R2/R2 chain
theorem r3r2r2_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d + 1, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 1 + 3 * k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show d + 4 = (d + 3) + 1 from by ring,
      show a + 1 + 1 = a + 2 from by ring]
  apply stepStar_trans (h (a + 2) (d + 3) e)
  ring_nf; finish

-- Even case: d = 2m
theorem trans_even (a m : ℕ) (h_a : a ≥ m + 1) :
    ⟨a, 0, 0, 2 * m, 0⟩ [fm]⊢⁺ ⟨a + m + 3, 0, 0, 3 * m + 7, 0⟩ := by
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le h_a
  -- Phase 1: d → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨m + 1 + A, 0, 2 * m, 0, 0⟩)
  · have h := d_to_c (a := m + 1 + A) (d := 0) (2 * m) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: drain rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1 + A, 0, 0, 0, m⟩)
  · have h := drain_round m (1 + A) 0 0
    rw [show 1 + A + m = m + 1 + A from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5
  apply step_stepStar_stepPlus (c₂ := ⟨A, 0, 0, 1, m + 2⟩)
  · rw [show 1 + A = A + 1 from by ring]
    show fm ⟨A + 1, 0, 0, 0, m⟩ = some ⟨A, 0, 0, 1, m + 2⟩
    simp [fm]
  -- Phase 4: R3/R2/R2 chain
  have h := r3r2r2_chain (m + 2) A 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Odd case: d = 2m+1
theorem trans_odd (a m : ℕ) (h_a : a ≥ m + 1) :
    ⟨a, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨a + m + 2, 0, 0, 3 * m + 5, 0⟩ := by
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le h_a
  -- Phase 1: d → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨m + 1 + A, 0, 2 * m + 1, 0, 0⟩)
  · have h := d_to_c (a := m + 1 + A) (d := 0) (2 * m + 1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: drain rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1 + A, 0, 1, 0, m⟩)
  · have h := drain_round m (1 + A) 1 0
    rw [show 1 + A + m = m + 1 + A from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5
  apply step_stepStar_stepPlus (c₂ := ⟨A, 0, 1, 1, m + 2⟩)
  · rw [show 1 + A = A + 1 from by ring]
    show fm ⟨A + 1, 0, 1, 0, m⟩ = some ⟨A, 0, 1, 1, m + 2⟩
    simp [fm]
  -- R3 → R1 → R2
  apply stepStar_trans (c₂ := ⟨A, 2, 1, 0, m + 1⟩)
  · have : fm ⟨A, 0, 1, 0 + 1, (m + 1) + 1⟩ = some ⟨A, 0 + 2, 1, 0, m + 1⟩ := by simp [fm]
    rw [show 0 + 1 = 1 from rfl, show (m + 1) + 1 = m + 2 from by ring,
        show 0 + 2 = 2 from rfl] at this
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨A, 1, 0, 0, m + 1⟩)
  · have : fm ⟨A, 1 + 1, 0 + 1, 0, m + 1⟩ = some ⟨A, 1, 0, 0, m + 1⟩ := by simp [fm]
    rw [show 1 + 1 = 2 from rfl, show 0 + 1 = 1 from rfl] at this
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨A + 1, 0, 0, 2, m + 1⟩)
  · have : fm ⟨A, 0 + 1, 0, 0, m + 1⟩ = some ⟨A + 1, 0, 0, 0 + 2, m + 1⟩ := by simp [fm]
    rw [show 0 + 1 = 1 from rfl, show 0 + 2 = 2 from rfl] at this
    exact step_stepStar this
  -- Phase 4: R3/R2/R2 chain
  have h := r3r2r2_chain (m + 1) (A + 1) 1 0
  simp only [Nat.zero_add] at h
  rw [show 1 + 1 = 2 from rfl] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a ≥ d + 1 ∧ d ≥ 1)
  · intro c ⟨a, d, hq, h_inv, h_d⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      have h_a : a ≥ m + 1 := by omega
      refine ⟨⟨a + m + 3, 0, 0, 3 * m + 7, 0⟩, ⟨a + m + 3, 3 * m + 7, rfl, ?_, ?_⟩, trans_even a m h_a⟩
      · omega
      · omega
    · subst hm
      have h_a : a ≥ m + 1 := by omega
      refine ⟨⟨a + m + 2, 0, 0, 3 * m + 5, 0⟩, ⟨a + m + 2, 3 * m + 5, rfl, ?_, ?_⟩, trans_odd a m h_a⟩
      · omega
      · omega
  · exact ⟨4, 7, rfl, by omega, by omega⟩

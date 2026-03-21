import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #104: [7/15, 3/77, 50/7, 11/5, 147/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1  0  2 -1  0
 0  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_104

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R4 chain: c → e
theorem c_to_e : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3 chain: d → a + c
theorem r3_chain : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5R2R2 chain
theorem r5r2r2_chain : ∀ k, ∀ a b e, ⟨a + k, b, 0, 0, e + 2 * k⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Odd e tail
theorem odd_tail : ∀ a b, ⟨a + 1, b, 0, 0, 1⟩ [fm]⊢* ⟨a + 1, b, 0, 2, 0⟩ := by
  intro a b
  step fm; step fm; step fm; step fm; step fm; finish

-- R3R1R1 chain
theorem r3r1r1_chain : ∀ k, ∀ A B D,
    ⟨A, B + 2 * k, 0, D + 1, 0⟩ [fm]⊢* ⟨A + k, B, 0, D + 1 + k, 0⟩ := by
  intro k; induction k with
  | zero => intro A B D; exists 0
  | succ k ih =>
    intro A B D
    rw [show B + 2 * (k + 1) = (B + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show D + 2 = (D + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Odd b tail
theorem odd_b_tail : ∀ A D, ⟨A, 1, 0, D + 1, 0⟩ [fm]⊢* ⟨A + 1, 0, 1, D + 1, 0⟩ := by
  intro A D
  step fm
  step fm
  finish

-- Middle phase for even B
theorem phase_middle_even : ∀ k, ∀ A,
    ⟨A, 2 * k, 0, 2, 0⟩ [fm]⊢* ⟨A + 2 * k + 2, 0, 2 * k + 4, 0, 0⟩ := by
  intro k A
  apply stepStar_trans (c₂ := ⟨A + k, 0, 0, 2 + k, 0⟩)
  · have h := r3r1r1_chain k A 0 1
    rw [show 0 + 2 * k = 2 * k from by ring,
        show 1 + 1 = 2 from rfl,
        show 1 + 1 + k = 2 + k from by ring] at h
    exact h
  · have h := r3_chain (2 + k) (A + k) 0
    rw [show 0 + 2 * (2 + k) = 2 * k + 4 from by ring,
        show A + k + (2 + k) = A + 2 * k + 2 from by ring] at h
    exact h

-- Middle phase for odd B
theorem phase_middle_odd : ∀ k, ∀ A,
    ⟨A, 2 * k + 1, 0, 2, 0⟩ [fm]⊢* ⟨A + 2 * k + 3, 0, 2 * k + 5, 0, 0⟩ := by
  intro k A
  apply stepStar_trans (c₂ := ⟨A + k, 1, 0, 2 + k, 0⟩)
  · have h := r3r1r1_chain k A 1 1
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show 1 + 1 = 2 from rfl,
        show 1 + 1 + k = 2 + k from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨A + k + 1, 0, 1, 2 + k, 0⟩)
  · have h := odd_b_tail (A + k) (1 + k)
    rw [show 1 + k + 1 = 2 + k from by ring] at h
    exact h
  · have h := r3_chain (2 + k) (A + k + 1) 1
    rw [show 1 + 2 * (2 + k) = 2 * k + 5 from by ring,
        show A + k + 1 + (2 + k) = A + 2 * k + 3 from by ring] at h
    exact h

-- Combined middle phase
theorem phase_middle : ∀ B, ∀ A,
    ⟨A, B, 0, 2, 0⟩ [fm]⊢* ⟨A + B + 2, 0, B + 4, 0, 0⟩ := by
  intro B A
  rcases Nat.even_or_odd B with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    have h := phase_middle_even k A
    ring_nf at h ⊢; exact h
  · subst hk
    have h := phase_middle_odd k A
    ring_nf at h ⊢; exact h

-- Even e transition
theorem trans_even : ∀ K, ∀ a,
    ⟨a + K + 2, 0, 0, 0, 2 * K + 2⟩ [fm]⊢⁺ ⟨a + 3 * K + 6, 0, 0, 0, 3 * K + 8⟩ := by
  intro K a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 3 * K + 3, 0, 0, 0⟩)
  · have h := r5r2r2_chain (K + 1) (a + 1) 0 0
    rw [show a + 1 + (K + 1) = a + K + 2 from by ring,
        show 0 + 2 * (K + 1) = 2 * K + 2 from by ring,
        show 0 + 3 * (K + 1) = 3 * K + 3 from by ring] at h
    exact h
  apply step_stepStar_stepPlus
  · show fm ⟨(a) + 1, 3 * K + 3, 0, 0, 0⟩ = some ⟨a, 3 * K + 3 + 1, 0, 2, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨a + 3 * K + 6, 0, 3 * K + 8, 0, 0⟩)
  · have h := phase_middle (3 * K + 4) a
    rw [show a + (3 * K + 4) + 2 = a + 3 * K + 6 from by ring,
        show 3 * K + 4 + 4 = 3 * K + 8 from by ring,
        show 3 * K + 3 + 1 = 3 * K + 4 from by ring] at h
    exact h
  · have h := c_to_e (3 * K + 8) (a + 3 * K + 6) 0
    rw [show 0 + (3 * K + 8) = 3 * K + 8 from by ring] at h
    exact h

-- Odd e transition
theorem trans_odd : ∀ K, ∀ a,
    ⟨a + K + 1, 0, 0, 0, 2 * K + 1⟩ [fm]⊢⁺ ⟨a + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩ := by
  intro K a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 3 * K, 0, 0, 1⟩)
  · have h := r5r2r2_chain K (a + 1) 0 1
    rw [show a + 1 + K = a + K + 1 from by ring,
        show 1 + 2 * K = 2 * K + 1 from by ring,
        show 0 + 3 * K = 3 * K from by ring] at h
    exact h
  apply step_stepStar_stepPlus
  · show fm ⟨(a) + 1, 3 * K, 0, 0, 1⟩ = some ⟨a, 3 * K + 1, 0, 2, 1⟩
    simp [fm]
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a, 3 * K + 1, 0, (1) + 1, (0) + 1⟩ = some ⟨a, 3 * K + 1 + 1, 0, 1, 0⟩ by simp [fm])
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a, 3 * K + 2, 0, (0) + 1, 0⟩ = some ⟨a + 1, 3 * K + 2, 2, 0, 0⟩ by simp [fm])
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a + 1, (3 * K + 1) + 1, (1) + 1, 0, 0⟩ = some ⟨a + 1, 3 * K + 1, 1, 1, 0⟩ by simp [fm])
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a + 1, (3 * K) + 1, (0) + 1, 1, 0⟩ = some ⟨a + 1, 3 * K, 0, 2, 0⟩ by simp [fm])
  apply stepStar_trans (c₂ := ⟨a + 3 * K + 3, 0, 3 * K + 4, 0, 0⟩)
  · have h := phase_middle (3 * K) (a + 1)
    rw [show a + 1 + (3 * K) + 2 = a + 3 * K + 3 from by ring,
        show 3 * K + 4 = 3 * K + 4 from rfl] at h
    exact h
  · have h := c_to_e (3 * K + 4) (a + 3 * K + 3) 0
    rw [show 0 + (3 * K + 4) = 3 * K + 4 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ a ≥ e / 2 + 1)
  · intro c ⟨a, e, hq, he_ge, ha_ge⟩
    subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK
      have hK_pos : K ≥ 1 := by omega
      obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le hK_pos
      subst hK
      have ha_bound : a ≥ K' + 2 := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ha_bound
      refine ⟨⟨n + 3 * K' + 6, 0, 0, 0, 3 * K' + 8⟩, ⟨n + 3 * K' + 6, 3 * K' + 8, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_even K' n
      convert h using 2; ring_nf
    · subst hK
      have ha_bound : a ≥ K + 1 := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ha_bound
      refine ⟨⟨n + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩, ⟨n + 3 * K + 3, 3 * K + 4, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_odd K n
      convert h using 2; ring_nf
  · exact ⟨3, 5, rfl, by omega, by omega⟩

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #152: [1/45, 25/77, 98/5, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0  2 -1 -1
 1  0 -1  2  0
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_152

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem r4_chain : ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  have many_step : ∀ k b, ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k b

theorem r3_chain_b0 : ∀ k, ∀ a c d, ⟨a, 0, c+k, d, 0⟩ [fm]⊢* ⟨a+k, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

theorem r3_chain_b1 : ∀ k, ∀ a c d, ⟨a, 1, c+k, d, 0⟩ [fm]⊢* ⟨a+k, 1, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

theorem drain_b0 : ∀ k, ∀ a e, ⟨a+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [← Nat.add_assoc, show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

theorem drain_b1 : ∀ k, ∀ a e, ⟨a+k, 1+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [← Nat.add_assoc, show 1 + 2 * (k + 1) = (1 + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

theorem start_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+1, 0, 0, 2, e+1⟩ := by
  step fm; step fm; finish

theorem start_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a+1, 1, 0, 2, e+1⟩ := by
  step fm; step fm; finish

theorem expansion_b0 : ∀ E, ∀ A C, ⟨A, 0, C, 2, E⟩ [fm]⊢* ⟨A+2*E+C, 0, 0, 3*E+2*C+2, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A C
  rcases E with _ | _ | E'
  · convert r3_chain_b0 C A 0 2 using 2 ; ring_nf
  · step fm
    have h := r3_chain_b0 (C + 2) A 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · step fm; step fm; step fm
    refine stepStar_trans (ih E' (by omega) (A + 1) (C + 3)) ?_; ring_nf; finish

theorem expansion_b1 : ∀ E, ∀ A C, ⟨A, 1, C, 2, E⟩ [fm]⊢* ⟨A+2*E+C, 1, 0, 3*E+2*C+2, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A C
  rcases E with _ | _ | E'
  · convert r3_chain_b1 C A 0 2 using 2 ; ring_nf
  · step fm
    have h := r3_chain_b1 (C + 2) A 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · step fm; step fm; step fm
    refine stepStar_trans (ih E' (by omega) (A + 1) (C + 3)) ?_; ring_nf; finish

-- (m+k+2, 0, 0, 2*(k+1), 0) →⁺ (m+2k+5, 0, 0, 3k+8, 0)
theorem trans_A_even : ⟨m+k+2, 0, 0, 2*(k+1), 0⟩ [fm]⊢⁺ ⟨m+2*k+5, 0, 0, 3*k+8, 0⟩ := by
  rw [show 2*(k+1) = 0 + 2*(k+1) from by ring]
  apply stepStar_stepPlus_stepPlus r4_chain
  rw [show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring,
      show m + k + 2 = (m + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_b0 (k+1) (m+1) 0)
  rw [show 0 + (k + 1) = k + 1 from by ring]
  apply stepPlus_stepStar_stepPlus start_b0
  rw [show k + 1 + 1 = k + 2 from by ring]
  have h := expansion_b0 (k+2) (m+1) 0
  refine stepStar_trans ?_ (by exists 0)
  convert h using 2 ; ring_nf

-- (m+k+3, 0, 0, 2*k+3, 0) →⁺ (m+2k+6, 1, 0, 3k+8, 0)
theorem trans_A_odd : ⟨m+k+3, 0, 0, 2*k+3, 0⟩ [fm]⊢⁺ ⟨m+2*k+6, 1, 0, 3*k+8, 0⟩ := by
  rw [show 2*k+3 = 0 + (2*k+3) from by ring]
  apply stepStar_stepPlus_stepPlus r4_chain
  rw [show 0 + (2 * k + 3) = 1 + 2 * (k + 1) from by ring,
      show m + k + 3 = (m + 2) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_b1 (k+1) (m+2) 0)
  rw [show 0 + (k + 1) = k + 1 from by ring]
  apply stepPlus_stepStar_stepPlus start_b1
  rw [show k + 1 + 1 = k + 2 from by ring]
  have h := expansion_b1 (k+2) (m+2) 0
  refine stepStar_trans ?_ (by exists 0)
  convert h using 2 ; ring_nf

-- (m+K+2, 1, 0, 2*K, 0) →⁺ (m+2K+4, 1, 0, 3K+5, 0)
theorem trans_B_even : ⟨m+K+2, 1, 0, 2*K, 0⟩ [fm]⊢⁺ ⟨m+2*K+4, 1, 0, 3*K+5, 0⟩ := by
  rw [show 2*K = 0 + 2*K from by ring]
  apply stepStar_stepPlus_stepPlus r4_chain
  rw [show 1 + 2 * K = 1 + 2 * K from rfl,
      show 0 + 2 * K = 2 * K from by ring,
      show m + K + 2 = (m + 2) + K from by ring]
  apply stepStar_stepPlus_stepPlus (drain_b1 K (m+2) 0)
  rw [show 0 + K = K from by ring]
  apply stepPlus_stepStar_stepPlus start_b1
  have h := expansion_b1 (K+1) (m+2) 0
  refine stepStar_trans ?_ (by exists 0)
  convert h using 2 ; ring_nf

-- (m+K+2, 1, 0, 2*K+1, 0) →⁺ (m+2K+5, 0, 0, 3K+8, 0)
theorem trans_B_odd : ⟨m+K+2, 1, 0, 2*K+1, 0⟩ [fm]⊢⁺ ⟨m+2*K+5, 0, 0, 3*K+8, 0⟩ := by
  rw [show 2*K+1 = 0 + (2*K+1) from by ring]
  apply stepStar_stepPlus_stepPlus r4_chain
  show ⟨m + K + 2, 1 + (2 * K + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨m + 2 * K + 5, 0, 0, 3 * K + 8, 0⟩
  rw [show 1 + (2 * K + 1) = 2 * (K + 1) from by ring,
      show m + K + 2 = (m + 1) + (K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_b0 (K+1) (m+1) 0)
  rw [show 0 + (K + 1) = K + 1 from by ring]
  apply stepPlus_stepStar_stepPlus start_b0
  rw [show K + 1 + 1 = K + 2 from by ring]
  have h := expansion_b0 (K+2) (m+1) 0
  refine stepStar_trans ?_ (by exists 0)
  convert h using 2 ; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 1, 0, 11, 0⟩)
  · execute fm 25
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦
      (∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 2 ∧ 2 * a ≥ d + 2) ∨
      (∃ a d, q = ⟨a, 1, 0, d, 0⟩ ∧ d ≥ 5 ∧ 2 * a ≥ d + 3))
  · intro c hP
    rcases hP with ⟨a, d, hq, hd, ha⟩ | ⟨a, d, hq, hd, ha⟩
    · -- Type A: (a, 0, 0, d, 0)
      subst hq
      rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
      · -- d even: d = 2K, K >= 1
        rw [show K + K = 2 * K from by ring] at hK; subst hK
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
        obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
        exact ⟨_, Or.inl ⟨_, _, rfl, by omega, by omega⟩, trans_A_even⟩
      · -- d odd: d = 2K+1, K >= 1
        subst hK
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
        obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 3 := ⟨a - k - 3, by omega⟩
        refine ⟨⟨m+2*k+6, 1, 0, 3*k+8, 0⟩, Or.inr ⟨m+2*k+6, 3*k+8, rfl, by omega, by omega⟩, ?_⟩
        show ⟨m + k + 3, 0, 0, 2 * (k + 1) + 1, 0⟩ [fm]⊢⁺ ⟨m + 2 * k + 6, 1, 0, 3 * k + 8, 0⟩
        rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
        exact trans_A_odd
    · -- Type B: (a, 1, 0, d, 0)
      subst hq
      rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
      · -- d even: d = 2K, K >= 3
        rw [show K + K = 2 * K from by ring] at hK; subst hK
        obtain ⟨m, rfl⟩ : ∃ m, a = m + K + 2 := ⟨a - K - 2, by omega⟩
        exact ⟨_, Or.inr ⟨_, _, rfl, by omega, by omega⟩, trans_B_even⟩
      · -- d odd: d = 2K+1, K >= 2
        subst hK
        obtain ⟨m, rfl⟩ : ∃ m, a = m + K + 2 := ⟨a - K - 2, by omega⟩
        exact ⟨_, Or.inl ⟨_, _, rfl, by omega, by omega⟩, trans_B_odd⟩
  · exact Or.inr ⟨7, 11, rfl, by omega, by omega⟩

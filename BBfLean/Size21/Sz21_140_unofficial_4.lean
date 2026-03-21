import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #4: [1/15, 98/3, 9/77, 5/49, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  2  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_4

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3R2R2 chain consuming e
theorem r3r2r2_chain : ∀ k, ∀ A D, ⟨A, 0, 0, D+1, k⟩ [fm]⊢* ⟨A+2*k, 0, 0, D+3*k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (ih (A+2) (D+3))
  ring_nf; finish

-- R4 chain for even d
theorem r4_chain : ∀ k, ∀ A C, ⟨A, 0, C, 2*k, 0⟩ [fm]⊢* ⟨A, 0, C+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm
  apply stepStar_trans (ih A (C+1))
  ring_nf; finish

-- R4 chain for odd d
theorem r4_chain_odd : ∀ k, ∀ A C, ⟨A, 0, C, 2*k+3, 0⟩ [fm]⊢* ⟨A, 0, C+k+1, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · step fm; finish
  rw [show 2 * (k + 1) + 3 = 2 * k + 3 + 2 from by ring]
  step fm
  apply stepStar_trans (ih A (C+1))
  ring_nf; finish

-- R5R1 drain
theorem r5r1_drain : ∀ C, ∀ A E, ⟨A+C, 0, C, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E+C⟩ := by
  intro C; induction' C with C ih <;> intro A E
  · exists 0
  rw [show A + (C + 1) = (A + C) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih A (E+1))
  ring_nf; finish

-- Cleanup when d=1
theorem cleanup_d1 : ⟨A+1, 0, C+3, 1, 0⟩ [fm]⊢* ⟨A, 0, C, 0, 0⟩ := by
  execute fm 5

-- Main transition for odd e
theorem main_trans_odd (k : ℕ) (a : ℕ) (ha : a ≥ 2) :
    ⟨a, 0, 0, 0, 2*k+1⟩ [fm]⊢⁺ ⟨a+k, 0, 0, 0, 3*k+4⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  apply step_stepStar_stepPlus
  · show fm ⟨(a'+1)+1, 0, 0, 0, 2*k+1⟩ = some ⟨a'+1, 1, 0, 0, 2*k+2⟩; simp [fm]
  step fm
  step fm
  step fm
  step fm
  apply stepStar_trans (r3r2r2_chain (2*k+1) (a'+4) 4)
  apply stepStar_trans (c₂ := ⟨a'+4+2*(2*k+1), 0, 3*k+4, 0, 0⟩)
  · have h := r4_chain (3*k+4) (a'+4+2*(2*k+1)) 0
    rw [show (0 : ℕ) + (3*k+4) = 3*k+4 from by ring,
        show 2 * (3*k+4) = 4+3*(2*k+1)+1 from by ring] at h
    exact h
  have h := r5r1_drain (3*k+4) (a'+k+2) 0
  rw [show a'+k+2+(3*k+4) = a'+4+2*(2*k+1) from by ring,
      show (0 : ℕ) + (3*k+4) = 3*k+4 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition for even e
theorem main_trans_even (k : ℕ) (a : ℕ) (ha : a ≥ 2) :
    ⟨a, 0, 0, 0, 2*k+2⟩ [fm]⊢⁺ ⟨a+k+3, 0, 0, 0, 3*k+2⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  apply step_stepStar_stepPlus
  · show fm ⟨(a'+1)+1, 0, 0, 0, 2*k+2⟩ = some ⟨a'+1, 1, 0, 0, 2*k+3⟩; simp [fm]
  step fm
  step fm
  step fm
  step fm
  apply stepStar_trans (r3r2r2_chain (2*k+2) (a'+4) 4)
  apply stepStar_trans (c₂ := ⟨a'+4+2*(2*k+2), 0, 3*k+5, 1, 0⟩)
  · have h := r4_chain_odd (3*k+4) (a'+4+2*(2*k+2)) 0
    rw [show (0 : ℕ) + (3*k+4) + 1 = 3*k+5 from by ring,
        show 2*(3*k+4)+3 = 4+3*(2*k+2)+1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨a'+4+2*(2*k+2)-1, 0, 3*k+2, 0, 0⟩)
  · have h := @cleanup_d1 (a'+4+2*(2*k+2)-1) (3*k+2)
    rw [show a'+4+2*(2*k+2)-1+1 = a'+4+2*(2*k+2) from by omega,
        show (3*k+2)+3 = 3*k+5 from by ring] at h
    exact h
  have h := r5r1_drain (3*k+2) (a'+k+5) 0
  rw [show a'+k+5+(3*k+2) = a'+4+2*(2*k+2)-1 from by omega,
      show (0 : ℕ) + (3*k+2) = 3*k+2 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 2 ∧ e ≥ 1)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      have hK1 : K ≥ 1 := by omega
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨⟨a+k+3, 0, 0, 0, 3*k+2⟩, ⟨a+k+3, 3*k+2, rfl, ?_, ?_⟩, main_trans_even k a ha⟩
      · omega
      · omega
    · subst hK
      refine ⟨⟨a+K, 0, 0, 0, 3*K+4⟩, ⟨a+K, 3*K+4, rfl, ?_, ?_⟩, main_trans_odd K a ha⟩
      · omega
      · omega
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz21_140_unofficial_4

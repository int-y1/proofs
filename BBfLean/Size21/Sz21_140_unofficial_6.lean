import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #6: [1/15, 98/3, 9/77, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  2  0 -1 -1
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_6

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- Phase 1: R4 repeated: d → c (when b=0, e=0)
theorem d_to_c : ∀ k, ∀ a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R5,R1,R1 chain: each round consumes 1 from a, 2 from c, adds 1 to e
theorem r5r1r1_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c+2*k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm
  rw [show c + 2 * k + 1 = (c + 2 * k + 1) from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2b (odd case): R5,R1,R2 when c=1 remaining
theorem r5r1r2_tail : ∀ a e, ⟨a+1, 0, 1, 0, e⟩ [fm]⊢* ⟨a+1, 0, 0, 2, e+1⟩ := by
  intro a e
  step fm
  step fm
  step fm
  finish

-- Phase 3: R5,R2,R2 start
theorem r5r2r2_start : ∀ a e, ⟨a+1, 0, 0, 0, e⟩ [fm]⊢* ⟨a+2, 0, 0, 4, e+1⟩ := by
  intro a e
  step fm
  step fm
  step fm
  ring_nf; finish

-- Phase 4: R3,R2,R2 chain: each round a+=2, d+=3, e-=1
theorem r3r2r2_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d+1, e+k⟩ [fm]⊢* ⟨a+2*k, 0, 0, d+1+3*k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show d + 4 = (d + 3) + 1 from by ring]
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 4 as stepPlus: one R3,R2,R2 round then chain
theorem r3r2r2_plus : ∀ k, ∀ a d e, ⟨a, 0, 0, d+1, e+1+k⟩ [fm]⊢⁺ ⟨a+2+2*k, 0, 0, d+4+3*k, e⟩ := by
  intro k a d e
  rw [show e + 1 + k = (e + k) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨a, 0, 0, d + 1, (e + k) + 1⟩ = some ⟨a, 2, 0, d, e + k⟩; simp [fm]
  step fm
  step fm
  rw [show d + 4 = (d + 3) + 1 from by ring]
  have h := r3r2r2_chain k (a + 2) (d + 3) e
  rw [show a + 2 + 2 * k = a + 2 + 2 * k from rfl,
      show d + 3 + 1 + 3 * k = d + 4 + 3 * k from by ring] at h
  exact h

-- Main transition for even d: (a+k+1, 0, 0, 2*k, 0) ⊢⁺ (a+2*k+4, 0, 0, 3*k+7, 0)
theorem main_trans_even (a k : ℕ) :
    ⟨a+k+1, 0, 0, 2*k, 0⟩ [fm]⊢⁺ ⟨a+2*k+4, 0, 0, 3*k+7, 0⟩ := by
  -- Phase 1: d_to_c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+k+1, 0, 2*k, 0, 0⟩)
  · have h := d_to_c (2*k) (a+k+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: r5r1r1_chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, k⟩)
  · have h := r5r1r1_chain k (a+1) 0 0
    rw [show a + 1 + k = a + k + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: r5r2r2_start
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+2, 0, 0, 4, k+1⟩)
  · exact r5r2r2_start a k
  -- Phase 4: r3r2r2_plus with k rounds
  -- (a+2, 0, 0, 3+1, 0+1+k) ⊢⁺ (a+2+2+2*k, 0, 0, 3+4+3*k, 0)
  have h := r3r2r2_plus k (a+2) 3 0
  rw [show a + 2 + 2 + 2 * k = a + 2 * k + 4 from by ring,
      show 3 + 4 + 3 * k = 3 * k + 7 from by ring,
      show (0 : ℕ) + 1 + k = k + 1 from by ring,
      show (4 : ℕ) = 3 + 1 from by ring] at h
  exact h

-- Main transition for odd d: (a+k+1, 0, 0, 2*k+1, 0) ⊢⁺ (a+2*k+3, 0, 0, 3*k+5, 0)
theorem main_trans_odd (a k : ℕ) :
    ⟨a+k+1, 0, 0, 2*k+1, 0⟩ [fm]⊢⁺ ⟨a+2*k+3, 0, 0, 3*k+5, 0⟩ := by
  -- Phase 1: d_to_c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+k+1, 0, 2*k+1, 0, 0⟩)
  · have h := d_to_c (2*k+1) (a+k+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2a: r5r1r1_chain k rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 1, 0, k⟩)
  · have h := r5r1r1_chain k (a+1) 1 0
    rw [show a + 1 + k = a + k + 1 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2b: r5r1r2_tail
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 2, k+1⟩)
  · exact r5r1r2_tail a k
  -- Phase 4: r3r2r2_plus with k rounds
  -- (a+1, 0, 0, 1+1, 0+1+k) ⊢⁺ (a+1+2+2*k, 0, 0, 1+4+3*k, 0)
  have h := r3r2r2_plus k (a+1) 1 0
  rw [show a + 1 + 2 + 2 * k = a + 2 * k + 3 from by ring,
      show 1 + 4 + 3 * k = 3 * k + 5 from by ring,
      show (0 : ℕ) + 1 + k = k + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring] at h
  exact h

-- Combined main transition using parity case split
theorem main_trans (a d : ℕ) (hd : d ≥ 1) (ha : 2 * a ≥ d + 1) :
    ∃ a' d', (⟨a, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a', 0, 0, d', 0⟩) ∧ d' ≥ 1 ∧ 2 * a' ≥ d' + 1 := by
  rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- d = 2k (even)
    rw [show k + k = 2 * k from by ring] at hk; subst hk
    have hak : a ≥ k + 1 := by omega
    obtain ⟨a₀, rfl⟩ := Nat.exists_eq_add_of_le hak
    -- Now a = k + 1 + a₀
    have htrans := main_trans_even a₀ k
    rw [show a₀ + k + 1 = k + 1 + a₀ from by ring,
        show a₀ + 2 * k + 4 = k + 1 + a₀ + k + 3 from by ring] at htrans
    exact ⟨k + 1 + a₀ + k + 3, 3 * k + 7, htrans, by omega, by omega⟩
  · -- d = 2k+1 (odd)
    subst hk
    have hak : a ≥ k + 1 := by omega
    obtain ⟨a₀, rfl⟩ := Nat.exists_eq_add_of_le hak
    have htrans := main_trans_odd a₀ k
    rw [show a₀ + k + 1 = k + 1 + a₀ from by ring,
        show a₀ + 2 * k + 3 = k + 1 + a₀ + k + 2 from by ring] at htrans
    exact ⟨k + 1 + a₀ + k + 2, 3 * k + 5, htrans, by omega, by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    obtain ⟨a', d', htrans, hd', ha'⟩ := main_trans a d hd ha
    exact ⟨_, ⟨a', d', rfl, hd', ha'⟩, htrans⟩
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz21_140_unofficial_6

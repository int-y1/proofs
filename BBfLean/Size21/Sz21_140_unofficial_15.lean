import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #15: [14/15, 9/22, 125/2, 11/7, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_15

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: convert a to c (when b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2,R1,R1 chain: (a+1, 0, c+2*k, d, e+k) ->* (a+k+1, 0, c, d+2*k, e)
theorem r2r1r1_chain : ∀ k a c d e, ⟨a+1, 0, c+2*k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2: (a, 2, (c+2)+2*k, d, e+k)
  rw [show (c + 2) + 2 * k = ((c + 1) + 2 * k) + 1 from by ring]
  step fm  -- R1: (a+1, 1, (c+1)+2*k, d+1, e+k)
  rw [show (c + 1) + 2 * k = (c + 2 * k) + 1 from by ring]
  step fm  -- R1: (a+2, 0, c+2*k, d+2, e+k)
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2 repeated when c=0: (a+k, b, 0, d, e+k) ->* (a, b+2*k, 0, d, e)
theorem r2_chain : ∀ k a b d e, ⟨a+k, b, 0, d, e+k⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2: (a+k, b+2, 0, d, e+k)
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Tail cleanup: (a+1, b, 0, d, 0) ->* (0, 0, 2*b+3*(a+1), d+b, 0)
theorem tail_cleanup : ∀ b, ∀ a d, ⟨a+1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2*b+3*(a+1), d+b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | _ | _ | b
  · -- b=0: just a_to_c
    have h := a_to_c (a+1) 0 0 d
    simp only [Nat.zero_add, (by ring : 0 + 3 * (a + 1) = 3 * (a + 1))] at h
    simp only [(by omega : 2 * 0 + 3 * (a + 1) = 3 * (a + 1)),
               (by omega : d + 0 = d)]
    exact h
  · -- b=1: R3, R1, then a_to_c
    step fm; step fm
    show ⟨a+1, 0, 2, d+1, 0⟩ [fm]⊢* ⟨0, 0, 2+3*(a+1), d+1, 0⟩
    have h := a_to_c (a+1) 0 2 (d+1)
    simp only [Nat.zero_add] at h; exact h
  · -- b=2: R3, R1, R1, then a_to_c
    step fm; step fm; step fm
    show ⟨a+2, 0, 1, d+2, 0⟩ [fm]⊢* ⟨0, 0, 4+3*(a+1), d+2, 0⟩
    have h := a_to_c (a+2) 0 1 (d+2)
    simp only [Nat.zero_add, (by ring : 1 + 3 * (a + 2) = 4 + 3 * (a + 1))] at h
    exact h
  · -- b+3: R3, R1, R1, R1, then IH
    step fm; step fm; step fm; step fm
    show ⟨a+3, b, 0, d+3, 0⟩ [fm]⊢* ⟨0, 0, 2*(b+3)+3*(a+1), d+(b+3), 0⟩
    have h := ih b (by omega) (a+2) (d+3)
    simp only [(by ring : (a+2)+1 = a+3),
               (by ring : 2*b+3*((a+2)+1) = 2*(b+3)+3*(a+1)),
               (by ring : (d+3)+b = d+(b+3))] at h
    exact h

-- Main transition for odd n: n = 2*m+1
theorem main_trans_odd (m : ℕ) : ⟨0, 0, 2*m+4, 2*m+1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4*m+6, 4*m+3, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e (2*m+1) (2*m+4) 0 0
    simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  -- Now: (1, 0, 2*m+2, 1, 2*m+1)
  apply stepStar_trans (c₂ := ⟨m+2, 0, 0, 2*m+3, m⟩)
  · have h := r2r1r1_chain (m+1) 0 0 1 m
    simp only [Nat.zero_add, (by ring : 0 + 2 * (m + 1) = 2 * m + 2),
               (by ring : m + (m + 1) = 2 * m + 1),
               (by ring : 1 + 2 * (m + 1) = 2 * m + 3)] at h
    exact h
  apply stepStar_trans (c₂ := ⟨2, 2*m, 0, 2*m+3, 0⟩)
  · have h := r2_chain m 2 0 (2*m+3) 0
    simp only [Nat.zero_add, (by ring : 2 + m = m + 2)] at h; exact h
  have h := tail_cleanup (2*m) 1 (2*m+3)
  simp only [(by ring : 1 + 1 = 2),
             (by ring : 2 * (2 * m) + 3 * 2 = 4 * m + 6),
             (by ring : 2 * m + 3 + 2 * m = 4 * m + 3)] at h
  exact h

-- Main transition for even n >= 2: n = 2*(m+1)
theorem main_trans_even (m : ℕ) : ⟨0, 0, 2*m+5, 2*m+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 4*m+8, 4*m+5, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e (2*m+2) (2*m+5) 0 0
    simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  -- Now: (1, 0, 2*m+3, 1, 2*m+2)
  apply stepStar_trans (c₂ := ⟨m+2, 0, 1, 2*m+3, m+1⟩)
  · have h := r2r1r1_chain (m+1) 0 1 1 (m+1)
    simp only [Nat.zero_add, (by ring : 1 + 2 * (m + 1) = 2 * m + 3),
               (by ring : m + 1 + (m + 1) = 2 * m + 2)] at h
    exact h
  -- Phase 4: R2, R1
  step fm; step fm
  -- Now: (m+2, 1, 0, 2*m+4, m)
  apply stepStar_trans (c₂ := ⟨2, 2*m+1, 0, 2*m+4, 0⟩)
  · have h := r2_chain m 2 1 (2*m+4) 0
    simp only [Nat.zero_add, (by ring : 2 + m = m + 2),
               (by ring : 1 + 2 * m = 2 * m + 1)] at h
    exact h
  have h := tail_cleanup (2*m+1) 1 (2*m+4)
  simp only [(by ring : 1 + 1 = 2),
             (by ring : 2 * (2 * m + 1) + 3 * 2 = 4 * m + 8),
             (by ring : 2 * m + 4 + (2 * m + 1) = 4 * m + 5)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+3, n, 0⟩) 0
  intro n
  rcases n with _ | n
  · exists 1; execute fm 3
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      exists 2*(2*m+1)+1
      show ⟨0, 0, m+m+1+3, m+m+1, 0⟩ [fm]⊢⁺ ⟨0, 0, (2*(2*m+1)+1)+3, 2*(2*m+1)+1, 0⟩
      simp only [(by ring : m + m + 1 = 2 * m + 1),
                 (by ring : 2 * (2 * m + 1) + 1 = 4 * m + 3)]
      exact main_trans_odd m
    · subst hm
      exists 2*(2*(m+1))+1
      show ⟨0, 0, 2*m+1+1+3, 2*m+1+1, 0⟩ [fm]⊢⁺ ⟨0, 0, (2*(2*(m+1))+1)+3, 2*(2*(m+1))+1, 0⟩
      simp only [(by ring : 2 * m + 1 + 1 + 3 = 2 * m + 5),
                 (by ring : 2 * m + 1 + 1 = 2 * m + 2),
                 (by ring : 2 * (2 * (m + 1)) + 1 = 4 * m + 5)]
      exact main_trans_even m

end Sz21_140_unofficial_15

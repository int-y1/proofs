import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #292: [14/15, 9/242, 25/2, 11/7, 9/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -2
-1  0  2  0  0
 0  0  0 -1  1
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_292

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+2⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R5 step lemma for when a=0, b=0, d=0
lemma r5_step (c e : ℕ) : ⟨0, 0, c+1, 0, e⟩ [fm]⊢ ⟨0, 2, c, 0, e⟩ := by
  unfold fm; simp only

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: convert a to c (when b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1,R1,R2 chain: k triples
theorem r1r1r2_chain : ∀ k a c d e, ⟨a, 2, c+2*k, d, e+2*k⟩ [fm]⊢* ⟨a+k, 2, c, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
      show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
  step fm
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2 repeated: convert a,e to b (when c=0)
theorem r2_chain : ∀ k a b d e, ⟨a+k, b, 0, d, e+2*k⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Tail cleanup: (a+1, b, 0, d, 0) ->* (0, 0, b+2*(a+1), d+b, 0)
theorem tail_cleanup : ∀ b, ∀ a d, ⟨a+1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, b+2*(a+1), d+b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | _ | b
  · -- b = 0: just a_to_c
    have h := a_to_c (a+1) 0 0 d
    simp only [Nat.zero_add, (by ring : 0 + 2 * (a + 1) = 2 * (a + 1))] at h
    simpa [(by omega : 0 + 2 * (a + 1) = 2 * (a + 1)), (by omega : d + 0 = d)] using h
  · -- b = 1: R3, R1, then a_to_c
    step fm; step fm
    show ⟨a+1, 0, 1, d+1, 0⟩ [fm]⊢* ⟨0, 0, 1+2*(a+1), d+1, 0⟩
    have h := a_to_c (a+1) 0 1 (d+1)
    simp only [Nat.zero_add] at h; exact h
  · -- b = b + 2: R3, R1, R1, then recurse
    step fm
    rw [show b + 2 = b + 1 + 1 from by ring]
    step fm; step fm
    show ⟨a+2, b, 0, d+2, 0⟩ [fm]⊢* ⟨0, 0, b+2+2*(a+1), d+(b+2), 0⟩
    have h := ih b (by omega) (a+1) (d+2)
    rw [show (a+1)+1 = a+2 from by ring,
        show b + 2 * ((a+1)+1) = b+2+2*(a+1) from by ring,
        show (d+2)+b = d+(b+2) from by ring] at h
    exact h

-- Transition for odd n: C(2m+1) ->+ C(2m+2)
theorem trans_odd (m : ℕ) :
    ⟨0, 0, 2*m+3, 4*m+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*m+4, 4*m+4, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e (4*m+2) (2*m+3) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R5 step: (0, 0, (2m+2)+1, 0, 4m+2) -> (0, 2, 2m+2, 0, 4m+2)
  apply step_stepStar_stepPlus (show ⟨0, 0, (2*m+2)+1, 0, 4*m+2⟩ [fm]⊢ ⟨0, 2, 2*m+2, 0, 4*m+2⟩ from r5_step _ _)
  show ⟨0, 2, 2*m+2, 0, 4*m+2⟩ [fm]⊢* ⟨0, 0, 2*m+4, 4*m+4, 0⟩
  apply stepStar_trans
  · have h := r1r1r2_chain (m+1) 0 0 0 (2*m)
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show 2 * m + 2 * (m + 1) = 4 * m + 2 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans
  · have h := r2_chain m 1 2 (2*(m+1)) 0
    rw [show 1 + m = m + 1 from by ring,
        show 0 + 2 * m = 2 * m from by ring] at h
    exact h
  have h := tail_cleanup (2 + 2*m) 0 (2*(m+1))
  rw [show 0 + 1 = 1 from by ring,
      show (2 + 2 * m) + 2 * (0 + 1) = 2 * m + 4 from by ring,
      show 2 * (m + 1) + (2 + 2 * m) = 4 * m + 4 from by ring] at h
  exact h

-- Transition for even n >= 2: C(2(m+1)) ->+ C(2(m+1)+1)
theorem trans_even (m : ℕ) :
    ⟨0, 0, 2*m+4, 4*m+4, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*m+5, 4*m+6, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e (4*m+4) (2*m+4) 0 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (show ⟨0, 0, (2*m+3)+1, 0, 4*m+4⟩ [fm]⊢ ⟨0, 2, 2*m+3, 0, 4*m+4⟩ from r5_step _ _)
  show ⟨0, 2, 2*m+3, 0, 4*m+4⟩ [fm]⊢* ⟨0, 0, 2*m+5, 4*m+6, 0⟩
  -- r1r1r2 with k=m+1
  apply stepStar_trans
  · have h := r1r1r2_chain (m+1) 0 1 0 (2*m+2)
    rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
        show (2 * m + 2) + 2 * (m + 1) = 4 * m + 4 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- (m+1, 2, 1, 2*(m+1), 2m+2). R1 step.
  step fm
  apply stepStar_trans
  · have h := r2_chain (m+1) 1 1 (2*m+3) 0
    rw [show 1 + (m + 1) = m + 2 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring] at h
    exact h
  have h := tail_cleanup (1 + 2*(m+1)) 0 (2*m+3)
  rw [show 0 + 1 = 1 from by ring,
      show (1 + 2 * (m + 1)) + 2 * (0 + 1) = 2 * m + 5 from by ring,
      show (2 * m + 3) + (1 + 2 * (m + 1)) = 4 * m + 6 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  refine progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = (⟨0, 0, n+2, 2*n, 0⟩ : Q)) ?_ ⟨0, rfl⟩
  intro q ⟨n, hq⟩; subst hq
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rcases m with _ | m
    · exact ⟨⟨0, 0, 3, 2, 0⟩, ⟨1, rfl⟩, by execute fm 5⟩
    · refine ⟨⟨0, 0, (m+1)+(m+1)+1+2, 2*((m+1)+(m+1)+1), 0⟩, ⟨(m+1)+(m+1)+1, rfl⟩, ?_⟩
      have h := trans_even m
      show ⟨0, 0, (m+1)+(m+1)+2, 2*((m+1)+(m+1)), 0⟩ [fm]⊢⁺
           ⟨0, 0, (m+1)+(m+1)+1+2, 2*((m+1)+(m+1)+1), 0⟩
      rw [show (m + 1) + (m + 1) + 2 = 2 * m + 4 from by omega,
          show 2 * ((m + 1) + (m + 1)) = 4 * m + 4 from by omega,
          show (m + 1) + (m + 1) + 1 + 2 = 2 * m + 5 from by omega,
          show 2 * ((m + 1) + (m + 1) + 1) = 4 * m + 6 from by omega]
      exact h
  · subst hm
    refine ⟨⟨0, 0, 2*m+2+2, 2*(2*m+2), 0⟩, ⟨2*m+2, rfl⟩, ?_⟩
    have h := trans_odd m
    show ⟨0, 0, 2*m+1+2, 2*(2*m+1), 0⟩ [fm]⊢⁺ ⟨0, 0, 2*m+2+2, 2*(2*m+2), 0⟩
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by omega,
        show 2 * (2 * m + 1) = 4 * m + 2 from by omega,
        show 2 * m + 2 + 2 = 2 * m + 4 from by omega,
        show 2 * (2 * m + 2) = 4 * m + 4 from by omega]
    exact h

end Sz22_2003_unofficial_292

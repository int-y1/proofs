import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #283: [14/15, 9/22, 125/2, 11/7, 14/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_283

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R3 repeated: convert a to c (when b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R2+R1+R1 chain: each iteration consumes 2 from c and 1 from e
theorem r2r1r1_chain : ∀ k a c d e, ⟨a+1, 0, c+2*k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  rw [show (c + 2) + 2 * k = ((c + 1) + 2 * k) + 1 from by ring]; step fm
  rw [show (c + 1) + 2 * k = (c + 2 * k) + 1 from by ring]; step fm
  apply stepStar_trans (h _ _ _ _); ring_nf; finish

-- R2 repeated when c=0: converts a to b
theorem r2_chain : ∀ k a b d e, ⟨a+k, b, 0, d, e+k⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _); ring_nf; finish

-- Tail cleanup: processes remaining a and b when c=0, e=0
theorem tail_cleanup : ∀ b, ∀ a d, ⟨a+1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2*b+3*(a+1), d+b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | _ | _ | b
  · have h := a_to_c (a+1) 0 0 d
    simp only [Nat.zero_add, (by ring : 0 + 3 * (a + 1) = 3 * (a + 1))] at h
    simp only [(by omega : 2 * 0 + 3 * (a + 1) = 3 * (a + 1)), (by omega : d + 0 = d)]
    exact h
  · step fm; step fm
    show ⟨a+1, 0, 2, d+1, 0⟩ [fm]⊢* ⟨0, 0, 2+3*(a+1), d+1, 0⟩
    have h := a_to_c (a+1) 0 2 (d+1); simp only [Nat.zero_add] at h; exact h
  · step fm; step fm; step fm
    show ⟨a+2, 0, 1, d+2, 0⟩ [fm]⊢* ⟨0, 0, 4+3*(a+1), d+2, 0⟩
    have h := a_to_c (a+2) 0 1 (d+2)
    simp only [Nat.zero_add, (by ring : 1 + 3 * (a + 2) = 4 + 3 * (a + 1))] at h; exact h
  · step fm; step fm; step fm; step fm
    show ⟨a+3, b, 0, d+3, 0⟩ [fm]⊢* ⟨0, 0, 2*(b+3)+3*(a+1), d+(b+3), 0⟩
    have h := ih b (by omega) (a+2) (d+3)
    simp only [(by ring : (a+2)+1 = a+3), (by ring : 2*b+3*((a+2)+1) = 2*(b+3)+3*(a+1)),
               (by ring : (d+3)+b = d+(b+3))] at h; exact h

-- Main transition: (0, 0, c, d, 0) ->+ (0, 0, c+d+2, 2d+1, 0) when c >= d+2.
-- The transition consists of: R4 loop, R5 step, mixing phase (R2+R1+R1 chain +
-- possibly R2 chain + tail cleanup), and R3 loop. Three sub-cases handle the
-- mixing phase depending on how c compares to 2d.
theorem main_trans (c d : ℕ) (hcd : c ≥ d + 2) :
    ⟨0, 0, c, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c+d+2, 2*d+1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e d c 0 0; simp only [Nat.zero_add] at h; exact h
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  apply step_stepStar_stepPlus (show ⟨0, 0, c'+1, 0, d⟩ [fm]⊢ ⟨1, 0, c', 1, d⟩ by unfold fm; simp)
  rcases d with _ | d
  · step fm; finish
  · rcases le_or_gt (2*(d+1)) c' with hle | hgt
    · -- CASE A: c' >= 2*(d+1), chain fully processes e
      obtain ⟨r, rfl⟩ : ∃ r, c' = r + 2*(d+1) := ⟨c' - 2*(d+1), by omega⟩
      apply stepStar_trans
      · have h := r2r1r1_chain (d+1) 0 r 1 0
        simp only [Nat.zero_add] at h; exact h
      have h := a_to_c (d+2) 0 r (2*(d+1)+1)
      simp only [Nat.zero_add] at h
      rw [show r + 3 * (d + 2) = r + 2 * (d + 1) + 1 + (d + 1) + 2 from by ring,
          show d + 2 = d + 1 + 1 from by ring] at h
      rw [show (1 : ℕ) + 2 * (d + 1) = 2 * (d + 1) + 1 from by ring]; exact h
    · -- c' < 2*(d+1), chain partially processes e, then tail cleanup
      rcases Nat.even_or_odd c' with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- CASE B: c' even (c' = j+j)
        subst hj
        obtain ⟨s, hs⟩ : ∃ s, d + 1 = j + s := ⟨d + 1 - j, by omega⟩
        obtain ⟨u, hu⟩ : ∃ u, j = u + s := ⟨j - s, by omega⟩
        apply stepStar_trans
        · have h := r2r1r1_chain (u+s) 0 0 1 s
          simp only [Nat.zero_add] at h
          rw [show s + (u + s) = u + 2 * s from by ring] at h
          rw [show u + 2 * s = s + (u + s) from by ring,
              show u + s + 1 = 0 + (u + s) + 1 from by ring] at h
          simp only [Nat.zero_add] at h
          rw [show j + j = 0 + 2 * (u + s) from by omega,
              show d + 1 = s + (u + s) from by omega]
          simp only [Nat.zero_add]; exact h
        apply stepStar_trans
        · have h := r2_chain s (u+1) 0 (1+2*(u+s)) 0
          simp only [Nat.zero_add] at h
          rw [show (u + 1) + s = u + s + 1 from by ring] at h; exact h
        have h := tail_cleanup (2*s) u (1+2*(u+s))
        rw [show 2 * (2 * s) + 3 * (u + 1) = j + j + 1 + (d + 1) + 2 from by omega,
            show 1 + 2 * (u + s) + 2 * s = 2 * (d + 1) + 1 from by omega] at h
        exact h
      · -- CASE C: c' odd (c' = 2*j+1)
        subst hj
        obtain ⟨s, hs⟩ : ∃ s, d + 1 = j + 1 + s := ⟨d - j, by omega⟩
        obtain ⟨u, hu⟩ : ∃ u, j = u + s := ⟨j - s, by omega⟩
        apply stepStar_trans
        · have h := r2r1r1_chain (u+s) 0 1 1 (s+1)
          simp only [Nat.zero_add] at h
          rw [show 1 + 2 * (u + s) = 2 * (u + s) + 1 from by ring,
              show (s + 1) + (u + s) = u + 2 * s + 1 from by ring] at h
          rw [show u + 2 * s + 1 = (s + 1) + (u + s) from by ring,
              show u + s + 1 = 0 + (u + s) + 1 from by ring] at h
          simp only [Nat.zero_add] at h
          rw [show (2 : ℕ) * j + 1 = 2 * (u + s) + 1 from by omega,
              show d + 1 = (s + 1) + (u + s) from by omega]; exact h
        apply stepStar_trans
        · show (⟨u+s+1, 0, 1, 2*(u+s)+1, s+1⟩ : Q) [fm]⊢* ⟨u+s+1, 1, 0, 2*(u+s)+2, s⟩
          rw [show 2 * (u + s) + 1 = (2 * (u + s)) + 1 from by ring]
          step fm; step fm
          rw [show 2 * (u + s) + 1 + 1 = 2 * (u + s) + 2 from by ring]; finish
        apply stepStar_trans
        · have h := r2_chain s (u+1) 1 (2*(u+s)+2) 0
          simp only [Nat.zero_add] at h
          rw [show (u + 1) + s = u + s + 1 from by ring] at h; exact h
        have h := tail_cleanup (1+2*s) u (2*(u+s)+2)
        rw [show 2 * (1 + 2 * s) + 3 * (u + 1) = 2 * j + 1 + 1 + (d + 1) + 2 from by omega,
            show 2 * (u + s) + 2 + (1 + 2 * s) = 2 * (d + 1) + 1 from by omega] at h
        exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ d + 2)
  · intro q ⟨c, d, hq, hcd⟩; subst hq
    exact ⟨⟨0, 0, c + d + 2, 2 * d + 1, 0⟩, ⟨c + d + 2, 2 * d + 1, rfl, by omega⟩,
           main_trans c d hcd⟩
  · exact ⟨3, 0, rfl, by omega⟩

end Sz22_2003_unofficial_283

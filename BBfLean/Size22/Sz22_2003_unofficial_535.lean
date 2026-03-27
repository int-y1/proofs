import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #535: [28/15, 63/22, 5/2, 11/7, 6/5]

Vector representation:
```
 2 -1 -1  1  0
-1  2  0  1 -1
-1  0  1  0  0
 0  0  0 -1  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_535

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 chain: convert a to c
theorem a_to_c : ∀ k c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih _); ring_nf; finish

-- R4 chain: convert d to e
theorem d_to_e : ∀ k e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  step fm
  apply stepStar_trans (ih _); ring_nf; finish

-- R3+R1 chain: convert b to a and d
theorem r3r1_chain : ∀ b a d, ⟨a+1, b, 0, d, 0⟩ [fm]⊢* ⟨a+b+1, 0, 0, d+b, 0⟩ := by
  intro b; induction' b with b ih <;> intro a d
  · exists 0
  rw [show a + 1 = (a + 1) + 0 from by ring]; step fm; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R2 chain: drain e via R2
theorem r2_chain : ∀ k b d, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+2*k, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R2+R1+R1 iterated chain
theorem r2r1r1_iter : ∀ k, ∀ c d e,
    ⟨a+1, 0, c+2*k, d, e+k⟩ [fm]⊢* ⟨a+3*k+1, 0, c, d+3*k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  apply stepStar_trans (ih (c + 2) d (e + 1))
  rw [show a + 3 * k + 1 = (a + 3 * k) + 1 from by ring,
      show c + 2 = c + 1 + 1 from by ring,
      show e + 1 = e + 0 + 1 from by ring]
  step fm; step fm; step fm; ring_nf; finish

-- Opening: R5+R1. From (0, 0, c+2, 0, e+1) via R5 then R1.
theorem opening : ⟨0, 0, c+2, 0, e+1⟩ [fm]⊢* ⟨3, 0, c, 1, e+1⟩ := by
  rw [show c + 2 = c + 1 + 1 from by ring,
      show e + 1 = e + 0 + 1 from by ring]
  step fm; step fm; ring_nf; finish

-- Combined opening + r2r1r1_iter for even case
theorem opening_and_iter_even :
    ⟨0, 0, 2*m+2, 0, m+E+1⟩ [fm]⊢* ⟨3*m+3, 0, 0, 3*m+1, E+1⟩ := by
  apply stepStar_trans (opening (c := 2*m) (e := m+E))
  rw [show m+E+1 = (E+1)+m from by ring,
      show 2*m = 0+2*m from by ring,
      show (3 : ℕ) = 2+1 from by ring]
  apply stepStar_trans (r2r1r1_iter m 0 1 (E+1))
  ring_nf; finish

-- Combined opening + r2r1r1_iter + partial R2+R1 for odd case
theorem opening_and_iter_odd :
    ⟨0, 0, 2*m+3, 0, m+E+2⟩ [fm]⊢* ⟨3*m+4, 1, 0, 3*m+3, E+1⟩ := by
  rw [show 2*m+3 = (2*m+1)+2 from by ring,
      show m+E+2 = (m+1+E)+1 from by ring]
  apply stepStar_trans (opening (c := 2*m+1) (e := m+1+E))
  rw [show m+1+E+1 = (E+2)+m from by ring,
      show 2*m+1 = 1+2*m from by ring,
      show (3 : ℕ) = 2+1 from by ring]
  apply stepStar_trans (r2r1r1_iter m 1 1 (E+2))
  rw [show 2+3*m+1 = (2+3*m)+1 from by ring,
      show E+2 = (E+1)+0+1 from by ring,
      show (1 : ℕ) = 0+1 from by ring]
  step fm; step fm; ring_nf; finish

-- r2_chain + r3r1_chain combined
theorem drain_and_convert (hF : A = F + 1 + K) :
    ⟨A, B, 0, D, K⟩ [fm]⊢* ⟨F+B+2*K+1, 0, 0, D+K+B+2*K, 0⟩ := by
  rw [hF]
  apply stepStar_trans (r2_chain K B D)
  rw [show F + 1 = (F+0)+1 from by ring]
  apply stepStar_trans (r3r1_chain (B+2*K) F (D+K))
  ring_nf; finish

-- Even case: a = 2*(m+1), d = m+1+E, with E <= 3*m+1
theorem even_trans (hE : E ≤ 3*m+1) :
    ⟨2*(m+1), 0, 0, m+1+E, 0⟩ [fm]⊢⁺ ⟨3*m+E+4, 0, 0, 3*m+3*E+4, 0⟩ := by
  -- First R3 step to get ⊢⁺
  rw [show 2*(m+1) = (2*m+1) + 1 from by ring]
  step fm
  -- Now ⊢*. Remaining a_to_c: (2*m+1) more R3 steps
  rw [show 2*m+1 = 0+(2*m+1) from by ring]
  apply stepStar_trans (a_to_c (2*m+1) 1)
  rw [show 1+(2*m+1) = 2*m+2 from by ring]
  apply stepStar_trans (d_to_e (m+1+E) 0)
  rw [show 0+(m+1+E) = m+E+1 from by ring]
  apply stepStar_trans opening_and_iter_even
  obtain ⟨F, hF⟩ : ∃ F, 3*m+3 = F + 1 + (E+1) := ⟨3*m+1-E, by omega⟩
  apply stepStar_trans (drain_and_convert hF)
  rw [show F+0+2*(E+1)+1 = 3*m+E+4 from by omega,
      show 3*m+1+(E+1)+0+2*(E+1) = 3*m+3*E+4 from by omega]
  finish

-- Odd case: a = 2*m+3, d = m+2+E, with E <= 3*m+2
theorem odd_trans (hE : E ≤ 3*m+2) :
    ⟨2*m+3, 0, 0, m+2+E, 0⟩ [fm]⊢⁺ ⟨3*m+E+6, 0, 0, 3*m+3*E+7, 0⟩ := by
  -- First R3 step to get ⊢⁺
  rw [show 2*m+3 = (2*m+2) + 1 from by ring]
  step fm
  -- Remaining a_to_c
  rw [show 2*m+2 = 0+(2*m+2) from by ring]
  apply stepStar_trans (a_to_c (2*m+2) 1)
  rw [show 1+(2*m+2) = 2*m+3 from by ring]
  apply stepStar_trans (d_to_e (m+2+E) 0)
  rw [show 0+(m+2+E) = m+E+2 from by ring]
  apply stepStar_trans opening_and_iter_odd
  obtain ⟨F, hF⟩ : ∃ F, 3*m+4 = F + 1 + (E+1) := ⟨3*m+2-E, by omega⟩
  apply stepStar_trans (drain_and_convert hF)
  rw [show F+1+2*(E+1)+1 = 3*m+E+6 from by omega,
      show 3*m+3+(E+1)+1+2*(E+1) = 3*m+3*E+7 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ a ≥ 2 ∧ 2*a ≥ d+2 ∧ a ≤ 2*d)
  · intro c ⟨a, d, hq, hd, ha2, had, hda⟩; subst hq
    rcases Nat.even_or_odd a with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, d = m + 1 + E := ⟨d - m - 1, by omega⟩
      refine ⟨⟨3*m+E+4, 0, 0, 3*m+3*E+4, 0⟩,
        ⟨3*m+E+4, 3*m+3*E+4, rfl, by omega, by omega, by omega, by omega⟩,
        even_trans (by omega)⟩
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, d = m + 2 + E := ⟨d - m - 2, by omega⟩
      refine ⟨⟨3*m+E+6, 0, 0, 3*m+3*E+7, 0⟩,
        ⟨3*m+E+6, 3*m+3*E+7, rfl, by omega, by omega, by omega, by omega⟩,
        odd_trans (by omega)⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega, by omega⟩

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1438: [7/15, 242/3, 3/77, 5/11, 135/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  1  0 -1 -1
 0  0  1  0 -1
-1  3  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1438

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | _ => none

-- R4 chain: convert e to c (b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- R5+R1x3 chain: each cycle a-=1, c-=2, d+=3
theorem r5_r1x3_chain : ∀ k, ∀ a c d, ⟨a + k, 0, 2 * k + c, d, 0⟩ [fm]⊢*
    ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + c = (2 * k + c) + 2 from by ring]
    step fm
    step fm
    step fm
    step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- R3+R2 interleaving: each cycle a+=1, d-=1, e+=1
theorem r3_r2_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢*
    ⟨a + k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) d (e + 1))
    ring_nf; finish

-- Even remainder: (m+1, 0, 0, d, 0) via R5+R1+R2x2 then R3/R2 chain
theorem even_remainder : ⟨m + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨m + d + 3, 0, 0, 0, d + 5⟩ := by
  step fm
  step fm
  step fm
  step fm
  rw [show m + 1 + 1 = m + 2 from by ring,
      show d + 1 = 0 + (d + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3_r2_chain (d + 1) (m + 2) 0 3)
  ring_nf; finish

-- Odd remainder: (m+1, 0, 1, d, 0) via R5+R1x2+R2 then R3/R2 chain
theorem odd_remainder : ⟨m + 1, 0, 1, d, 0⟩ [fm]⊢⁺ ⟨m + d + 3, 0, 0, 0, d + 4⟩ := by
  step fm
  step fm
  step fm
  step fm
  rw [show d + 1 + 1 = 0 + (d + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3_r2_chain (d + 2) (m + 1) 0 1)
  ring_nf; finish

-- Even full transition: from (m+K+1, 0, 0, 0, 2K) via e_to_c, r5_r1x3, even_remainder
theorem even_trans (K : ℕ) :
    ⟨m + K + 1, 0, 0, 0, 2 * K⟩ [fm]⊢⁺ ⟨m + 3 * K + 3, 0, 0, 0, 3 * K + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (0 : ℕ) = 0 from rfl,
        show 2 * K = 0 + (2 * K) from by ring]
    exact e_to_c (2 * K) (m + K + 1) 0
  apply stepStar_stepPlus_stepPlus
  · rw [show m + K + 1 = (m + 1) + K from by ring,
        show 0 + 2 * K = 2 * K + 0 from by ring]
    exact r5_r1x3_chain K (m + 1) 0 0
  show ⟨m + 1, 0, 0, 0 + 3 * K, 0⟩ [fm]⊢⁺ _
  rw [show 0 + 3 * K = 3 * K from by ring]
  exact even_remainder

-- Odd full transition: from (m+K+1, 0, 0, 0, 2K+1) via e_to_c, r5_r1x3, odd_remainder
theorem odd_trans (K : ℕ) :
    ⟨m + K + 1, 0, 0, 0, 2 * K + 1⟩ [fm]⊢⁺ ⟨m + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * K + 1 = 0 + (2 * K + 1) from by ring]
    exact e_to_c (2 * K + 1) (m + K + 1) 0
  apply stepStar_stepPlus_stepPlus
  · rw [show m + K + 1 = (m + 1) + K from by ring,
        show 0 + (2 * K + 1) = 2 * K + 1 from by ring]
    exact r5_r1x3_chain K (m + 1) 1 0
  show ⟨m + 1, 0, 1, 0 + 3 * K, 0⟩ [fm]⊢⁺ _
  rw [show 0 + 3 * K = 3 * K from by ring]
  exact odd_remainder

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩)
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 5 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- e even: e = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m', rfl⟩ : ∃ m', a = m' + K + 1 := ⟨a - K - 1, by omega⟩
      refine ⟨⟨m' + 3 * K + 3, 0, 0, 0, 3 * K + 5⟩,
        ⟨m' + 3 * K + 3, 3 * K + 5, rfl, by omega, by omega⟩, even_trans K⟩
    · -- e odd: e = 2*K + 1
      subst hK
      obtain ⟨m', rfl⟩ : ∃ m', a = m' + K + 1 := ⟨a - K - 1, by omega⟩
      refine ⟨⟨m' + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩,
        ⟨m' + 3 * K + 3, 3 * K + 4, rfl, by omega, by omega⟩, odd_trans K⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

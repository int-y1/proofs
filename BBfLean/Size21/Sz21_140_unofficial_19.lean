import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #19: [27/35, 5/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_19

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain₀ : ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a+k, 0, 0, d+k, 0⟩ := by
  have h : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a+k, 0, 0, d+k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact h k a d

theorem r4_chain : ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  have h : ∀ k e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro e
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact h k e

theorem e_consume_c0 : ⟨a+1, 0, 0, 0, e+4⟩ [fm]⊢* ⟨a, 0, 3, 0, e⟩ := by
  execute fm 6

theorem e_consume_c : ⟨a+1, 0, c+1, 0, e+4⟩ [fm]⊢* ⟨a, 0, c+4, 0, e⟩ := by
  execute fm 6

theorem e_consume_gen : ⟨a+k, 0, c+1, 0, e+4*k⟩ [fm]⊢* ⟨a, 0, c+1+3*k, 0, e⟩ := by
  have h : ∀ k a c e, ⟨a+k, 0, c+1, 0, e+4*k⟩ [fm]⊢* ⟨a, 0, c+1+3*k, 0, e⟩ := by
    intro k; induction' k with k h <;> intro a c e
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 4 * (k + 1) = (e + 4 * k) + 4 from by ring]
    apply stepStar_trans (e_consume_c (a := a+k) (c := c) (e := e+4*k))
    rw [show c + 4 = (c + 3) + 1 from by ring]
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact h k a c e

theorem e_consume : ⟨a+(k+1), 0, 0, 0, e+4*(k+1)⟩ [fm]⊢* ⟨a, 0, 3*(k+1), 0, e⟩ := by
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 4 * (k + 1) = (e + 4 * k) + 4 from by ring]
  apply stepStar_trans (e_consume_c0 (a := a+k) (e := e+4*k))
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (e_consume_gen (a := a) (k := k) (c := 2) (e := e))
  ring_nf; finish

theorem r3r1_chain : ∀ k b a, ⟨a, b+1, k, 0, 0⟩ [fm]⊢* ⟨a+k, b+1+2*k, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro b a
  · exists 0
  step fm; step fm
  apply stepStar_trans (h (b+2) (a+1))
  ring_nf; finish

theorem c_to_ab : ⟨a+1, 0, c+1, 0, 0⟩ [fm]⊢⁺ ⟨a+c, 2*c+4, 0, 0, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r3r1_chain c 3 a)
  ring_nf; finish

theorem e2_tail : ⟨a+1, 0, c+1, 0, 2⟩ [fm]⊢* ⟨a+1, 4, c+1, 0, 0⟩ := by
  execute fm 6

theorem trans_even (K : ℕ) :
    ⟨a, 4*(K+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨a+6*K+4, 6*K+8, 0, 0, 0⟩ := by
  step fm
  apply stepStar_trans (r3_chain₀ (k := 4*K+3) (a := a+1) (d := 1))
  rw [show a + 1 + (4 * K + 3) = a + 4 * (K + 1) from by ring,
      show 0 + 1 + (4 * K + 3) = 4 * (K + 1) from by ring]
  apply stepStar_trans (r4_chain (a := a + 4*(K+1)) (k := 4*(K+1)) (e := 0))
  rw [show 0 + 4 * (K + 1) = 4 * (K + 1) from by ring,
      show a + 4 * (K + 1) = (a + 3 * K + 3) + (K + 1) from by ring,
      show 4 * (K + 1) = 0 + 4 * (K + 1) from by ring]
  apply stepStar_trans (e_consume (k := K) (a := a + 3*K + 3) (e := 0))
  rw [show 3 * (K + 1) = 3 * K + 3 from by ring,
      show a + 3 * K + 3 = (a + 3 * K + 2) + 1 from by ring,
      show 3 * K + 3 = (3 * K + 2) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar c_to_ab)
  ring_nf; finish

theorem trans_odd (K : ℕ) :
    ⟨a, 4*(K+1)+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+6*K+8, 6*K+10, 0, 0, 0⟩ := by
  step fm
  apply stepStar_trans (r3_chain₀ (k := 4*K+5) (a := a+1) (d := 1))
  rw [show a + 1 + (4 * K + 5) = a + (4 * (K + 1) + 2) from by ring,
      show 0 + 1 + (4 * K + 5) = 4 * (K + 1) + 2 from by ring]
  apply stepStar_trans (r4_chain (a := a + (4*(K+1)+2)) (k := 4*(K+1)+2) (e := 0))
  rw [show 0 + (4 * (K + 1) + 2) = 4 * (K + 1) + 2 from by ring,
      show a + (4 * (K + 1) + 2) = (a + 3 * K + 5) + (K + 1) from by ring,
      show 4 * (K + 1) + 2 = 2 + 4 * (K + 1) from by ring]
  apply stepStar_trans (e_consume (k := K) (a := a + 3*K + 5) (e := 2))
  rw [show 3 * (K + 1) = 3 * K + 3 from by ring,
      show a + 3 * K + 5 = (a + 3 * K + 4) + 1 from by ring,
      show 3 * K + 3 = (3 * K + 2) + 1 from by ring]
  apply stepStar_trans e2_tail
  apply stepStar_trans (r3r1_chain ((3*K+2)+1) 3 ((a+3*K+4)+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 4, 0, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b, 0, 0, 0⟩ ∧ b ≥ 4 ∧ 2 ∣ b)
  · intro c ⟨a, b, hq, hb4, ⟨m, hm⟩⟩; subst hq
    rcases Nat.even_or_odd m with ⟨K, hK⟩ | ⟨K, hK⟩
    · subst hK
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rw [show 2 * (K' + 1 + (K' + 1)) = 4 * (K' + 1) from by ring] at hm; subst hm
      exact ⟨⟨a + 6*K' + 4, 6*K' + 8, 0, 0, 0⟩,
             ⟨a + 6*K' + 4, 6*K' + 8, rfl, by omega, ⟨3*K' + 4, by ring⟩⟩,
             trans_even K'⟩
    · subst hK
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rw [show 2 * (2 * (K' + 1) + 1) = 4 * (K' + 1) + 2 from by ring] at hm; subst hm
      exact ⟨⟨a + 6*K' + 8, 6*K' + 10, 0, 0, 0⟩,
             ⟨a + 6*K' + 8, 6*K' + 10, rfl, by omega, ⟨3*K' + 5, by ring⟩⟩,
             trans_odd K'⟩
  · exact ⟨1, 4, rfl, by omega, ⟨2, by ring⟩⟩

end Sz21_140_unofficial_19

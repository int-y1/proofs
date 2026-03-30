import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #671: [35/6, 28/55, 1331/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  3
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_671

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move d to b.
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R3 chain: convert a to e.
theorem r3_chain : ∀ k, ∀ a e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (e + 3)); ring_nf; finish

-- R2 chain: drain c via R2 when b = 0.
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (d + 1) e); ring_nf; finish

-- R1R1R2 chain: each round does R1 R1 R2.
theorem r1r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show (e + k + 1 : ℕ) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) (d + 3) e); ring_nf; finish

-- d=0 transition: (0, 0, 0, 0, e+2) →⁺ (0, 0, 0, 1, e+6)
theorem d0_trans : ⟨0, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, e + 6⟩ := by
  execute fm 4

-- R5+R2 opening.
theorem r5r2_steps : ∀ b, ⟨0, b, 0, 0, e + 1 + 1⟩ [fm]⊢* ⟨2, b, 0, 1, e⟩ := by
  intro b; induction' b with b _
  · step fm; step fm; finish
  · step fm; step fm; finish

-- post_r4_even: even b = 2*(k+1), after R4 phase.
theorem post_r4_even (k : ℕ) :
    ⟨0, 2 * (k + 1), 0, 0, e + 2 * (k + 1) + 2⟩ [fm]⊢*
    ⟨0, 0, 0, 4 * k + 5, e + 6 * k + 12⟩ := by
  rw [show e + 2 * (k + 1) + 2 = (e + 2 * (k + 1)) + 1 + 1 from by ring]
  apply stepStar_trans (r5r2_steps (2 * (k + 1)))
  rw [show (2 * (k + 1) : ℕ) = 0 + 2 * (k + 1) from by ring,
      show e + (0 + 2 * (k + 1)) = (e + (k + 1)) + (k + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (k + 1) 0 0 1 (e + (k + 1)))
  apply stepStar_trans (r2_chain (k + 1) 2 0 (1 + 3 * (k + 1)) e)
  rw [show 2 + 2 * (k + 1) = 0 + (2 * k + 4) from by ring,
      show 1 + 3 * (k + 1) + (k + 1) = 4 * k + 5 from by ring]
  apply stepStar_trans (r3_chain (2 * k + 4) 0 e)
  ring_nf; finish

-- post_r4_odd: odd b = 2*k+1, after R4 phase.
theorem post_r4_odd (k : ℕ) :
    ⟨0, 2 * k + 1, 0, 0, e + 2 * k + 3⟩ [fm]⊢*
    ⟨0, 0, 0, 4 * k + 3, e + 6 * k + 9⟩ := by
  rw [show e + 2 * k + 3 = (e + 2 * k + 1) + 1 + 1 from by ring]
  apply stepStar_trans (r5r2_steps (2 * k + 1))
  rw [show (2 * k + 1 : ℕ) = 1 + 2 * k from by ring,
      show e + 2 * k + 1 = (e + k + 1) + k from by ring]
  apply stepStar_trans (r1r1r2_chain k 1 0 1 (e + k + 1))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show (0 + k : ℕ) = k from by ring]
  apply stepStar_trans (step_stepStar (by unfold fm; rfl :
    (1 + 1, 0 + 1, k, 1 + 3 * k, e + k + 1) [fm]⊢
    (1, 0, k + 1, (1 + 3 * k) + 1, e + k + 1)))
  rw [show k + 1 = 0 + (k + 1) from by ring,
      show e + k + 1 = e + (k + 1) from by ring]
  apply stepStar_trans (r2_chain (k + 1) 1 0 ((1 + 3 * k) + 1) e)
  rw [show 1 + 2 * (k + 1) = 0 + (2 * k + 3) from by ring,
      show (1 + 3 * k) + 1 + (k + 1) = 4 * k + 3 from by ring]
  apply stepStar_trans (r3_chain (2 * k + 3) 0 e)
  ring_nf; finish

-- Even d ≥ 2: first R4 step for ⊢⁺, then chain.
theorem trans_even (k : ℕ) :
    ⟨0, 0, 0, 2 * (k + 1), e + 2 * (k + 1) + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * k + 5, e + 6 * k + 12⟩ := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · unfold fm; rfl
  simp only [Nat.zero_add]
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (d_to_b (2 * k + 1) 1 0)
  simp only [Nat.zero_add]
  rw [show (1 : ℕ) + (2 * k + 1) = 2 * (k + 1) from by ring]
  exact post_r4_even k

-- Odd d ≥ 1: first R4 step for ⊢⁺, then chain.
theorem trans_odd (k : ℕ) :
    ⟨0, 0, 0, 2 * k + 1, e + 2 * k + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * k + 3, e + 6 * k + 9⟩ := by
  rw [show 2 * k + 1 = 2 * k + 0 + 1 from by ring]
  apply step_stepStar_stepPlus
  · unfold fm; rfl
  simp only [Nat.zero_add]
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (d_to_b (2 * k) 1 0)
  simp only [Nat.zero_add]
  rw [show (1 : ℕ) + 2 * k = 2 * k + 1 from by ring]
  exact post_r4_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      rcases K with _ | k
      · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
        exact ⟨⟨0, 0, 0, 1, e' + 6⟩, ⟨1, e' + 6, rfl, by omega⟩, d0_trans⟩
      · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 * (k + 1) + 2 := ⟨e - (2 * (k + 1) + 2), by omega⟩
        exact ⟨⟨0, 0, 0, 4 * k + 5, e' + 6 * k + 12⟩,
          ⟨4 * k + 5, e' + 6 * k + 12, rfl, by omega⟩, trans_even k⟩
    · subst hK
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 * K + 3 := ⟨e - (2 * K + 3), by omega⟩
      exact ⟨⟨0, 0, 0, 4 * K + 3, e' + 6 * K + 9⟩,
        ⟨4 * K + 3, e' + 6 * K + 9, rfl, by omega⟩, trans_odd K⟩
  · exact ⟨0, 3, rfl, by omega⟩

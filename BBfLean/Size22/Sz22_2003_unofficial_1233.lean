import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1233: [5/6, 5929/3, 99/35, 2/11, 3/2]

Vector representation:
```
-1 -1  1  0  0
 0 -1  0  2  2
 0  2 -1 -1  1
 1  0  0  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1233

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: transfer e to a
theorem e_to_a : ∀ k, ∀ a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- R3,R1,R1 drain round
theorem drain_round (a c d e : ℕ) :
    ⟨a + 2, 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨a, 0, c + 2, d, e + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Drain chain (even a): (2k, 0, c+1, d+k, e) ⊢* (0, 0, c+k+1, d, e+k)
theorem drain_even : ∀ k, ∀ c d e,
    ⟨2 * k, 0, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (drain_round (2 * k) c (d + k) e)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R3,R1,R2 odd ending
theorem odd_end (c d e : ℕ) :
    ⟨1, 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, c + 1, d + 2, e + 3⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Drain chain (odd a): (2k+1, 0, c+1, d+k+1, e) ⊢* (0, 0, c+k+1, d+2, e+k+3)
theorem drain_odd : ∀ k, ∀ c d e,
    ⟨2 * k + 1, 0, c + 1, d + k + 1, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2, e + k + 3⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exact odd_end c d e
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    apply stepStar_trans (drain_round (2 * k + 1) c (d + k + 1) e)
    rw [show c + 2 = (c + 1) + 1 from by ring,
        show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show e + (k + 1) + 3 = (e + 1) + k + 3 from by ring]
    exact ih (c + 1) d (e + 1)

-- R3,R2,R2 chain
theorem r3r2r2_chain : ∀ k, ∀ c d e,
    ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 5))
    ring_nf; finish

-- Even main transition: (2k+2, 0, 0, d, 0) ⊢⁺ (6k+5, 0, 0, d+2k+3, 0) when d > k
theorem main_even (k d : ℕ) (hd : d > k) :
    ⟨2 * k + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨6 * k + 5, 0, 0, d + 2 * k + 3, 0⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + k + 1 := ⟨d - k - 1, by omega⟩
  rw [show 2 * k + 2 = (2 * k) + 1 + 1 from by ring]
  step fm; step fm
  rw [show d' + k + 1 = (d' + 1) + k from by ring]
  apply stepStar_trans (drain_even k 0 (d' + 1) 0)
  rw [show 0 + k + 1 = 0 + (k + 1) from by ring,
      show 0 + k = k from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 d' k)
  rw [show d' + 3 * (k + 1) + 1 = d' + 3 * k + 4 from by ring,
      show k + 5 * (k + 1) = 6 * k + 5 from by ring]
  apply stepStar_trans (e_to_a (6 * k + 5) 0 (d' + 3 * k + 4))
  rw [show 0 + (6 * k + 5) = 6 * k + 5 from by ring]
  ring_nf; finish

-- Odd main transition: (2k+3, 0, 0, d, 0) ⊢⁺ (6k+8, 0, 0, d+2k+4, 0) when d > k
theorem main_odd (k d : ℕ) (hd : d > k) :
    ⟨2 * k + 3, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨6 * k + 8, 0, 0, d + 2 * k + 4, 0⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + k + 1 := ⟨d - k - 1, by omega⟩
  rw [show 2 * k + 3 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (drain_odd k 0 d' 0)
  rw [show 0 + k + 1 = 0 + (k + 1) from by ring,
      show d' + 2 = (d' + 1) + 1 from by ring,
      show 0 + k + 3 = k + 3 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 (d' + 1) (k + 3))
  rw [show d' + 1 + 3 * (k + 1) + 1 = d' + 3 * k + 5 from by ring,
      show k + 3 + 5 * (k + 1) = 6 * k + 8 from by ring]
  apply stepStar_trans (e_to_a (6 * k + 8) 0 (d' + 3 * k + 5))
  rw [show 0 + (6 * k + 8) = 6 * k + 8 from by ring]
  ring_nf; finish

-- Main transition: (a+2, 0, 0, d, 0) ⊢⁺ (3a+5, 0, 0, d+a+3, 0) when 2d > a
theorem main_transition (a d : ℕ) (hd : 2 * d > a) :
    ⟨a + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨3 * a + 5, 0, 0, d + a + 3, 0⟩ := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k + 2 = 2 * k + 2 from by ring,
        show 3 * (k + k) + 5 = 6 * k + 5 from by ring,
        show d + (k + k) + 3 = d + 2 * k + 3 from by ring]
    exact main_even k d (by omega)
  · subst hk
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 3 * (2 * k + 1) + 5 = 6 * k + 8 from by ring,
        show d + (2 * k + 1) + 3 = d + 2 * k + 4 from by ring]
    exact main_odd k d (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d, 0⟩ ∧ 2 * d > a)
  · intro c ⟨a, d, hq, hd⟩; subst hq
    exact ⟨⟨3 * a + 5, 0, 0, d + a + 3, 0⟩,
      ⟨3 * a + 3, d + a + 3, by ring_nf, by omega⟩,
      main_transition a d hd⟩
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1233

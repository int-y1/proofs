import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1802: [9/10, 539/2, 44/21, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  1
 2 -1  0 -1  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1802

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: transfer e to c.
theorem e_to_c : ∀ k c d, ⟨(0 : ℕ), 0, c, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (c + 1) d

-- R3+R2+R2 repeated: drain b while accumulating d and e.
theorem drain : ∀ k b d e, ⟨(0 : ℕ), b + k, 0, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d + 3 * k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih b (d + 3) (e + 3))
    ring_nf; finish

-- R3+R1+R1 repeated: spiral consuming c and d, building b and e.
theorem spiral : ∀ k b c d e, ⟨(0 : ℕ), b + 1, c + 2 * k, d + k + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 3 * k + 1, c, d + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) c d (e + 1))
    ring_nf; finish

-- Even E: (0,0,0,D+K+2,2K) →* (0,0,0,D+9K+4,10K+3)
theorem even_star (K D : ℕ) : ⟨(0 : ℕ), 0, 0, D + K + 2, 2 * K⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, D + 9 * K + 4, 10 * K + 3⟩ := by
  rw [show (2 * K : ℕ) = 0 + 2 * K from by ring]
  apply stepStar_trans (e_to_c (2 * K) 0 (D + K + 2) (e := 0))
  rw [show D + K + 2 = (D + K + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (spiral K 0 0 D 0)
  rw [show 0 + 3 * K + 1 = 0 + (3 * K + 1) from by ring,
      show D + 1 = D + 0 + 1 from by ring,
      show (0 + K : ℕ) = K from by ring]
  apply stepStar_trans (drain (3 * K + 1) 0 (D + 0) K)
  ring_nf; finish

theorem even_trans (K D : ℕ) : ⟨(0 : ℕ), 0, 0, D + K + 2, 2 * K⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D + 9 * K + 4, 10 * K + 3⟩ := by
  apply stepStar_stepPlus (even_star K D)
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.2) h; simp at this; omega

-- Odd E: (0,0,0,D+K+2,2K+1) →* (0,0,0,D+9K+8,10K+8)
theorem odd_star (K D : ℕ) : ⟨(0 : ℕ), 0, 0, D + K + 2, 2 * K + 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, D + 9 * K + 8, 10 * K + 8⟩ := by
  rw [show (2 * K + 1 : ℕ) = 0 + (2 * K + 1) from by ring]
  apply stepStar_trans (e_to_c (2 * K + 1) 0 (D + K + 2) (e := 0))
  rw [show D + K + 2 = (D + K + 1) + 1 from by ring]
  step fm
  rw [show (0 + (2 * K + 1) : ℕ) = 1 + 2 * K from by ring]
  apply stepStar_trans (spiral K 0 1 D 0)
  rw [show 0 + 3 * K + 1 = (3 * K) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show (0 + K : ℕ) = K from by ring]
  step fm; step fm; step fm
  rw [show 3 * K + 2 = 0 + (3 * K + 2) from by ring,
      show D + 2 = (D + 1) + 1 from by ring,
      show K + 1 + 1 = K + 2 from by ring]
  apply stepStar_trans (drain (3 * K + 2) 0 (D + 1) (K + 2))
  ring_nf; finish

theorem odd_trans (K D : ℕ) : ⟨(0 : ℕ), 0, 0, D + K + 2, 2 * K + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D + 9 * K + 8, 10 * K + 8⟩ := by
  apply stepStar_stepPlus (odd_star K D)
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.2) h; simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨(0 : ℕ), 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨(0 : ℕ), 0, 0, D, E⟩ ∧ 2 * D ≥ E + 3 ∧ E ≥ 1)
  · intro c ⟨D, E, hq, hD, hE⟩; subst hq
    rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + K + 2 := ⟨D - K - 2, by omega⟩
      refine ⟨⟨(0 : ℕ), 0, 0, D' + 9 * K + 4, 10 * K + 3⟩,
        ⟨D' + 9 * K + 4, 10 * K + 3, rfl, by omega, by omega⟩, even_trans K D'⟩
    · subst hK
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + K + 2 := ⟨D - K - 2, by omega⟩
      refine ⟨⟨(0 : ℕ), 0, 0, D' + 9 * K + 8, 10 * K + 8⟩,
        ⟨D' + 9 * K + 8, 10 * K + 8, rfl, by omega, by omega⟩, odd_trans K D'⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

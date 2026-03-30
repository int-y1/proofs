import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #680: [35/6, 3025/2, 4/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  2  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_680

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move c to b.
theorem c_to_b : ∀ k, ∀ b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- R1R1R3 chain: (2, b+2*k, c, d, e+k) →* (2, b, c+2*k, d+k, e).
theorem r1r1r3_chain : ∀ k, ∀ b c d e,
    ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + 2 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 1) e)
    ring_nf; finish

-- R3R2R2 chain: (0, 0, c, k, e+1) →* (0, 0, c+4*k, 0, e+3*k+1).
theorem r3r2r2_chain : ∀ k, ∀ c e,
    ⟨0, 0, c, k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 4 * k, 0, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm; step fm; step fm
    show ⟨0, 0, c + 4, k, e + 4⟩ [fm]⊢* _
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 4) (e + 3))
    ring_nf; finish

-- Odd transition: (0, 2*m+1, 0, 0, e+m+1) →⁺ (0, 6*m+4, 0, 0, e+3*m+4).
theorem odd_trans (m : ℕ) (e : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, e + m + 1⟩ [fm]⊢⁺ ⟨0, 6 * m + 4, 0, 0, e + 3 * m + 4⟩ := by
  -- R5
  step fm
  -- R3
  step fm
  show ⟨2, 2 * m, 0, 0, e + m⟩ [fm]⊢* _
  -- R1R1R3 chain (k = m)
  rw [show 2 * m = 0 + 2 * m from by ring, show e + m = e + m from rfl]
  apply stepStar_trans (r1r1r3_chain m 0 0 0 e)
  simp only [Nat.zero_add]
  -- Now at (2, 0, 2*m, m, e). R2+R2.
  step fm; step fm
  show ⟨0, 0, 2 * m + 4, m, e + 4⟩ [fm]⊢* _
  -- R3R2R2 chain (k = m)
  rw [show e + 4 = (e + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain m (2 * m + 4) (e + 3))
  rw [show 2 * m + 4 + 4 * m = 6 * m + 4 from by ring,
      show e + 3 + 3 * m + 1 = e + 3 * m + 4 from by ring]
  -- R4 chain
  rw [show (6 * m + 4 : ℕ) = 0 + (6 * m + 4) from by ring]
  apply stepStar_trans (c_to_b (6 * m + 4) 0 0 (e + 3 * m + 4))
  ring_nf; finish

-- Even transition: (0, 2*(m+1), 0, 0, e+m+1) →⁺ (0, 6*m+7, 0, 0, e+3*m+5).
theorem even_trans (m : ℕ) (e : ℕ) :
    ⟨0, 2 * (m + 1), 0, 0, e + m + 1⟩ [fm]⊢⁺ ⟨0, 6 * m + 7, 0, 0, e + 3 * m + 5⟩ := by
  -- R5
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by ring]
  step fm
  -- R3
  step fm
  show ⟨2, 2 * m + 1, 0, 0, e + m⟩ [fm]⊢* _
  -- R1R1R3 chain (k = m)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring, show e + m = e + m from rfl]
  apply stepStar_trans (r1r1r3_chain m 1 0 0 e)
  simp only [Nat.zero_add]
  -- Now at (2, 1, 2*m, m, e). R1 (a=2>=1, b=1>=1).
  step fm
  -- (1, 0, 2*m+1, m+1, e). R2 (a=1>=1, b=0).
  step fm
  show ⟨0, 0, 2 * m + 3, m + 1, e + 2⟩ [fm]⊢* _
  -- R3R2R2 chain (k = m+1)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) (2 * m + 3) (e + 1))
  rw [show 2 * m + 3 + 4 * (m + 1) = 6 * m + 7 from by ring,
      show e + 1 + 3 * (m + 1) + 1 = e + 3 * m + 5 from by ring]
  -- R4 chain
  rw [show (6 * m + 7 : ℕ) = 0 + (6 * m + 7) from by ring]
  apply stepStar_trans (c_to_b (6 * m + 7) 0 0 (e + 3 * m + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b, 0, 0, e⟩ ∧ b ≥ 2 ∧ 2 * e ≥ b)
  · intro c ⟨b, e, hq, hb, he⟩; subst hq
    rcases Nat.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- b even: b = m + m = 2*m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + m' + 1 := ⟨e - m' - 1, by omega⟩
      exact ⟨⟨0, 6 * m' + 7, 0, 0, e' + 3 * m' + 5⟩,
        ⟨6 * m' + 7, e' + 3 * m' + 5, rfl, by omega, by omega⟩,
        even_trans m' e'⟩
    · -- b odd: b = 2*m + 1
      subst hm
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + m + 1 := ⟨e - m - 1, by omega⟩
      exact ⟨⟨0, 6 * m + 4, 0, 0, e' + 3 * m + 4⟩,
        ⟨6 * m + 4, e' + 3 * m + 4, rfl, by omega, by omega⟩,
        odd_trans m e'⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

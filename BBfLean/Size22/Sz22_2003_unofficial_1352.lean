import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1352: [63/10, 363/2, 4/77, 5/3, 7/5]

Vector representation:
```
-1  2 -1  1  0
-1  1  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1352

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem r1r1r3_chain : ∀ k r b d e,
    ⟨2, b, 2 * k + r, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, r, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro r b d e
  · simp; exists 0
  · rw [show 2 * (k + 1) + r = (2 * k + r) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih r (b + 4) (d + 1) e)
    ring_nf; finish

theorem r1_r2_r3 : ⟨2, b, 1, d, e⟩ [fm]⊢* ⟨2, b + 3, 0, d, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem r2r2r3_chain : ∀ k b d e,
    ⟨2, b, 0, d + k, e⟩ [fm]⊢* ⟨2, b + 2 * k, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 2) d (e + 3))
    ring_nf; finish

theorem b_to_c : ∀ k b c e,
    ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e)
    ring_nf; finish

theorem main_even (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 2, 0, e + 3 * k + 4⟩ := by
  step fm; step fm
  apply stepStar_trans (r1r1r3_chain k 0 0 0 e)
  rw [show (0 + 4 * k : ℕ) = 4 * k from by ring,
      show (0 + k : ℕ) = 0 + k from by ring]
  apply stepStar_trans (r2r2r3_chain k (4 * k) 0 e)
  rw [show 4 * k + 2 * k = 6 * k from by ring]
  step fm; step fm
  rw [show (6 * k + 2 : ℕ) = 0 + (6 * k + 2) from by ring]
  apply stepStar_trans (b_to_c (6 * k + 2) 0 0 (e + 3 * k + 4))
  ring_nf; finish

theorem main_odd (k e : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 5, 0, e + 3 * k + 6⟩ := by
  step fm; step fm
  rw [show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans (r1r1r3_chain k 1 0 0 (e + 1))
  rw [show (0 + 4 * k : ℕ) = 4 * k from by ring,
      show (0 + k : ℕ) = k from by ring]
  apply stepStar_trans r1_r2_r3
  rw [show (k : ℕ) = 0 + k from by ring,
      show 4 * (0 + k) + 3 = 4 * k + 3 from by ring,
      show e + 1 + 1 = e + 2 from by ring]
  apply stepStar_trans (r2r2r3_chain k (4 * k + 3) 0 (e + 2))
  rw [show 4 * k + 3 + 2 * k = 6 * k + 3 from by ring]
  step fm; step fm
  rw [show (6 * k + 5 : ℕ) = 0 + (6 * k + 5) from by ring,
      show e + 2 + 3 * k + 4 = e + 3 * k + 6 from by ring]
  apply stepStar_trans (b_to_c (6 * k + 5) 0 0 (e + 3 * k + 6))
  ring_nf; finish

theorem main_trans (c e : ℕ) (he : 2 * e ≥ c) :
    ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 2, 0, e + c + 4⟩ := by
  rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + k := ⟨e - k, by omega⟩
    rw [show (k + k) + 1 = 2 * k + 1 from by ring,
        show 3 * (k + k) + 2 = 6 * k + 2 from by ring,
        show (e' + k) + (k + k) + 4 = e' + 3 * k + 4 from by ring]
    exact main_even k e'
  · subst hk
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + (k + 1) := ⟨e - (k + 1), by omega⟩
    rw [show (2 * k + 1) + 1 = 2 * k + 2 from by ring,
        show (e' + (k + 1)) + 1 = e' + k + 2 from by ring,
        show 3 * (2 * k + 1) + 2 = 6 * k + 5 from by ring,
        show (e' + (k + 1)) + (2 * k + 1) + 4 = e' + 3 * k + 6 from by ring]
    exact main_odd k e'

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 1, 0, e + 1⟩ ∧ 2 * e ≥ c)
  · intro q ⟨c, e, hq, he⟩; subst hq
    exact ⟨⟨0, 0, 3 * c + 2, 0, e + c + 4⟩,
      ⟨3 * c + 1, e + c + 3, by ring_nf, by omega⟩,
      main_trans c e he⟩
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1352

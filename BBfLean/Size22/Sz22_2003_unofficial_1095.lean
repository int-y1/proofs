import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1095: [5/6, 343/2, 44/245, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  3  0
 2  0 -1 -2  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1095

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c+1, d+2, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d; step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R1, R1, R3 chain (even b).
theorem r1r1r3_even : ∀ k c d e, ⟨2, 2 * k, c, d + 2 * k, e⟩ [fm]⊢* ⟨2, 0, c + k, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    show ⟨2, 2 * k + 1 + 1, c, (d + 2 * k) + 2, e⟩ [fm]⊢* ⟨2, 0, c + (k + 1), d, e + (k + 1)⟩
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R1, R1, R3 chain (odd b).
theorem r1r1r3_odd : ∀ k c d e, ⟨2, 2 * k + 1, c, d + 2 * k, e⟩ [fm]⊢* ⟨2, 1, c + k, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    show ⟨2, (2 * k + 1) + 1 + 1, c, (d + 2 * k) + 2, e⟩ [fm]⊢* ⟨2, 1, c + (k + 1), d, e + (k + 1)⟩
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R3, R2, R2 chain.
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c + k, d + 2, e⟩ [fm]⊢* ⟨0, 0, c, d + 4 * k + 2, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = c + k + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih c (d + 4) (e + 1))
    ring_nf; finish

-- Even transition: (0,0,0,d+2m+3,2m) ⊢⁺ (0,0,0,d+4m+6,2m+1)
theorem main_even :
    ⟨0, 0, 0, d + 2 * m + 3, 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * m + 6, 2 * m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) 0 (d + 2 * m + 3))
  rw [show d + 2 * m + 3 = d + 2 * m + 2 + 1 from by omega]
  step fm
  rw [show d + 2 * m + 2 = (d + 2 * m) + 2 from by omega]
  step fm
  rw [show (0 + 2 * m : ℕ) = 2 * m from by omega]
  apply stepStar_trans (r1r1r3_even m 0 d 1)
  step fm; step fm
  rw [show d + 6 = (d + 4) + 2 from by omega,
      show 1 + m = m + 1 from by omega]
  apply stepStar_trans (r3r2r2_chain m 0 (d + 4) (m + 1))
  ring_nf; finish

-- Odd transition: (0,0,0,d+2m+4,2m+1) ⊢⁺ (0,0,0,d+4m+8,2m+2)
theorem main_odd :
    ⟨0, 0, 0, d + 2 * m + 4, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * m + 8, 2 * m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) 0 (d + 2 * m + 4))
  rw [show (0 + (2 * m + 1) : ℕ) = 2 * m + 1 from by omega,
      show d + 2 * m + 4 = d + 2 * m + 3 + 1 from by omega]
  step fm
  rw [show d + 2 * m + 3 = (d + 2 * m + 1) + 2 from by omega]
  step fm
  rw [show d + 2 * m + 1 = (d + 1) + 2 * m from by omega]
  apply stepStar_trans (r1r1r3_odd m 0 (d + 1) 1)
  step fm; step fm
  rw [show d + 1 + 3 = (d + 2) + 2 from by omega,
      show 1 + m = m + 1 from by omega]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 (d + 2) (m + 1))
  ring_nf; finish

-- General even transition.
theorem trans_even (hd : d ≥ 2 * m + 3) :
    ⟨0, 0, 0, d, 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * m + 3, 2 * m + 1⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + (2 * m + 3) := ⟨d - (2 * m + 3), by omega⟩
  show ⟨0, 0, 0, d' + (2 * m + 3), 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, d' + (2 * m + 3) + 2 * m + 3, 2 * m + 1⟩
  rw [show d' + (2 * m + 3) = d' + 2 * m + 3 from by omega,
      show d' + 2 * m + 3 + 2 * m + 3 = d' + 4 * m + 6 from by omega]
  exact main_even

-- General odd transition.
theorem trans_odd (hd : d ≥ 2 * m + 4) :
    ⟨0, 0, 0, d, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * m + 4, 2 * m + 2⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + (2 * m + 4) := ⟨d - (2 * m + 4), by omega⟩
  show ⟨0, 0, 0, d' + (2 * m + 4), 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d' + (2 * m + 4) + 2 * m + 4, 2 * m + 2⟩
  rw [show d' + (2 * m + 4) = d' + 2 * m + 4 from by omega,
      show d' + 2 * m + 4 + 2 * m + 4 = d' + 4 * m + 8 from by omega]
  exact main_odd

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n d, q = ⟨0, 0, 0, d, n⟩ ∧ d ≥ n + 3)
  · intro c ⟨n, d, hq, hd⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      exact ⟨⟨0, 0, 0, d + 2 * m + 3, 2 * m + 1⟩,
        ⟨2 * m + 1, d + 2 * m + 3, rfl, by omega⟩,
        trans_even (by omega)⟩
    · subst hm
      exact ⟨⟨0, 0, 0, d + 2 * m + 4, 2 * m + 2⟩,
        ⟨2 * m + 2, d + 2 * m + 4, rfl, by omega⟩,
        trans_odd (by omega)⟩
  · exact ⟨0, 3, rfl, by omega⟩

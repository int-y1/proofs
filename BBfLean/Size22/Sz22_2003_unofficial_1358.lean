import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1358: [63/10, 4/33, 121/2, 5/7, 15/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1358

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2)); ring_nf; finish

theorem r2_chain : ∀ k a d e, ⟨a, k, 0, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e); ring_nf; finish

theorem d_to_c : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) c (d + 2) e)
    ring_nf; finish

theorem mixing_even (m : ℕ) : ∀ E,
    ⟨2, 0, 2 * m, 0, E + 4 * m⟩ [fm]⊢* ⟨6 * m + 2, 0, 0, 2 * m, E⟩ := by
  intro E
  rw [show 2 * m = 0 + 2 * m from by ring,
      show E + 4 * m = (E + 3 * m) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 0 0 0 (E + 3 * m))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring,
      show (0 : ℕ) + 2 * m = 2 * m from by ring,
      show 6 * m + 2 = 2 + 2 * (3 * m) from by ring]
  exact r2_chain (3 * m) 2 (2 * m) E

theorem mixing_odd (m : ℕ) : ∀ E,
    ⟨2, 0, 2 * m + 1, 0, E + 4 * m + 2⟩ [fm]⊢* ⟨6 * m + 5, 0, 0, 2 * m + 1, E⟩ := by
  intro E
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show E + 4 * m + 2 = (E + 3 * m + 2) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 0 1 0 (E + 3 * m + 2))
  rw [show (0 : ℕ) + 3 * m = 3 * m from by ring,
      show (0 : ℕ) + 2 * m = 2 * m from by ring]
  step fm  -- R1: (1, 3m+2, 0, 2m+1, E+3m+2)
  rw [show 6 * m + 5 = 1 + 2 * (3 * m + 2) from by ring,
      show E + 3 * m + 2 = E + (3 * m + 2) from by ring,
      show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring]
  exact r2_chain (3 * m + 2) 1 (1 + 2 * m) E

theorem main_even (m : ℕ) :
    ⟨0, 0, 2 * m + 1, 0, 8 * m ^ 2 + 16 * m + 8⟩ [fm]⊢⁺
    ⟨0, 0, 2 * m + 2, 0, 8 * m ^ 2 + 24 * m + 18⟩ := by
  rw [show 8 * m ^ 2 + 16 * m + 8 = (8 * m ^ 2 + 16 * m + 6) + 1 + 1 from by ring]
  step fm; step fm
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring,
      show 8 * m ^ 2 + 16 * m + 6 = (8 * m ^ 2 + 12 * m + 2) + 4 * (m + 1) from by ring]
  apply stepStar_trans (mixing_even (m + 1) (8 * m ^ 2 + 12 * m + 2))
  rw [show 6 * (m + 1) + 2 = 6 * m + 8 from by ring,
      show 2 * (m + 1) = 2 * m + 2 from by ring]
  apply stepStar_trans (r3_chain (6 * m + 8) (2 * m + 2) (8 * m ^ 2 + 12 * m + 2))
  rw [show 8 * m ^ 2 + 12 * m + 2 + 2 * (6 * m + 8) = 8 * m ^ 2 + 24 * m + 18 from by ring,
      show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_trans (d_to_c (2 * m + 2) 0 0 (8 * m ^ 2 + 24 * m + 18))
  ring_nf; finish

theorem main_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, 8 * m ^ 2 + 24 * m + 18⟩ [fm]⊢⁺
    ⟨0, 0, 2 * m + 3, 0, 8 * m ^ 2 + 32 * m + 32⟩ := by
  rw [show 8 * m ^ 2 + 24 * m + 18 = (8 * m ^ 2 + 24 * m + 16) + 1 + 1 from by ring]
  step fm; step fm
  rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 from by ring,
      show 8 * m ^ 2 + 24 * m + 16 = (8 * m ^ 2 + 20 * m + 10) + 4 * (m + 1) + 2 from by ring]
  apply stepStar_trans (mixing_odd (m + 1) (8 * m ^ 2 + 20 * m + 10))
  rw [show 6 * (m + 1) + 5 = 6 * m + 11 from by ring,
      show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
  apply stepStar_trans (r3_chain (6 * m + 11) (2 * m + 3) (8 * m ^ 2 + 20 * m + 10))
  rw [show 8 * m ^ 2 + 20 * m + 10 + 2 * (6 * m + 11) = 8 * m ^ 2 + 32 * m + 32 from by ring,
      show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_trans (d_to_c (2 * m + 3) 0 0 (8 * m ^ 2 + 32 * m + 32))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 0, 2 * n ^ 2 + 8 * n + 8⟩ [fm]⊢⁺
    ⟨0, 0, n + 2, 0, 2 * (n + 1) ^ 2 + 8 * (n + 1) + 8⟩ := by
  rw [show 2 * (n + 1) ^ 2 + 8 * (n + 1) + 8 = 2 * n ^ 2 + 12 * n + 18 from by ring]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * (2 * m) ^ 2 + 8 * (2 * m) + 8 = 8 * m ^ 2 + 16 * m + 8 from by ring,
        show 2 * (2 * m) ^ 2 + 12 * (2 * m) + 18 = 8 * m ^ 2 + 24 * m + 18 from by ring]
    exact main_even m
  · subst hm
    rw [show 2 * (2 * m + 1) ^ 2 + 8 * (2 * m + 1) + 8 = 8 * m ^ 2 + 24 * m + 18 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * (2 * m + 1) ^ 2 + 12 * (2 * m + 1) + 18 = 8 * m ^ 2 + 32 * m + 32 from by ring]
    exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 8⟩)
  · execute fm 12
  · show ¬halts fm ⟨0, 0, 0 + 1, 0, 2 * 0 ^ 2 + 8 * 0 + 8⟩
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨0, 0, n + 1, 0, 2 * n ^ 2 + 8 * n + 8⟩) 0
    intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1358

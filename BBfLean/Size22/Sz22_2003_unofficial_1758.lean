import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1758: [9/10, 2/21, 5929/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  0
-1  0  0  2  2
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1758

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem round4 : ⟨0, b, c + 1 + 1, 0, e + 1⟩ [fm]⊢* ⟨0, b + 3, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem interleave4 : ∀ k, ∀ b c e,
    ⟨0, b, c + 2 * (k + 1), 0, e + k + 1⟩ [fm]⊢* ⟨0, b + 3 * (k + 1), c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · rw [show c + 2 * 1 = c + 1 + 1 from by ring, show e + 0 + 1 = e + 1 from by ring]; exact round4
  · rw [show c + 2 * (k + 2) = (c + 2 * (k + 1)) + 1 + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    apply stepStar_trans round4
    rw [show b + 3 * (k + 1 + 1) = (b + 3) + 3 * (k + 1) from by ring]; exact ih (b + 3) c e

theorem round32 : ⟨a + 1, b + 1 + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2, b, 0, 0, e + 2⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem drain32 : ∀ k, ∀ a b e,
    ⟨a + 1, b + 2 * (k + 1), 0, 0, e⟩ [fm]⊢* ⟨a + k + 2, b, 0, 0, e + 2 * (k + 1)⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · rw [show b + 2 * 1 = b + 1 + 1 from by ring]; exact round32
  · rw [show b + 2 * (k + 2) = (b + 2 * (k + 1)) + 1 + 1 from by ring]
    apply stepStar_trans round32
    rw [show a + (k + 1) + 2 = (a + 1) + k + 2 from by ring,
        show e + 2 * (k + 1 + 1) = (e + 2) + 2 * (k + 1) from by ring,
        show (a + 2 : ℕ) = (a + 1) + 1 from by ring]; exact ih (a + 1) b (e + 2)

theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (c + 1) d); ring_nf; finish

theorem a_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]; exact ih a (d + 2) (e + 2)

theorem trans_d2 :
    ⟨0, 0, 0, 4 * j + 2, f + 4 * j + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * j + 6, f + 14 * j + 8⟩ := by
  rw [show (4 * j + 2 : ℕ) = (4 * j + 1) + 1 from by ring]
  step fm
  rw [show (4 * j + 1 : ℕ) = 0 + (4 * j + 1) from by ring]
  apply stepStar_trans (d_to_c (4 * j + 1) (c := 1) (d := 0))
  rw [show 1 + (4 * j + 1) = 0 + 2 * (2 * j + 1) from by ring,
      show (f + 4 * j + 2 : ℕ) = (f + 2 * j + 1) + 2 * j + 1 from by ring]
  apply stepStar_trans (interleave4 (2 * j) 0 0 (f + 2 * j + 1))
  rw [show 0 + 3 * (2 * j + 1) = (6 * j + 2) + 1 from by ring,
      show (f + 2 * j + 1 : ℕ) = (f + 2 * j) + 1 from by ring]
  step fm; step fm
  rw [show (6 * j + 2 : ℕ) = 0 + 2 * (3 * j + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain32 (3 * j) 1 0 (f + 2 * j))
  rw [show 1 + 3 * j + 2 = 0 + (3 * j + 3) from by ring,
      show (f + 2 * j) + 2 * (3 * j + 1) = f + 8 * j + 2 from by ring]
  apply stepStar_trans (a_drain (3 * j + 3) 0 0 (f + 8 * j + 2))
  ring_nf; finish

theorem trans_d0 :
    ⟨0, 0, 0, 4 * j + 4, f + 4 * j + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * j + 9, f + 14 * j + 15⟩ := by
  rw [show (4 * j + 4 : ℕ) = (4 * j + 3) + 1 from by ring]
  step fm
  rw [show (4 * j + 3 : ℕ) = 0 + (4 * j + 3) from by ring]
  apply stepStar_trans (d_to_c (4 * j + 3) (c := 1) (d := 0))
  rw [show 1 + (4 * j + 3) = 0 + 2 * (2 * j + 2) from by ring,
      show (f + 4 * j + 4 : ℕ) = (f + 2 * j + 2) + 2 * j + 2 from by ring]
  apply stepStar_trans (interleave4 (2 * j + 1) 0 0 (f + 2 * j + 2))
  rw [show 0 + 3 * (2 * j + 2) = (6 * j + 5) + 1 from by ring,
      show (f + 2 * j + 2 : ℕ) = (f + 2 * j + 1) + 1 from by ring]
  step fm; step fm
  rw [show (6 * j + 5 : ℕ) = 1 + 2 * (3 * j + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain32 (3 * j + 1) 1 1 (f + 2 * j + 1))
  rw [show 1 + (3 * j + 1) + 2 = (3 * j + 3) + 1 from by ring,
      show (f + 2 * j + 1) + 2 * (3 * j + 2) = f + 8 * j + 5 from by ring]
  step fm; step fm
  rw [show (3 * j + 4 : ℕ) = 0 + (3 * j + 4) from by ring]
  apply stepStar_trans (a_drain (3 * j + 4) 0 1 (f + 8 * j + 7))
  ring_nf; finish

theorem trans_d3 :
    ⟨0, 0, 0, 4 * j + 3, f + 4 * j + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * j + 6, f + 14 * j + 11⟩ := by
  rw [show (4 * j + 3 : ℕ) = (4 * j + 2) + 1 from by ring]
  step fm
  rw [show (4 * j + 2 : ℕ) = 0 + (4 * j + 2) from by ring]
  apply stepStar_trans (d_to_c (4 * j + 2) (c := 1) (d := 0))
  rw [show 1 + (4 * j + 2) = 1 + 2 * (2 * j + 1) from by ring,
      show (f + 4 * j + 3 : ℕ) = (f + 2 * j + 2) + 2 * j + 1 from by ring]
  apply stepStar_trans (interleave4 (2 * j) 0 1 (f + 2 * j + 2))
  rw [show 0 + 3 * (2 * j + 1) = 6 * j + 3 from by ring,
      show (f + 2 * j + 2 : ℕ) = (f + 2 * j + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (6 * j + 2 : ℕ) = 0 + 2 * (3 * j + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain32 (3 * j) 1 0 (f + 2 * j + 3))
  rw [show 1 + 3 * j + 2 = 0 + (3 * j + 3) from by ring,
      show (f + 2 * j + 3) + 2 * (3 * j + 1) = f + 8 * j + 5 from by ring]
  apply stepStar_trans (a_drain (3 * j + 3) 0 0 (f + 8 * j + 5))
  ring_nf; finish

theorem trans_d1 :
    ⟨0, 0, 0, 4 * j + 5, f + 4 * j + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * j + 9, f + 14 * j + 18⟩ := by
  rw [show (4 * j + 5 : ℕ) = (4 * j + 4) + 1 from by ring]
  step fm
  rw [show (4 * j + 4 : ℕ) = 0 + (4 * j + 4) from by ring]
  apply stepStar_trans (d_to_c (4 * j + 4) (c := 1) (d := 0))
  rw [show 1 + (4 * j + 4) = 1 + 2 * (2 * j + 2) from by ring,
      show (f + 4 * j + 5 : ℕ) = (f + 2 * j + 3) + 2 * j + 2 from by ring]
  apply stepStar_trans (interleave4 (2 * j + 1) 0 1 (f + 2 * j + 3))
  rw [show 0 + 3 * (2 * j + 2) = 6 * j + 6 from by ring,
      show (f + 2 * j + 3 : ℕ) = (f + 2 * j + 2) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (6 * j + 5 : ℕ) = 1 + 2 * (3 * j + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain32 (3 * j + 1) 1 1 (f + 2 * j + 4))
  rw [show 1 + (3 * j + 1) + 2 = (3 * j + 3) + 1 from by ring,
      show (f + 2 * j + 4) + 2 * (3 * j + 2) = f + 8 * j + 8 from by ring]
  step fm; step fm
  rw [show (3 * j + 4 : ℕ) = 0 + (3 * j + 4) from by ring]
  apply stepStar_trans (a_drain (3 * j + 4) 0 1 (f + 8 * j + 10))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d f, q = ⟨0, 0, 0, d + 2, f + d + 2⟩)
  · intro c ⟨d, f, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      rcases Nat.even_or_odd K with ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [show j + j = 2 * j from by ring] at hj; subst hj
        refine ⟨⟨0, 0, 0, 6 * j + 6, f + 14 * j + 8⟩,
          ⟨6 * j + 4, f + 8 * j + 2, by ring_nf⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (2 * j) + 2, f + 2 * (2 * j) + 2⟩ [fm]⊢⁺ _
        rw [show 2 * (2 * j) = 4 * j from by ring]; exact trans_d2
      · subst hj
        refine ⟨⟨0, 0, 0, 6 * j + 9, f + 14 * j + 15⟩,
          ⟨6 * j + 7, f + 8 * j + 6, by ring_nf⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (2 * j + 1) + 2, f + 2 * (2 * j + 1) + 2⟩ [fm]⊢⁺ _
        rw [show 2 * (2 * j + 1) = 4 * j + 2 from by ring]; exact trans_d0
    · subst hK
      rcases Nat.even_or_odd K with ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [show j + j = 2 * j from by ring] at hj; subst hj
        refine ⟨⟨0, 0, 0, 6 * j + 6, f + 14 * j + 11⟩,
          ⟨6 * j + 4, f + 8 * j + 5, by ring_nf⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (2 * j) + 1 + 2, f + (2 * (2 * j) + 1) + 2⟩ [fm]⊢⁺ _
        rw [show 2 * (2 * j) + 1 = 4 * j + 1 from by ring,
            show f + (4 * j + 1) + 2 = f + 4 * j + 3 from by ring]; exact trans_d3
      · subst hj
        refine ⟨⟨0, 0, 0, 6 * j + 9, f + 14 * j + 18⟩,
          ⟨6 * j + 7, f + 8 * j + 9, by ring_nf⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (2 * j + 1) + 1 + 2, f + (2 * (2 * j + 1) + 1) + 2⟩ [fm]⊢⁺ _
        rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 from by ring,
            show f + (4 * j + 3) + 2 = f + 4 * j + 5 from by ring]; exact trans_d1
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1758

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1800: [9/10, 539/2, 2/21, 5/7, 98/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  1
 1 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1800

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

theorem spiral_round : ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢* ⟨0, b + 4, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem spiral_chain : ∀ k b c e, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 4 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (spiral_round (b := b) (c := c + 3 * k) (e := e + k))
    apply stepStar_trans (ih (b + 4) c e)
    ring_nf; finish

theorem tail_c1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, 2, e⟩ := by
  step fm; step fm; finish

theorem tail_c2 : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨0, b + 3, 0, 1, e⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain_chain : ∀ k b d e, ⟨0, b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (d + 1) (e + 1))
    ring_nf; finish

theorem trans_mod0 (hk : k ≥ 1) :
    ⟨0, 0, 0, 3 * k, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * k + 4, e + 4 * k + 1⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 3 * (j + 1) = (3 * j + 2) + 1 from by ring]
  step fm
  rw [show e + (j + 1) + 1 = e + j + 2 from by ring,
      show 3 * j + 2 = 0 + (3 * j + 2) from by ring]
  apply stepStar_trans (r4_chain (3 * j + 2) 1 0 (e + j + 2))
  rw [show 1 + (3 * j + 2) = 0 + 3 * (j + 1) from by ring,
      show e + j + 2 = (e + 1) + (j + 1) from by ring]
  apply stepStar_trans (spiral_chain (j + 1) 0 0 (e + 1))
  rw [show 0 + 4 * (j + 1) = 4 * j + 4 from by ring]
  step fm; step fm
  show ⟨0, 4 * j + 4, 0, 4, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 4 * (j + 1) + 4, e + 4 * (j + 1) + 1⟩
  rw [show 4 = 3 + 1 from by ring,
      show e + 1 = (e + 1) + 0 from by ring,
      show 4 * j + 4 = 0 + (4 * j + 4) from by ring]
  apply stepStar_trans (drain_chain (4 * j + 4) 0 3 ((e + 1) + 0))
  ring_nf; finish

theorem trans_mod1 :
    ⟨0, 0, 0, 3 * k + 1, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * k + 4, e + 4 * k + 2⟩ := by
  rw [show 3 * k + 1 = 3 * k + 1 from rfl]
  step fm
  rw [show e + k + 1 = e + 1 + k from by ring,
      show 3 * k = 0 + 3 * k from by ring]
  apply stepStar_trans (r4_chain (3 * k) 1 0 (e + 1 + k))
  rw [show 1 + 3 * k = 1 + 3 * k from rfl,
      show e + 1 + k = (e + 1) + k from by ring]
  apply stepStar_trans (spiral_chain k 0 1 (e + 1))
  rw [show 0 + 4 * k = 4 * k from by ring]
  apply stepStar_trans (tail_c1 (b := 4 * k) (e := e))
  rw [show 2 = 1 + 1 from by ring,
      show e = e + 0 from by ring,
      show 4 * k + 2 = 0 + (4 * k + 2) from by ring]
  apply stepStar_trans (drain_chain (4 * k + 2) 0 1 (e + 0))
  ring_nf; finish

theorem trans_mod2 :
    ⟨0, 0, 0, 3 * k + 2, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * k + 4, e + 4 * k + 3⟩ := by
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
  step fm
  rw [show e + k + 1 = e + 1 + k from by ring,
      show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
  apply stepStar_trans (r4_chain (3 * k + 1) 1 0 (e + 1 + k))
  rw [show 1 + (3 * k + 1) = 2 + 3 * k from by ring,
      show e + 1 + k = (e + 1) + k from by ring]
  apply stepStar_trans (spiral_chain k 0 2 (e + 1))
  rw [show 0 + 4 * k = 4 * k from by ring]
  apply stepStar_trans (tail_c2 (b := 4 * k) (e := e))
  rw [show 1 = 0 + 1 from by ring,
      show e = e + 0 from by ring,
      show 4 * k + 3 = 0 + (4 * k + 3) from by ring]
  apply stepStar_trans (drain_chain (4 * k + 3) 0 0 (e + 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ 3 * e ≥ d + 1)
  · intro c ⟨d, e, hq, hd, hinv⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl⟩ : ∃ k, d = 3 * k ∨ d = 3 * k + 1 ∨ d = 3 * k + 2 :=
      ⟨d / 3, by omega⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + k + 1 := ⟨e - k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 4 * k + 4, F + 4 * k + 1⟩,
        ⟨4 * k + 4, F + 4 * k + 1, rfl, by omega, by omega⟩,
        trans_mod0 (by omega)⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + k + 1 := ⟨e - k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 4 * k + 4, F + 4 * k + 2⟩,
        ⟨4 * k + 4, F + 4 * k + 2, rfl, by omega, by omega⟩,
        trans_mod1⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + k + 1 := ⟨e - k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 4 * k + 4, F + 4 * k + 3⟩,
        ⟨4 * k + 4, F + 4 * k + 3, rfl, by omega, by omega⟩,
        trans_mod2⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

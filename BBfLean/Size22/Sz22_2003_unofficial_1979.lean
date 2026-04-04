import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1979: [99/35, 25/6, 44/5, 7/11, 5/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  2  0  0
 2  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1979

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3_chain : ∀ C, ⟨a, 0, C, 0, z⟩ [fm]⊢* ⟨a + 2 * C, 0, 0, 0, z + C⟩ := by
  intro C; induction' C with C ih generalizing a z
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2) (z := z + 1))
    ring_nf; finish

theorem drain : ∀ B, ∀ A C Z,
    ⟨A, B, C + 1, 0, Z⟩ [fm]⊢* ⟨A + 2 * C + 3 * B + 2, 0, 0, 0, C + Z + 2 * B + 1⟩ := by
  intro B; induction' B with B ih <;> intro A C Z
  · rw [show A + 2 * C + 3 * 0 + 2 = A + 2 * (C + 1) from by ring,
        show C + Z + 2 * 0 + 1 = Z + (C + 1) from by ring]
    exact r3_chain (C + 1)
  · rcases A with _ | A
    · step fm; step fm
      apply stepStar_trans (ih 1 (C + 1) (Z + 1))
      ring_nf; finish
    · step fm
      apply stepStar_trans (ih A (C + 2) Z)
      ring_nf; finish

theorem triple_chain : ∀ K, ∀ B D Z,
    ⟨a + K, B, 2, D + 2 * K, Z⟩ [fm]⊢* ⟨a, B + 3 * K, 2, D, Z + 2 * K⟩ := by
  intro K; induction' K with K ih <;> intro B D Z
  · exists 0
  · rw [show a + (K + 1) = (a + K) + 1 from by ring,
        show D + 2 * (K + 1) = (D + 2 * K) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (B + 3) D (Z + 2))
    ring_nf; finish

theorem main_trans_even : ∀ K,
    ⟨a + K + 2, 0, 0, 0, 2 * K + 1⟩ [fm]⊢⁺
    ⟨a + 9 * K + 7, 0, 0, 0, 8 * K + 5⟩ := by
  intro K
  apply stepStar_stepPlus_stepPlus
  · exact e_to_d (2 * K + 1) (a := a + K + 2) (d := 0)
  step fm; simp only [Nat.zero_add]
  step fm; step fm
  rw [show (2 * K : ℕ) = 0 + 2 * K from by ring]
  apply stepStar_trans (triple_chain K (B := 1) (D := 0) (Z := 1))
  rw [show 1 + 3 * K = 3 * K + 1 from by ring,
      show 1 + 2 * K = 2 * K + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (3 * K + 1) a 1 (2 * K + 1))
  ring_nf; finish

theorem main_trans_odd : ∀ K,
    ⟨a + K + 2, 0, 0, 0, 2 * K + 2⟩ [fm]⊢⁺
    ⟨a + 9 * K + 11, 0, 0, 0, 8 * K + 9⟩ := by
  intro K
  apply stepStar_stepPlus_stepPlus
  · exact e_to_d (2 * K + 2) (a := a + K + 2) (d := 0)
  step fm; simp only [Nat.zero_add]
  step fm; step fm
  rw [show (2 * K + 1 : ℕ) = 1 + 2 * K from by ring]
  apply stepStar_trans (triple_chain K (B := 1) (D := 1) (Z := 1))
  rw [show 1 + 3 * K = 3 * K + 1 from by ring,
      show 1 + 2 * K = 2 * K + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (3 * K + 3) a 0 (2 * K + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a E, q = ⟨a + E + 2, 0, 0, 0, E + 1⟩)
  · intro c ⟨a, E, hq⟩; subst hq
    rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      refine ⟨⟨a + 10 * K + 7, 0, 0, 0, 8 * K + 5⟩,
        ⟨a + 2 * K + 1, 8 * K + 4, by ring_nf⟩, ?_⟩
      show (⟨a + 2 * K + 2, 0, 0, 0, 2 * K + 1⟩ : Q) [fm]⊢⁺
        ⟨a + 10 * K + 7, 0, 0, 0, 8 * K + 5⟩
      rw [show a + 2 * K + 2 = (a + K) + K + 2 from by ring,
          show a + 10 * K + 7 = (a + K) + 9 * K + 7 from by ring]
      exact main_trans_even K
    · subst hK
      refine ⟨⟨a + 10 * K + 12, 0, 0, 0, 8 * K + 9⟩,
        ⟨a + 2 * K + 2, 8 * K + 8, by ring_nf⟩, ?_⟩
      show (⟨a + (2 * K + 1) + 2, 0, 0, 0, (2 * K + 1) + 1⟩ : Q) [fm]⊢⁺
        ⟨a + 10 * K + 12, 0, 0, 0, 8 * K + 9⟩
      rw [show a + (2 * K + 1) + 2 = (a + K + 1) + K + 2 from by ring,
          show (2 * K + 1) + 1 = 2 * K + 2 from by ring,
          show a + 10 * K + 12 = (a + K + 1) + 9 * K + 11 from by ring]
      exact main_trans_odd K
  · exact ⟨0, 0, by ring_nf⟩

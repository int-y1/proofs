import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #956: [4/15, 33/14, 3025/2, 7/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  2
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_956

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    have := ih (a + 1) c d (e + 1)
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring] at this
    exact this

theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    have := ih a (b + 1) (e + 1)
    rw [show b + 1 + k = b + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring] at this
    exact this

theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, 0, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · ring_nf; finish
  · step fm
    have := ih (c + 2) (e + 2)
    rw [show c + 2 + 2 * j = c + 2 * (j + 1) from by ring,
        show e + 2 + 2 * j = e + 2 * (j + 1) from by ring] at this
    exact this

theorem ab_drain : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, 0, e + 2 * a + 4 * b + 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ihb; intro a e
  rcases b with _ | _ | b
  · -- b = 0: just R3 drain
    have := r3_drain (a + 1) 0 e
    rw [show 0 + 2 * (a + 1) = 2 * a + 3 * 0 + 2 from by ring,
        show e + 2 * (a + 1) = e + 2 * a + 4 * 0 + 2 from by ring] at this
    exact this
  · -- b = 1: R3, R1, then R3 drain
    step fm; step fm
    have := r3_drain (a + 2) 1 (e + 2)
    rw [show 1 + 2 * (a + 2) = 2 * a + 3 * 1 + 2 from by ring,
        show e + 2 + 2 * (a + 2) = e + 2 * a + 4 * 1 + 2 from by ring] at this
    exact this
  · -- b = b + 2: R3, R1, R1 then recurse with b
    step fm; step fm; step fm
    have := ihb b (by omega) (a + 3) (e + 2)
    rw [show (a + 3) + 1 = a + 2 + 1 + 1 from by ring] at this
    rw [show a + 1 + 2 + 1 = (a + 3) + 1 from by ring]
    rw [show 2 * (a + 3) + 3 * b + 2 = 2 * a + 3 * (b + 2) + 2 from by ring,
        show (e + 2) + 2 * (a + 3) + 4 * b + 2 = e + 2 * a + 4 * (b + 2) + 2 from by ring]
      at this
    exact this

theorem main_trans (C D : ℕ) (hDC : D ≥ C) (h2C : 2 * C ≥ D) (hC2 : C ≥ 2) :
    ⟨0, 0, C, D, 0⟩ [fm]⊢⁺ ⟨0, 0, C + D + 2, 3 * D + 1, 0⟩ := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
  -- R5: (0, 0, C'+1, D'+1, 0) -> (0, 1, C'+1, D', 0)
  have hR5 : ⟨0, 0, C' + 1, D' + 1, 0⟩ [fm]⊢ ⟨0, 1, C' + 1, D', 0⟩ := by
    unfold fm; simp only
  -- R1: (0, 1, C'+1, D', 0) -> (2, 0, C', D', 0)
  have hR1 : ⟨0, 1, C' + 1, D', 0⟩ [fm]⊢* ⟨2, 0, C', D', 0⟩ := by
    step fm; finish
  -- R2R1 chain (C' rounds): (2, 0, C', D', 0) -> (C'+2, 0, 0, D'-C', C')
  have hchain : ⟨2, 0, C', D', 0⟩ [fm]⊢* ⟨C' + 2, 0, 0, D' - C', C'⟩ := by
    have := r2r1_chain C' 1 0 (D' - C') 0
    simp only [Nat.zero_add] at this
    rw [show (1 : ℕ) + 1 = 2 from rfl,
        show (D' - C') + C' = D' from by omega,
        show 1 + C' + 1 = C' + 2 from by ring] at this
    exact this
  -- R2 drain (D'-C' rounds): (C'+2, 0, 0, D'-C', C') -> (2*C'+2-D', D'-C', 0, 0, D')
  have hdrain : ⟨C' + 2, 0, 0, D' - C', C'⟩ [fm]⊢*
      ⟨2 * C' + 2 - D', D' - C', 0, 0, D'⟩ := by
    have := r2_drain (D' - C') (2 * C' + 2 - D') 0 C'
    rw [show (2 * C' + 2 - D') + (D' - C') = C' + 2 from by omega,
        show 0 + (D' - C') = D' - C' from by omega,
        show C' + (D' - C') = D' from by omega] at this
    exact this
  -- ab_drain: (2*C'+2-D', D'-C', 0, 0, D') -> (0, 0, C'+D'+4, 0, 3*D'+4)
  have hab : ⟨2 * C' + 2 - D', D' - C', 0, 0, D'⟩ [fm]⊢*
      ⟨0, 0, C' + 1 + (D' + 1) + 2, 0, 3 * (D' + 1) + 1⟩ := by
    have := ab_drain (D' - C') (2 * C' + 1 - D') D'
    rw [show (2 * C' + 1 - D') + 1 = 2 * C' + 2 - D' from by omega,
        show 2 * (2 * C' + 1 - D') + 3 * (D' - C') + 2 = C' + 1 + (D' + 1) + 2 from by omega,
        show D' + 2 * (2 * C' + 1 - D') + 4 * (D' - C') + 2 = 3 * (D' + 1) + 1 from by omega]
      at this
    exact this
  -- R4 drain: (0, 0, C+D+2, 0, 3D+1) -> (0, 0, C+D+2, 3D+1, 0)
  have hr4 : ⟨0, 0, C' + 1 + (D' + 1) + 2, 0, 3 * (D' + 1) + 1⟩ [fm]⊢*
      ⟨0, 0, C' + 1 + (D' + 1) + 2, 3 * (D' + 1) + 1, 0⟩ := by
    have := r4_drain (3 * (D' + 1) + 1) (C' + 1 + (D' + 1) + 2) 0
    rw [show 0 + (3 * (D' + 1) + 1) = 3 * (D' + 1) + 1 from by omega] at this
    exact this
  exact step_stepStar_stepPlus hR5
    (stepStar_trans hR1
      (stepStar_trans hchain
        (stepStar_trans hdrain
          (stepStar_trans hab hr4))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C D, q = ⟨0, 0, C, D, 0⟩ ∧ C ≥ 2 ∧ D ≥ C ∧ 2 * C ≥ D)
  · intro q ⟨C, D, hq, hC2, hDC, h2C⟩
    exact ⟨⟨0, 0, C + D + 2, 3 * D + 1, 0⟩,
      ⟨C + D + 2, 3 * D + 1, rfl, by omega, by omega, by omega⟩,
      hq ▸ main_trans C D hDC h2C hC2⟩
  · exact ⟨2, 2, rfl, le_refl 2, le_refl 2, by omega⟩

end Sz22_2003_unofficial_956

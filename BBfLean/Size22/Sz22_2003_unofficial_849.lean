import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #849: [36/35, 5/22, 49/2, 11/3, 55/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_849

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: move b to e
theorem b_to_e : ∀ k d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    have := ih d (e + 1)
    rwa [show e + 1 + k = e + (k + 1) from by omega] at this

-- R3 repeated: drain a to d
theorem r3_drain : ∀ k d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    have := ih (d + 2)
    rwa [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring] at this

-- R2 repeated: drain e, accumulate c
theorem r2_drain : ∀ k c, ⟨a + k, b, c, 0, k⟩ [fm]⊢* ⟨a, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    have := ih (c + 1)
    rwa [show c + 1 + k = c + (k + 1) from by ring] at this

-- R1/R2 interleaved chain
theorem r1r2_chain : ∀ k a b, ⟨a, b, 1, d + k, e + k⟩ [fm]⊢* ⟨a + k, b + 2 * k, 1, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    have := ih (a + 1) (b + 2)
    rwa [show a + 1 + k = a + (k + 1) from by ring,
         show b + 2 + 2 * k = b + 2 * (k + 1) from by ring] at this

-- Bounce + drain: strong induction on c
theorem bounce_drain : ∀ c, ∀ a b, ⟨a + 1, b, c, 0, 0⟩ [fm]⊢* ⟨0, b + 2 * c, 0, 2 * a + 3 * c + 2, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a b
  rcases c with _ | _ | c
  · -- c = 0
    show ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢* ⟨0, b, 0, 2 * a + 2, 0⟩
    have := r3_drain (a + 1) 0 (a := 0) (b := b)
    simp only [Nat.zero_add] at this
    rwa [show 2 * (a + 1) = 2 * a + 2 from by ring] at this
  · -- c = 1
    step fm; step fm; step fm
    show ⟨a + 1, b + 2, 0, 3, 0⟩ [fm]⊢* ⟨0, b + 2, 0, 2 * a + 5, 0⟩
    have := r3_drain (a + 1) 3 (a := 0) (b := b + 2)
    simp only [Nat.zero_add] at this
    rwa [show 3 + 2 * (a + 1) = 2 * a + 5 from by ring] at this
  · -- c + 2
    step fm; step fm; step fm
    rw [show a + 2 + 2 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (a + 3) (b + 4))
    rw [show b + 4 + 2 * c = b + 2 * (c + 2) from by ring,
        show 2 * (a + 3) + 3 * c + 2 = 2 * a + 3 * (c + 2) + 2 from by ring]
    exists 0

-- Main transition
theorem main_trans (hD : D ≥ m + 4) :
    ⟨0, 0, 0, D, D + m⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 2 * D + m + 3, 2 * D + 2 * m + 4⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + m + 4 := ⟨D - m - 4, by omega⟩
  step fm
  rw [show n + m + 3 = 0 + (n + m + 3) from by ring,
      show n + m + 4 + m + 1 = (m + 2) + (n + m + 3) from by ring]
  apply stepStar_trans (r1r2_chain (n + m + 3) 0 0 (d := 0) (e := m + 2))
  rw [show 0 + (n + m + 3) = (n + 1) + (m + 2) from by ring,
      show 0 + 2 * (n + m + 3) = 2 * (n + m + 3) from by ring]
  apply stepStar_trans (r2_drain (m + 2) 1 (a := n + 1) (b := 2 * (n + m + 3)))
  rw [show 1 + (m + 2) = m + 3 from by ring]
  apply stepStar_trans (bounce_drain (m + 3) n (2 * (n + m + 3)))
  rw [show 2 * (n + m + 3) + 2 * (m + 3) = 0 + (2 * (n + m + 3) + 2 * (m + 3)) from by ring,
      show 2 * n + 3 * (m + 3) + 2 = 2 * (n + m + 4) + m + 3 from by ring]
  apply stepStar_trans (b_to_e (2 * (n + m + 3) + 2 * (m + 3))
    (2 * (n + m + 4) + m + 3) 0 (b := 0))
  rw [show 0 + (2 * (n + m + 3) + 2 * (m + 3)) = 2 * (n + m + 4) + 2 * m + 4 from by ring]
  exists 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 12, 12⟩) (by execute fm 43)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D m, q = ⟨0, 0, 0, D, D + m⟩ ∧ D ≥ m + 4)
  · intro c ⟨D, m, hq, hD⟩; subst hq
    refine ⟨⟨0, 0, 0, 2 * D + m + 3, 2 * D + 2 * m + 4⟩,
      ⟨2 * D + m + 3, m + 1, ?_, ?_⟩, main_trans hD⟩
    · unfold Q; simp only [Prod.mk.injEq, true_and]; omega
    · omega
  · exact ⟨12, 0, rfl, by omega⟩

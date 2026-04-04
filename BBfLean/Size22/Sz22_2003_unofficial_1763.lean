import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1763: [9/10, 22/21, 343/2, 5/11, 6/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1763

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ C d, ⟨0, 0, C, d, k⟩ [fm]⊢* ⟨0, 0, C + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro C d
  · exists 0
  · step fm
    apply stepStar_trans (ih (C + 1) d)
    ring_nf; finish

theorem r3_chain : ∀ A, ∀ d, ⟨A, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * A, e⟩ := by
  intro A; induction' A with A ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 3))
    ring_nf; finish

theorem interleave : ∀ k, ∀ B D E, ⟨1, B, k + 1, D + k, E⟩ [fm]⊢* ⟨0, B + k + 2, 0, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · step fm; finish
  · step fm
    step fm
    show ⟨1, B + 1, k + 1, Nat.add D k, E + 1⟩ [fm]⊢* _
    rw [show Nat.add D k = D + k from rfl]
    apply stepStar_trans (ih (B + 1) D (E + 1))
    ring_nf; finish

theorem combined_drain :
    ∀ N, ∀ A B D E, A + 3 * B ≤ N → (B ≥ 1 → A + D ≥ 1) →
    ⟨A, B, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 3 * A + 2 * B, E + B⟩ := by
  intro N; induction' N using Nat.strongRecOn with N ih; intro A B D E hN hcond
  rcases B with _ | B
  · simp at hN ⊢
    exact r3_chain A D
  · rcases D with _ | D
    · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      step fm
      apply stepStar_trans (ih _ (by omega) A' (B + 1) 3 E (le_refl _) (by omega))
      ring_nf; finish
    · step fm
      apply stepStar_trans (ih _ (by omega) (A + 1) B D (E + 1) (le_refl _) (by omega))
      ring_nf; finish

theorem main_trans : ⟨0, 0, 0, e + F + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + F + 7, 2 * e + 1⟩ := by
  rcases e with _ | e
  · -- e = 0: (0,0,0,F+3,0)
    simp only [Nat.zero_add, Nat.mul_zero]
    step fm -- R5: (1, 1, 0, F+2, 0)
    apply stepStar_trans (combined_drain 4 1 1 (F + 2) 0 (by omega) (by omega))
    show ⟨0, 0, 0, F + 2 + 3 * 1 + 2 * 1, 0 + 1⟩ [fm]⊢* ⟨0, 0, 0, F + 7, 1⟩
    ring_nf; finish
  · -- e ≥ 1: (0,0,0,(e+1)+F+3, e+1)
    -- Phase 1: move e+1 from reg e to reg c
    apply stepStar_stepPlus_stepPlus
    · exact e_to_c (e + 1) 0 ((e + 1) + F + 3)
    -- Now at (0, 0, e+1, (e+1)+F+3, 0)
    show ⟨0, 0, 0 + (e + 1), (e + 1) + F + 3, 0⟩ [fm]⊢⁺ _
    rw [show (0 : ℕ) + (e + 1) = e + 1 from by ring]
    -- Phase 2: R5 step
    step fm
    -- Now at (1, 1, e+1, (e+1)+F+3-1, 0) = (1, 1, e+1, e+F+3, 0)
    show ⟨1, 1, e + 1, (e + 1) + F + 3 - 1, 0⟩ [fm]⊢* _
    rw [show (e + 1) + F + 3 - 1 = (F + 3) + e from by omega]
    -- Phase 3: interleave drains c
    apply stepStar_trans (interleave e 1 (F + 3) 0)
    -- Now at (0, e+3, 0, F+3, e)
    show ⟨0, 1 + e + 2, 0, F + 3, 0 + e⟩ [fm]⊢* _
    rw [show 1 + e + 2 = e + 3 from by ring, show (0 : ℕ) + e = e from by ring]
    -- Phase 4: combined drain
    apply stepStar_trans (combined_drain (3 * (e + 3)) 0 (e + 3) (F + 3) e (by omega) (by omega))
    show ⟨0, 0, 0, F + 3 + 3 * 0 + 2 * (e + 3), e + (e + 3)⟩ [fm]⊢* _
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ F e, q = ⟨0, 0, 0, e + F + 3, e⟩)
  · intro q ⟨F, e, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 2 * e + F + 7, 2 * e + 1⟩,
      ⟨F + 3, 2 * e + 1, by ring_nf⟩,
      main_trans⟩
  · exact ⟨0, 0, rfl⟩

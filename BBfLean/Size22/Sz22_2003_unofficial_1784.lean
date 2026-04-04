import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1784: [9/10, 4/21, 539/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  0
-1  0  0  2  1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1784

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

theorem spiral_round : ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢* ⟨0, b + 5, c, 0, e⟩ := by
  step fm
  rw [show c + 3 = (c + 2) + 1 from by ring]
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm; step fm
  rw [show c + 1 = c + 1 from rfl]
  step fm
  ring_nf; finish

theorem spiral_chain : ∀ k, ∀ b c e, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih b (c + 3) (e + 1))
    apply stepStar_trans (spiral_round (b := b + 5 * k) (c := c) (e := e))
    ring_nf; finish

theorem r3r2r2_round : ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢* ⟨a + 4, b, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a b e, ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a (b + 2) e)
    rw [show a + 3 * k + 1 = (a + 3 * k) + 1 from by ring]
    apply stepStar_trans (r3r2r2_round (a := a + 3 * k) (b := b) (e := e + k))
    ring_nf; finish

theorem b1_end : ∀ a, ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * a + 5, e + a + 3⟩ := by
  intro a
  step fm; step fm; step fm
  show ⟨a + 1, 0, 0, 3, e + 2⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 5, e + a + 3⟩
  rw [show a + 1 = 0 + (a + 1) from by ring]
  apply stepStar_trans (r3_drain (a + 1) (d := 3) (e := e + 2))
  ring_nf; finish

theorem c2_handling : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨4, b + 1, 0, 0, e + 1⟩ := by
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  ring_nf; finish

theorem case_even : ∀ m, ⟨0, 0, 0, 6 * m + 2, F + 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 30 * m + 11, F + 20 * m + 7⟩ := by
  intro m
  -- First step: R4 fires since d = 6m+2 >= 1
  rw [show (6 * m + 2 : ℕ) = (6 * m + 1) + 1 from by ring]
  step fm
  -- Now at (0, 0, 1, 6m+1, F+2m+1). Continue with R4 chain.
  show ⟨0, 0, 1, 6 * m + 1, F + 2 * m + 1⟩ [fm]⊢* _
  rw [show (6 * m + 1 : ℕ) = 0 + (6 * m + 1) from by ring]
  apply stepStar_trans (r4_chain (6 * m + 1) (c := 1) (d := 0) (e := F + 2 * m + 1))
  rw [show (1 + (6 * m + 1) : ℕ) = 2 + 3 * (2 * m) from by ring,
      show F + 2 * m + 1 = (F + 1) + 2 * m from by ring]
  apply stepStar_trans (spiral_chain (2 * m) (b := 0) (c := 2) (e := F + 1))
  rw [show (0 + 5 * (2 * m) : ℕ) = 10 * m from by ring]
  apply stepStar_trans (c2_handling (b := 10 * m) (e := F))
  rw [show (10 * m + 1 : ℕ) = 1 + 2 * (5 * m) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (5 * m) (a := 3) (b := 1) (e := F + 1))
  rw [show 3 + 3 * (5 * m) + 1 = (15 * m + 3) + 1 from by ring,
      show F + 1 + 5 * m = F + 5 * m + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (b1_end (15 * m + 3) (e := F + 5 * m + 1)))
  ring_nf; finish

theorem case_odd : ∀ m, ⟨0, 0, 0, 6 * m + 5, F + 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 30 * m + 26, F + 20 * m + 17⟩ := by
  intro m
  rw [show (6 * m + 5 : ℕ) = (6 * m + 4) + 1 from by ring]
  step fm
  show ⟨0, 0, 1, 6 * m + 4, F + 2 * m + 2⟩ [fm]⊢* _
  rw [show (6 * m + 4 : ℕ) = 0 + (6 * m + 4) from by ring]
  apply stepStar_trans (r4_chain (6 * m + 4) (c := 1) (d := 0) (e := F + 2 * m + 2))
  rw [show (1 + (6 * m + 4) : ℕ) = 2 + 3 * (2 * m + 1) from by ring,
      show F + 2 * m + 2 = (F + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (spiral_chain (2 * m + 1) (b := 0) (c := 2) (e := F + 1))
  rw [show (0 + 5 * (2 * m + 1) : ℕ) = 10 * m + 5 from by ring]
  apply stepStar_trans (c2_handling (b := 10 * m + 5) (e := F))
  rw [show (10 * m + 5 + 1 : ℕ) = 0 + 2 * (5 * m + 3) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (5 * m + 3) (a := 3) (b := 0) (e := F + 1))
  rw [show 3 + 3 * (5 * m + 3) + 1 = 15 * m + 13 from by ring,
      show F + 1 + (5 * m + 3) = F + 5 * m + 4 from by ring,
      show (15 * m + 13 : ℕ) = 0 + (15 * m + 13) from by ring]
  apply stepStar_trans (r3_drain (15 * m + 13) (d := 0) (e := F + 5 * m + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D % 3 = 2 ∧ D ≥ 2 ∧ 3 * E ≥ D + 1)
  · intro c ⟨D, E, hq, hmod, hD, hE⟩; subst hq
    rcases Nat.even_or_odd ((D - 2) / 3) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hD_eq : D = 6 * m + 2 := by omega
      subst hD_eq
      obtain ⟨F, rfl⟩ : ∃ F, E = F + 2 * m + 1 := ⟨E - (2 * m + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 30 * m + 11, F + 20 * m + 7⟩,
        ⟨30 * m + 11, F + 20 * m + 7, rfl, by omega, by omega, by omega⟩,
        case_even m⟩
    · have hD_eq : D = 6 * m + 5 := by omega
      subst hD_eq
      obtain ⟨F, rfl⟩ : ∃ F, E = F + 2 * m + 2 := ⟨E - (2 * m + 2), by omega⟩
      exact ⟨⟨0, 0, 0, 30 * m + 26, F + 20 * m + 17⟩,
        ⟨30 * m + 26, F + 20 * m + 17, rfl, by omega, by omega, by omega⟩,
        case_odd m⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

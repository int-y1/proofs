import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1191: [5/6, 49/2, 484/35, 3/11, 25/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1191

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ∀ b d, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ d e, ⟨(0 : ℕ), 0, k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 4 + 3 * k, e + 2 + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 2))
    ring_nf; finish

theorem spiral_even : ∀ k, ∀ c d e, ⟨(0 : ℕ), 2 + 2 * k, c + 1, d + 1 + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 + k, d, e + 2 + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 + 2 * (k + 1) = (2 + 2 * k) + 1 + 1 from by ring,
        show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 2)); ring_nf; finish

theorem spiral_odd : ∀ k, ∀ c d e, ⟨(0 : ℕ), 1 + 2 * k, c + 1, d + 1 + k, e⟩ [fm]⊢* ⟨0, 0, c + 1 + k, d + 2, e + 2 + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 1 + 1 from by ring,
        show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 2)); ring_nf; finish

theorem case_e0 : ⟨(0 : ℕ), 0, 0, G + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, G + 7, 4⟩ := by
  rw [show G + 2 = (G + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show G + 1 + 3 = (G + 3) + 1 from by ring]
  step fm; step fm; step fm; finish

theorem case_e1 : ⟨(0 : ℕ), 0, 0, G + 3, 1⟩ [fm]⊢⁺ ⟨0, 0, 0, G + 9, 6⟩ := by
  step fm
  rw [show G + 3 = (G + 2) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show G + 1 + 2 = (G + 2) + 1 from by ring]
  step fm; step fm; step fm
  rw [show G + 2 + 2 + 2 = (G + 5) + 1 from by ring]
  step fm; step fm; step fm; finish

theorem case_even : ∀ m, ⟨(0 : ℕ), 0, 0, 2 * m + G + 4, 2 + 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + G + 11, 4 * m + 8⟩ := by
  intro m
  rw [show (2 + 2 * m : ℕ) = (1 + 2 * m) + 1 from by ring]
  step fm
  rw [show (1 + 2 * m : ℕ) = 0 + (1 + 2 * m) from by ring]
  apply stepStar_trans (e_to_b (1 + 2 * m) (b := 1) (d := 2 * m + G + 4) (e := 0))
  rw [show 1 + (1 + 2 * m) = 2 + 2 * m from by ring,
      show 2 * m + G + 4 = (2 * m + G + 3) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 2 * m + G + 3 = (m + G + 2) + 1 + m from by ring]
  apply stepStar_trans (spiral_even m 1 (m + G + 2) 0)
  rw [show 1 + 2 + m = (m + 2) + 1 from by ring,
      show m + G + 2 = (m + G + 1) + 1 from by ring,
      show 0 + 2 + 2 * m = 2 + 2 * m from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 2) (m + G + 1) (2 + 2 * m))
  ring_nf; finish

theorem case_odd : ∀ m, ⟨(0 : ℕ), 0, 0, 2 * m + G + 5, 3 + 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + G + 13, 4 * m + 10⟩ := by
  intro m
  rw [show (3 + 2 * m : ℕ) = (2 + 2 * m) + 1 from by ring]
  step fm
  rw [show (2 + 2 * m : ℕ) = 0 + (2 + 2 * m) from by ring]
  apply stepStar_trans (e_to_b (2 + 2 * m) (b := 1) (d := 2 * m + G + 5) (e := 0))
  rw [show 1 + (2 + 2 * m) = 3 + 2 * m from by ring,
      show 2 * m + G + 5 = (2 * m + G + 4) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 3 + 2 * m = 1 + 2 * (m + 1) from by ring,
      show 2 * m + G + 4 = (m + G + 2) + 1 + (m + 1) from by ring]
  apply stepStar_trans (spiral_odd (m + 1) 1 (m + G + 2) 0)
  rw [show 1 + 1 + (m + 1) = (m + 2) + 1 from by ring,
      show m + G + 2 + 2 = (m + G + 3) + 1 from by ring,
      show 0 + 2 + 2 * (m + 1) = 2 * m + 4 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 2) (m + G + 3) (2 * m + 4))
  ring_nf; finish

theorem main_trans {G E : ℕ} : ⟨(0 : ℕ), 0, 0, E + G + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * E + G + 7, 2 * E + 4⟩ := by
  rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rcases m with _ | m
    · rw [show 2 * 0 + G + 2 = G + 2 from by ring,
          show (2 * 0 : ℕ) = 0 from by ring,
          show 2 * (2 * 0) + G + 7 = G + 7 from by ring,
          show 2 * (2 * 0) + 4 = 4 from by ring]
      exact case_e0
    · show ⟨0, 0, 0, 2 * (m + 1) + G + 2, 2 * (m + 1)⟩ [fm]⊢⁺
        ⟨0, 0, 0, 2 * (2 * (m + 1)) + G + 7, 2 * (2 * (m + 1)) + 4⟩
      rw [show 2 * (m + 1) + G + 2 = 2 * m + G + 4 from by ring,
          show (2 * (m + 1) : ℕ) = 2 + 2 * m from by ring,
          show 2 * (2 + 2 * m) + G + 7 = 4 * m + G + 11 from by ring,
          show 2 * (2 + 2 * m) + 4 = 4 * m + 8 from by ring]
      exact case_even m
  · subst hm
    rcases m with _ | m
    · rw [show 2 * 0 + 1 + G + 2 = G + 3 from by ring,
          show (2 * 0 + 1 : ℕ) = 1 from by ring,
          show 2 * (2 * 0 + 1) + G + 7 = G + 9 from by ring,
          show 2 * (2 * 0 + 1) + 4 = 6 from by ring]
      exact case_e1
    · show ⟨0, 0, 0, 2 * (m + 1) + 1 + G + 2, 2 * (m + 1) + 1⟩ [fm]⊢⁺
        ⟨0, 0, 0, 2 * (2 * (m + 1) + 1) + G + 7, 2 * (2 * (m + 1) + 1) + 4⟩
      rw [show 2 * (m + 1) + 1 + G + 2 = 2 * m + G + 5 from by ring,
          show (2 * (m + 1) + 1 : ℕ) = 3 + 2 * m from by ring,
          show 2 * (3 + 2 * m) + G + 7 = 4 * m + G + 13 from by ring,
          show 2 * (3 + 2 * m) + 4 = 4 * m + 10 from by ring]
      exact case_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · step fm; finish
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.2 + p.1 + 2, p.2⟩) ⟨0, 0⟩
  intro ⟨G, E⟩
  refine ⟨⟨G + 1, 2 * E + 4⟩, ?_⟩
  show ⟨0, 0, 0, E + G + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * E + 4 + (G + 1) + 2, 2 * E + 4⟩
  rw [show 2 * E + 4 + (G + 1) + 2 = 2 * E + G + 7 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1191

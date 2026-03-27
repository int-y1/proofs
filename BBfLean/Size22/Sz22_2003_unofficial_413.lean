import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #413: [25/63, 242/7, 7/55, 3/11, 35/2]

Vector representation:
```
 0 -2  2 -1  0
 1  0  0 -1  2
 0  0 -1  1 -1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_413

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem e_to_b : ∀ k a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b; step fm
    apply stepStar_trans (ih a (b+1)); ring_nf; finish

theorem descent : ∀ k a b c, ⟨a+k, b+2*k, c, 0, 0⟩ [fm]⊢* ⟨a, b, c+3*k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; exists 0
  | succ k ih =>
    intro a b c
    show ⟨a + k + 1, b + (2 * k + 2), c, 0, 0⟩ [fm]⊢* ⟨a, b, c + (3 * k + 3), 0, 0⟩
    step fm; step fm
    apply stepStar_trans (ih a b (c + 3)); ring_nf; finish

theorem pump0 : ∀ k a e, ⟨a, 0, k, 0, e+1⟩ [fm]⊢* ⟨a+k, 0, 0, 0, e+k+1⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e; step fm; step fm
    apply stepStar_trans (ih (a+1) (e+1)); ring_nf; finish

theorem pump1 : ∀ k a e, ⟨a, 1, k, 0, e+1⟩ [fm]⊢* ⟨a+k, 1, 0, 0, e+k+1⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e; step fm; step fm
    apply stepStar_trans (ih (a+1) (e+1)); ring_nf; finish

theorem tail0 (a c : ℕ) :
    ⟨a+1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a+c+2, c+3, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
    (show ⟨a+1, 0, c, 0, 0⟩ [fm]⊢ ⟨a, 0, c+1, 1, 0⟩ from by unfold fm; simp)
  apply stepStar_trans
    (step_stepStar (show ⟨a, 0, c+1, 1, 0⟩ [fm]⊢ ⟨a+1, 0, c+1, 0, 2⟩ from by unfold fm; simp))
  apply stepStar_trans
  · show ⟨a+1, 0, c+1, 0, 1+1⟩ [fm]⊢* ⟨a+1+(c+1), 0, 0, 0, 1+(c+1)+1⟩
    exact pump0 (c+1) (a+1) 1
  rw [show a + 1 + (c + 1) = a + c + 2 from by ring,
      show 1 + (c + 1) + 1 = c + 3 from by ring]
  have he := e_to_b (c+3) (a+c+2) 0
  simp only [Nat.zero_add] at he; exact he

theorem tail1 (a c : ℕ) :
    ⟨a+1, 1, c, 0, 0⟩ [fm]⊢⁺ ⟨a+c+2, c+4, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
    (show ⟨a+1, 1, c, 0, 0⟩ [fm]⊢ ⟨a, 1, c+1, 1, 0⟩ from by unfold fm; simp)
  apply stepStar_trans
    (step_stepStar (show ⟨a, 1, c+1, 1, 0⟩ [fm]⊢ ⟨a+1, 1, c+1, 0, 2⟩ from by unfold fm; simp))
  apply stepStar_trans
  · show ⟨a+1, 1, c+1, 0, 1+1⟩ [fm]⊢* ⟨a+1+(c+1), 1, 0, 0, 1+(c+1)+1⟩
    exact pump1 (c+1) (a+1) 1
  rw [show a + 1 + (c + 1) = a + c + 2 from by ring,
      show 1 + (c + 1) + 1 = c + 3 from by ring,
      show c + 4 = 1 + (c + 3) from by ring]
  exact e_to_b (c+3) (a+c+2) 1

theorem cycle_even (a h : ℕ) :
    ⟨a+h+1, 2*h, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+3*h+2, 3*h+3, 0, 0, 0⟩ := by
  rw [show a + h + 1 = (a + 1) + h from by ring,
      show (2 : ℕ) * h = 0 + 2 * h from by ring]
  apply stepStar_stepPlus_stepPlus (descent h (a+1) 0 0)
  simp only [Nat.zero_add]
  exact tail0 a (3*h)

theorem cycle_odd (a h : ℕ) :
    ⟨a+h+1, 2*h+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+3*h+2, 3*h+4, 0, 0, 0⟩ := by
  rw [show a + h + 1 = (a + 1) + h from by ring,
      show 2 * h + 1 = 1 + 2 * h from by ring]
  apply stepStar_stepPlus_stepPlus (descent h (a+1) 1 0)
  simp only [Nat.zero_add]
  exact tail1 a (3*h)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩) (by execute fm 7)
  refine progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = (⟨a, b, 0, 0, 0⟩ : Q) ∧ a ≥ b / 2 + 1 ∧ (b ≥ 2 ∨ a ≥ 2))
    ?_ ⟨2, 3, rfl, by omega, Or.inl (by omega)⟩
  intro q ⟨A, B, hq, hAB, hba⟩; subst hq
  obtain ⟨a₀, ha₀⟩ := Nat.exists_eq_add_of_le hAB
  rcases Nat.even_or_odd B with ⟨h, hBe⟩ | ⟨h, hBo⟩
  · have hBd : B / 2 = h := by omega
    rw [ha₀, hBd, hBe,
        show h + 1 + a₀ = a₀ + h + 1 from by ring,
        show h + h = 2 * h from by ring]
    refine ⟨⟨a₀+3*h+2, 3*h+3, 0, 0, 0⟩,
           ⟨a₀+3*h+2, 3*h+3, rfl, by omega, Or.inl (by omega)⟩,
           cycle_even a₀ h⟩
  · have hBd : B / 2 = h := by omega
    have ha₀_bound : h = 0 → a₀ ≥ 1 := by
      intro hh0; subst hh0; simp at hBo; subst hBo; omega
    rw [ha₀, hBd, hBo,
        show h + 1 + a₀ = a₀ + h + 1 from by ring]
    refine ⟨⟨a₀+3*h+2, 3*h+4, 0, 0, 0⟩,
           ⟨a₀+3*h+2, 3*h+4, rfl, ?_, Or.inl (by omega)⟩,
           cycle_odd a₀ h⟩
    rcases h with _ | h
    · have := ha₀_bound rfl; omega
    · omega

end Sz22_2003_unofficial_413

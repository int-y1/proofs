import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1359: [63/10, 4/33, 121/2, 5/7, 21/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1359

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem a_drain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih d (e + 2)); ring_nf; finish

theorem b_drain : ∀ k a d e, ⟨a, k, 0, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) d e); ring_nf; finish

theorem r1r1r2_chain : ∀ k b d e,
    ⟨2, b, 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e); ring_nf; finish

theorem r1r1r2_chain_odd : ∀ k b d e,
    ⟨2, b, 2 * k + 1, d, e + k⟩ [fm]⊢* ⟨1, b + 3 * k + 2, 0, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · rw [show 2 * 0 + 1 = 0 + 1 from rfl]; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e); ring_nf; finish

theorem main_even (m e : ℕ) :
    ⟨0, 0, 0, 2 * m, e + 4 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 1, e + 12 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
    (c₂ := ⟨0, 0, 0 + 2 * m, 0, e + 4 * m + 2⟩)
  · exact d_to_c (2 * m) 0 (e + 4 * m + 2)
  rw [show (0 + 2 * m : ℕ) = 2 * m from by ring,
      show e + 4 * m + 2 = (e + 4 * m) + 1 + 1 from by ring]
  step fm; step fm
  rw [show e + 4 * m = (e + 3 * m) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 0 1 (e + 3 * m))
  rw [show 0 + 3 * m = 3 * m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  apply stepStar_trans (b_drain (3 * m) 2 (2 * m + 1) e)
  rw [show 2 + 2 * (3 * m) = 6 * m + 2 from by ring]
  apply stepStar_trans (a_drain (6 * m + 2) (2 * m + 1) e)
  rw [show e + 2 * (6 * m + 2) = e + 12 * m + 4 from by ring]; finish

theorem main_odd (m e : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, e + 4 * m + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, e + 12 * m + 10⟩ := by
  apply stepStar_stepPlus_stepPlus
    (c₂ := ⟨0, 0, 0 + (2 * m + 1), 0, e + 4 * m + 4⟩)
  · exact d_to_c (2 * m + 1) 0 (e + 4 * m + 4)
  rw [show (0 + (2 * m + 1) : ℕ) = 2 * m + 1 from by ring,
      show e + 4 * m + 4 = (e + 4 * m + 2) + 1 + 1 from by ring]
  step fm; step fm
  rw [show e + 4 * m + 2 = (e + 3 * m + 2) + m from by ring]
  apply stepStar_trans (r1r1r2_chain_odd m 0 1 (e + 3 * m + 2))
  rw [show 0 + 3 * m + 2 = 3 * m + 2 from by ring,
      show 1 + 2 * m + 1 = 2 * m + 2 from by ring,
      show e + 3 * m + 2 = e + (3 * m + 2) from by ring]
  apply stepStar_trans (b_drain (3 * m + 2) 1 (2 * m + 2) e)
  rw [show 1 + 2 * (3 * m + 2) = 6 * m + 5 from by ring]
  apply stepStar_trans (a_drain (6 * m + 5) (2 * m + 2) e)
  rw [show e + 2 * (6 * m + 5) = e + 12 * m + 10 from by ring]; finish

theorem main_trans_gen (D e : ℕ) :
    ⟨0, 0, 0, D, e + 2 * D + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 1, e + 6 * D + 4⟩ := by
  rcases Nat.even_or_odd D with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show e + 2 * (2 * m) + 2 = e + 4 * m + 2 from by ring,
        show e + 6 * (2 * m) + 4 = e + 12 * m + 4 from by ring]
    exact main_even m e
  · subst hm
    rw [show e + 2 * (2 * m + 1) + 2 = e + 4 * m + 4 from by ring,
        show (2 * m + 1) + 1 = 2 * m + 2 from by ring,
        show e + 6 * (2 * m + 1) + 4 = e + 12 * m + 10 from by ring]
    exact main_odd m e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩)
  · execute fm 5
  change ¬halts fm ⟨0, 0, 0, 0 + 1, 0 + 2 * 0 + 4⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + 2 * d + 4⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  refine ⟨⟨d + 1, e + 4 * d + 4⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, e + 2 * d + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1 + 1, (e + 4 * d + 4) + 2 * (d + 1) + 4⟩
  rw [show e + 2 * d + 4 = e + 2 * (d + 1) + 2 from by ring,
      show d + 1 + 1 = (d + 1) + 1 from by ring,
      show (e + 4 * d + 4) + 2 * (d + 1) + 4 = e + 6 * (d + 1) + 4 from by ring]
  exact main_trans_gen (d + 1) e

end Sz22_2003_unofficial_1359

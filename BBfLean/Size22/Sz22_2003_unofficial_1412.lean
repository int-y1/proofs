import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1412: [7/15, 117/77, 22/3, 5/13, 507/2]

Vector representation:
```
 0 -1 -1  1  0  0
 0  2  0 -1 -1  1
 1 -1  0  0  1  0
 0  0  1  0  0 -1
-1  1  0  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1412

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b+2, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | _ => none

theorem f_to_c : ∀ k c f, ⟨a, 0, c, 0, e, f + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) f); ring_nf; finish

theorem middle_rounds : ∀ k d f, ⟨a, 0, c + 2 * k + 1, d + 1, e + k, f⟩ [fm]⊢*
    ⟨a, 0, c + 1, d + k + 1, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [show c + 2 * (k + 1) + 1 = (c + 2 * k + 1) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show c + 2 * k + 1 + 1 = (c + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 1) (f + 1)); ring_nf; finish

theorem middle_final : ⟨a, 0, 1, d + 1, 1, f⟩ [fm]⊢* ⟨a, 1, 0, d + 1, 0, f + 1⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm; step fm; finish

theorem r1r2_pairs : ∀ k a b f, ⟨a, b, 0, k + 1, 1, f⟩ [fm]⊢*
    ⟨a + k, b + k, 0, 1, 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b f
  · exists 0
  · rw [show k + 1 + 1 = (k + 1) + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (b + 1) (f + 1)); ring_nf; finish

theorem final_r1 : ⟨a, b, 0, 1, 1, f⟩ [fm]⊢* ⟨a, b + 2, 0, 0, 0, f + 1⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm; finish

theorem r2_drain : ∀ k a e f, ⟨a, k, 0, 0, e, f⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1) f); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n ^ 2 + 3 * n + 3, 0, 0, 0, n + 2, 2 * n + 4⟩ [fm]⊢⁺
    ⟨(n + 1) ^ 2 + 3 * (n + 1) + 3, 0, 0, 0, (n + 1) + 2, 2 * (n + 1) + 4⟩ := by
  -- Phase 1: f_to_c
  have p1 : ⟨n ^ 2 + 3 * n + 3, 0, 0, 0, n + 2, 2 * n + 4⟩ [fm]⊢*
      ⟨n ^ 2 + 3 * n + 3, 0, 2 * n + 4, 0, n + 2, 0⟩ := by
    rw [show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
    exact f_to_c (2 * n + 4) 0 0
  -- Phase 2: R4 + R0
  have p2 : ⟨n ^ 2 + 3 * n + 3, 0, 2 * n + 4, 0, n + 2, 0⟩ [fm]⊢⁺
      ⟨n ^ 2 + 3 * n + 2, 0, 2 * n + 3, 1, n + 2, 2⟩ := by
    rw [show n ^ 2 + 3 * n + 3 = (n ^ 2 + 3 * n + 2) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
    step fm; finish
  -- Phase 3: Middle rounds + final
  have p3 : ⟨n ^ 2 + 3 * n + 2, 0, 2 * n + 3, 1, n + 2, 2⟩ [fm]⊢*
      ⟨n ^ 2 + 3 * n + 2, 1, 0, n + 2, 0, n + 4⟩ := by
    rw [show 2 * n + 3 = 0 + 2 * (n + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl,
        show n + 2 = 1 + (n + 1) from by ring]
    apply stepStar_trans (middle_rounds (n + 1) 0 2)
    rw [show 0 + 1 = 1 from by ring,
        show 0 + (n + 1) + 1 = (n + 1) + 1 from by ring,
        show 2 + (n + 1) = (n + 1) + 1 + 1 from by ring,
        show 1 + (n + 1) = n + 2 from by ring]
    step fm; step fm; finish
  -- Phase 4: R2
  have p4 : ⟨n ^ 2 + 3 * n + 2, 1, 0, n + 2, 0, n + 4⟩ [fm]⊢*
      ⟨n ^ 2 + 3 * n + 3, 0, 0, n + 2, 1, n + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 5: R1/R2 pairs + final R1
  have p5 : ⟨n ^ 2 + 3 * n + 3, 0, 0, n + 2, 1, n + 4⟩ [fm]⊢*
      ⟨n ^ 2 + 4 * n + 4, n + 3, 0, 0, 0, 2 * n + 6⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    apply stepStar_trans (r1r2_pairs (n + 1) (n ^ 2 + 3 * n + 3) 0 (n + 4))
    rw [show n ^ 2 + 3 * n + 3 + (n + 1) = n ^ 2 + 4 * n + 4 from by ring,
        show (0 + (n + 1) : ℕ) = n + 1 from by ring,
        show n + 4 + (n + 1) = 2 * n + 5 from by ring]
    exact final_r1
  -- Phase 6: R2 drain
  have p6 : ⟨n ^ 2 + 4 * n + 4, n + 3, 0, 0, 0, 2 * n + 6⟩ [fm]⊢*
      ⟨(n + 1) ^ 2 + 3 * (n + 1) + 3, 0, 0, 0, (n + 1) + 2, 2 * (n + 1) + 4⟩ := by
    apply stepStar_trans (r2_drain (n + 3) (n ^ 2 + 4 * n + 4) 0 (2 * n + 6))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3
        (stepStar_trans p4
          (stepStar_trans p5 p6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2, 4⟩)
  · execute fm 12
  · show ¬halts fm (0 ^ 2 + 3 * 0 + 3, 0, 0, 0, 0 + 2, 2 * 0 + 4)
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨n ^ 2 + 3 * n + 3, 0, 0, 0, n + 2, 2 * n + 4⟩) 0
    intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1412

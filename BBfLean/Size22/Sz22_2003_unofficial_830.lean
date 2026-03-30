import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #830: [35/6, 8/55, 77/2, 39/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  0 -1  0
-1  0  0  1  1  0
 0  1  0 -1  0  1
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_830

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ a d e, ⟨a, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + a, e + a, f⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · rw [show d + (a + 1) = (d + 1) + a from by ring,
        show e + (a + 1) = (e + 1) + a from by ring]
    step fm; apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm; apply stepStar_trans (ih (b + 1) e (f + 1)); ring_nf; finish

theorem r2_chain : ∀ e a c d, ⟨a, 0, c + e, d, e, f⟩ [fm]⊢* ⟨a + 3 * e, 0, c, d, 0, f⟩ := by
  intro e; induction' e with e ih <;> intro a c d
  · exists 0
  · rw [show c + (e + 1) = (c + e) + 1 from by ring,
        show (e : ℕ) + 1 = e + 1 from by ring]
    apply stepStar_trans (step_stepStar (show (⟨a, 0, (c + e) + 1, d, e + 1, f⟩ : Q) [fm]⊢
      ⟨a + 3, 0, c + e, d, e, f⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 3) c d); ring_nf; finish

theorem full_rounds : ∀ k b c d e,
    ⟨3, b + 3 * k, c, d, e + k, f⟩ [fm]⊢* ⟨3, b, c + 2 * k, d + 3 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 3 * (k + 1) = b + 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 3) e); ring_nf; finish

theorem r3r2_alt : ∀ c a d, ⟨a + 1, 0, c, d, 0, f⟩ [fm]⊢* ⟨a + 1 + 2 * c, 0, 0, d + c, 0, f⟩ := by
  intro c; induction' c with c ih <;> intro a d
  · exists 0
  · step fm; step fm
    rw [show a + 3 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (d + 1)); ring_nf; finish

theorem main_trans (m r : ℕ) (hr : r ≥ 1) (hrm : r ≤ 2 * m) :
    ⟨m + r, 0, 0, 2 * m - r, 0, f⟩ [fm]⊢⁺
    ⟨4 * m + r + 2, 0, 0, 5 * m - r + 1, 0, f + 3 * m - 1⟩ := by
  rw [show m + r = (m + r - 1) + 1 from by omega]
  step fm
  apply stepStar_trans (r3_chain (m + r - 1) (2 * m - r + 1) 1 (f := f))
  rw [show 2 * m - r + 1 + (m + r - 1) = 3 * m from by omega,
      show 1 + (m + r - 1) = m + r from by omega]
  apply stepStar_trans (r4_chain (3 * m) 0 (m + r) f)
  simp only [Nat.zero_add]
  rw [show f + 3 * m = (f + 3 * m - 1) + 1 from by omega]
  apply stepStar_trans (step_stepStar (show (⟨0, 3 * m, 0, 0, m + r, (f + 3 * m - 1) + 1⟩ : Q) [fm]⊢
    ⟨0, 3 * m, 1, 0, m + r, f + 3 * m - 1⟩ from by simp [fm]))
  rw [show m + r = (m + r - 1) + 1 from by omega]
  apply stepStar_trans (step_stepStar (show (⟨0, 3 * m, 1, 0, (m + r - 1) + 1, f + 3 * m - 1⟩ : Q) [fm]⊢
    ⟨3, 3 * m, 0, 0, m + r - 1, f + 3 * m - 1⟩ from by simp [fm]))
  show (⟨3, 3 * m, 0, 0, m + r - 1, f + 3 * m - 1⟩ : Q) [fm]⊢* _
  have hfr := full_rounds m 0 0 0 (r - 1) (f := f + 3 * m - 1)
  simp only [Nat.zero_add] at hfr
  rw [show (r - 1) + m = m + r - 1 from by omega] at hfr
  apply stepStar_trans hfr
  rw [show 2 * m = (2 * m - r + 1) + (r - 1) from by omega]
  apply stepStar_trans (r2_chain (r - 1) 3 (2 * m - r + 1) (3 * m) (f := f + 3 * m - 1))
  rw [show 3 + 3 * (r - 1) = 3 * r from by omega]
  rw [show 3 * r = (3 * r - 1) + 1 from by omega]
  have h4 := r3r2_alt (2 * m - r + 1) (3 * r - 1) (3 * m) (f := f + 3 * m - 1)
  rw [show 3 * r - 1 + 1 + 2 * (2 * m - r + 1) = 4 * m + r + 2 from by omega,
      show 3 * m + (2 * m - r + 1) = 5 * m - r + 1 from by omega] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0, 0⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m r f, q = ⟨m + r, 0, 0, 2 * m - r, 0, f⟩ ∧ r ≥ 1 ∧ r ≤ 2 * m)
  · intro c ⟨m, r, f, hq, hr, hrm⟩; subst hq
    refine ⟨⟨4 * m + r + 2, 0, 0, 5 * m - r + 1, 0, f + 3 * m - 1⟩,
      ⟨3 * m + 1, m + r + 1, f + 3 * m - 1, ?_, by omega, by omega⟩,
      main_trans m r hr hrm⟩
    have h1 : (3 * m + 1) + (m + r + 1) = 4 * m + r + 2 := by omega
    have h2 : 2 * (3 * m + 1) - (m + r + 1) = 5 * m - r + 1 := by omega
    rw [h1, h2]
  · exact ⟨2, 2, 0, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_830

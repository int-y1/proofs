import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #695: [35/6, 4/55, 11011/2, 3/7, 2/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  1  2  1
 0  1  0 -1  0  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_695

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k c d e f, ⟨0, 2 * k, c + 1, d, e + k, f⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r2_chain : ∀ k a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢*
    ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r3_chain : ∀ k a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢*
    ⟨a, 0, 0, d + k, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2) (f + 1))
    ring_nf; finish

theorem main_trans (m e f : ℕ) (hsum : e + f = 4 * m + 3) (hf1 : f ≥ 1) (hf2 : f ≤ 2 * m + 1) :
    ⟨0, 0, 0, 2 * m + 1, e, f⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 3, e + 2 * m + 3, f + 2 * m + 1⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, e = r + 2 * m + 1 := ⟨e - 2 * m - 1, by omega⟩
  have phase1 : ⟨0, 0, 0, 2 * m + 1, e, f⟩ [fm]⊢*
      ⟨0, 2 * m + 1, 0, 0, e, f⟩ := by
    rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
    exact r4_chain (2 * m + 1) 0 0 e f
  have phase2 : ⟨0, 2 * m + 1, 0, 0, e, f⟩ [fm]⊢⁺
      ⟨0, 2 * m, 1, 1, e, f - 1⟩ := by
    rw [show f = (f - 1) + 1 from by omega,
        show (2 * m + 1 : ℕ) = (2 * m) + 1 from by ring]
    step fm; step fm; finish
  have phase3 : ⟨0, 2 * m, 1, 1, e, f - 1⟩ [fm]⊢*
      ⟨0, 0, m + 1, 2 * m + 1, r + m + 1, f - 1⟩ := by
    rw [hr, show r + 2 * m + 1 = (r + m + 1) + m from by ring]
    have key := r2r1r1_chain m 0 1 (r + m + 1) (f - 1)
    convert key using 2; ring_nf
  have phase4 : ⟨0, 0, m + 1, 2 * m + 1, r + m + 1, f - 1⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 0, 2 * m + 1, r, f - 1⟩ := by
    rw [show (m + 1 : ℕ) = 0 + (m + 1) from by ring,
        show r + m + 1 = r + (m + 1) from by ring,
        show (2 * m + 2 : ℕ) = 0 + 2 * (m + 1) from by ring]
    exact r2_chain (m + 1) 0 0 (2 * m + 1) r (f - 1)
  have phase5 : ⟨2 * m + 2, 0, 0, 2 * m + 1, r, f - 1⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * m + 3, r + 4 * m + 4, f + 2 * m + 1⟩ := by
    rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring]
    apply stepStar_trans (r3_chain (2 * m + 2) 0 (2 * m + 1) r (f - 1))
    rw [show f - 1 + (2 * m + 2) = f + 2 * m + 1 from by omega]
    ring_nf; finish
  have hrval : r + 4 * m + 4 = e + 2 * m + 3 := by omega
  rw [hrval] at phase5
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase2
      (stepStar_trans phase3
        (stepStar_trans phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e f, q = ⟨0, 0, 0, 2 * m + 1, e, f⟩ ∧ e + f = 4 * m + 3 ∧ f ≥ 1 ∧ f ≤ 2 * m + 1)
  · intro c ⟨m, e, f, hq, hsum, hf1, hf2⟩; subst hq
    refine ⟨⟨0, 0, 0, 4 * m + 3, e + 2 * m + 3, f + 2 * m + 1⟩,
      ⟨2 * m + 1, e + 2 * m + 3, f + 2 * m + 1, by ring_nf, by omega, by omega, by omega⟩,
      main_trans m e f hsum hf1 hf2⟩
  · exact ⟨0, 2, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_695

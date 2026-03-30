import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1086: [5/6, 2/35, 539/2, 3/7, 20/33]

Vector representation:
```
-1 -1  1  0  0
 1  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 2 -1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1086

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r5r1r1_chain : ∀ k b c e, ⟨0, b + 3 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 3) e)
    ring_nf; finish

theorem spiral : ∀ k a e, ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 2 = a + 1 + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem end2_phase : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢* ⟨2, 0, c, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem end1_phase : ⟨0, 1, c + 1, 0, e + 1⟩ [fm]⊢* ⟨3, 0, c, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem case_mod1 (m : ℕ) : ⟨3 * m + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * m + 2, 0, 0, 0, e + 4 * m + 1⟩ := by
  rw [show 3 * m + 1 = 0 + (3 * m) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (3 * m) 0 2 (e + 1))
  rw [show 2 + 2 * (3 * m) = 6 * m + 2 from by ring,
      show e + 1 + 3 * m = e + 3 * m + 1 from by ring]
  apply stepStar_trans (r4_chain (6 * m + 2) 0 (e + 3 * m + 1))
  rw [show 0 + (6 * m + 2) = 6 * m + 2 from by ring,
      show 6 * m + 2 = 2 + 3 * (2 * m) from by ring,
      show e + 3 * m + 1 = (e + m + 1) + (2 * m) from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * m) 2 0 (e + m + 1))
  rw [show 0 + 3 * (2 * m) = 6 * m from by ring,
      show e + m + 1 = (e + m) + 1 from by ring]
  apply stepStar_trans (end2_phase (c := 6 * m) (e := e + m))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 6 * m = 2 * (3 * m) from by ring]
  apply stepStar_trans (spiral (3 * m) 1 ((e + m) + 1))
  ring_nf; finish

theorem case_mod2 (m : ℕ) : ⟨3 * m + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * m + 4, 0, 0, 0, e + 4 * m + 2⟩ := by
  rw [show 3 * m + 2 = 0 + (3 * m + 1) + 1 from by ring]
  step fm
  rw [show 0 + (3 * m + 1) = 0 + (3 * m + 1) from by ring]
  apply stepStar_trans (r3_chain (3 * m + 1) 0 2 (e + 1))
  rw [show 2 + 2 * (3 * m + 1) = 6 * m + 4 from by ring,
      show e + 1 + (3 * m + 1) = e + 3 * m + 2 from by ring]
  apply stepStar_trans (r4_chain (6 * m + 4) 0 (e + 3 * m + 2))
  rw [show 0 + (6 * m + 4) = 6 * m + 4 from by ring,
      show 6 * m + 4 = 1 + 3 * (2 * m + 1) from by ring,
      show e + 3 * m + 2 = (e + m + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * m + 1) 1 0 (e + m + 1))
  rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring,
      show 6 * m + 3 = (6 * m + 2) + 1 from by ring,
      show e + m + 1 = (e + m) + 1 from by ring]
  apply stepStar_trans (end1_phase (c := 6 * m + 2) (e := e + m))
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 6 * m + 2 = 2 * (3 * m + 1) from by ring]
  apply stepStar_trans (spiral (3 * m + 1) 2 ((e + m) + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, e⟩ ↦ ⟨3 * m + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨m, e⟩
  exact ⟨⟨m + 1, e + 8 * m + 3⟩, by
    show ⟨3 * m + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * (m + 1) + 1, 0, 0, 0, e + 8 * m + 3⟩
    rw [show 3 * (m + 1) + 1 = 3 * m + 4 from by ring]
    apply stepPlus_stepStar_stepPlus (case_mod1 m (e := e))
    rw [show 3 * m + 2 = 3 * m + 2 from rfl]
    have h := @case_mod2 (e + 4 * m + 1) m
    rw [show e + 4 * m + 1 + 4 * m + 2 = e + 8 * m + 3 from by ring,
        show 3 * m + 4 = 3 * m + 4 from rfl] at h
    exact stepPlus_stepStar h⟩

end Sz22_2003_unofficial_1086

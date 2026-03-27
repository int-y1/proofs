import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #196: [1/6, 286/35, 55/2, 21/11, 4/39]

Vector representation:
```
-1 -1  0  0  0  0
 1  0 -1 -1  1  1
-1  0  1  0  1  0
 0  1  0  1 -1  0
 2 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_196

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

theorem phase_one : ∀ e f,
    ⟨2, 0, 0, 0, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 0, e+2, f+2⟩ := by
  intro e f
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm; step fm
  rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  ring_nf; finish

theorem e_drain : ∀ k b d f,
    ⟨0, b, 0, d, k, f⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d+k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro b d f; simp; exists 0
  | succ k ih =>
    intro b d f
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) f)
    ring_nf; finish

theorem r5r1r1_drain : ∀ k b d f,
    ⟨0, b + 3 * k, 0, d, 0, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d, 0, f⟩ := by
  intro k; induction k with
  | zero => intro b d f; simp; exists 0
  | succ k ih =>
    intro b d f
    rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) d (f + 1))
    rw [show b + 3 = (b + 2) + 1 from by ring,
        show f + 1 = f + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
        show b + 2 = (b + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show b + 1 = b + 1 from rfl]
    step fm
    finish

theorem r3r2_chain : ∀ k e f,
    ⟨2, 0, 0, k, e, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, 0, 0, e + 2 * k, f + k⟩ := by
  intro k; induction k with
  | zero => intro e f; simp; exists 0
  | succ k ih =>
    intro e f
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show e + 1 + 1 = e + 2 from by ring]
    apply stepStar_trans (ih (e + 2) (f + 1))
    ring_nf; finish

theorem main_trans (m f : ℕ) :
    ⟨2, 0, 0, 0, 3*m+2, f+m⟩ [fm]⊢⁺ ⟨(2 : ℕ), 0, 0, 0, 6*m+8, 3*m+f+4⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 0, 3*m+4, f+m+2⟩)
  · have h := phase_one (3*m+2) (f+m)
    rw [show 3 * m + 2 + 2 = 3 * m + 4 from by ring,
        show f + m + 2 = f + m + 2 from rfl] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*m+4, 0, 3*m+4, 0, f+m+2⟩)
  · have h := e_drain (3*m+4) 0 0 (f+m+2)
    rw [show 0 + (3 * m + 4) = 3 * m + 4 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 3*m+4, 0, f+1⟩)
  · have h := r5r1r1_drain (m+1) 1 (3*m+4) (f+1)
    rw [show 1 + 3 * (m + 1) = 3 * m + 4 from by ring,
        show f + 1 + (m + 1) = f + m + 2 from by ring] at h
    exact h
  apply step_stepStar_stepPlus (c₂ := ⟨2, 0, 0, 3*m+4, 0, f⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show f + 1 = f + 1 from rfl]
    simp [fm]
  have h := r3r2_chain (3*m+4) 0 f
  rw [show 0 + 2 * (3 * m + 4) = 6 * m + 8 from by ring,
      show f + (3 * m + 4) = 3 * m + f + 4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 1⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, f⟩ ↦ ⟨2, 0, 0, 0, 3*m+2, f+m⟩) ⟨0, 1⟩
  intro ⟨m, f⟩
  refine ⟨⟨2*m+2, m+f+2⟩, ?_⟩
  show ⟨2, 0, 0, 0, 3*m+2, f+m⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 3*(2*m+2)+2, (m+f+2)+(2*m+2)⟩
  rw [show 3 * (2 * m + 2) + 2 = 6 * m + 8 from by ring,
      show (m + f + 2) + (2 * m + 2) = 3 * m + f + 4 from by ring]
  exact main_trans m f

end Sz22_2003_unofficial_196

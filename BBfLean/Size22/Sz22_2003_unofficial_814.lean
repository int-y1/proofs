import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #814: [35/6, 8/55, 1001/2, 3/7, 2/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  0 -1  0
-1  0  0  1  1  1
 0  1  0 -1  0  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_814

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k, f + k⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f; step fm
    apply stepStar_trans (ih (d + 1) (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction k with
  | zero => intro b e f; exists 0
  | succ k ih =>
    intro b e f; step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r2_step (a c d e f : ℕ) :
    fm ⟨a, 0, c + 1, d, e + 1, f⟩ = some ⟨a + 3, 0, c, d, e, f⟩ := by
  rcases a with _ | a <;> rfl

theorem r2_drain : ∀ k a c d f, ⟨a, 0, c + k, d, k, f⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, 0, f⟩ := by
  intro k; induction k with
  | zero => intro a c d f; exists 0
  | succ k ih =>
    intro a c d f
    rw [show c + (k + 1) = c + k + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step a (c + k) d k f))
    apply stepStar_trans (ih (a + 3) c d f)
    rw [show a + 3 + 3 * k = a + 3 * (k + 1) from by ring]; finish

theorem inner_loop : ∀ k b c d e f,
    ⟨(3 : ℕ), b + 3 * k, c, d, e + k, f⟩ [fm]⊢* ⟨3, b, c + 2 * k, d + 3 * k, e, f⟩ := by
  intro k; induction k with
  | zero => intro b c d e f; exists 0
  | succ k ih =>
    intro b c d e f
    rw [show b + 3 * (k + 1) = b + 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 3) e f)
    ring_nf; finish

theorem r3r2_alt : ∀ k a d f, ⟨a + 1, 0, k, d, 0, f⟩ [fm]⊢*
    ⟨a + 2 * k + 1, 0, 0, d + k, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro a d f; exists 0
  | succ k ih =>
    intro a d f; step fm; step fm
    rw [show a + 1 + 2 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (d + 1) (f + 1))
    ring_nf; finish

theorem phase3_mod0 (j n : ℕ) :
    ⟨(3 : ℕ), 6 * j + 3 * n, 0, 1, 3 * j + 2 * n, 6 * j + 2 * n⟩ [fm]⊢*
    ⟨3 * j + 3 * n + 3, 0, 3 * j + n, 6 * j + 3 * n + 1, 0, 6 * j + 2 * n⟩ := by
  rw [show 6 * j + 3 * n = 0 + 3 * (2 * j + n) from by ring,
      show 3 * j + 2 * n = (j + n) + (2 * j + n) from by ring]
  apply stepStar_trans (inner_loop (2 * j + n) 0 0 1 (j + n) (6 * j + 2 * n))
  rw [show 0 + 2 * (2 * j + n) = (3 * j + n) + (j + n) from by ring,
      show 1 + 3 * (2 * j + n) = 6 * j + 3 * n + 1 from by ring]
  apply stepStar_trans (r2_drain (j + n) 3 (3 * j + n) (6 * j + 3 * n + 1) (6 * j + 2 * n))
  ring_nf; finish

theorem phase3_mod1 (j n : ℕ) :
    ⟨(3 : ℕ), 6 * j + 3 * n + 2, 0, 1, 3 * j + 2 * n + 1, 6 * j + 2 * n + 2⟩ [fm]⊢*
    ⟨3 * j + 3 * n + 4, 0, 3 * j + n + 1, 6 * j + 3 * n + 3, 0, 6 * j + 2 * n + 2⟩ := by
  rw [show 6 * j + 3 * n + 2 = 2 + 3 * (2 * j + n) from by ring,
      show 3 * j + 2 * n + 1 = (j + n + 1) + (2 * j + n) from by ring]
  apply stepStar_trans (inner_loop (2 * j + n) 2 0 1 (j + n + 1) (6 * j + 2 * n + 2))
  step fm; step fm
  rw [show 0 + 2 * (2 * j + n) + 1 + 1 = (3 * j + n + 1) + (j + n + 1) from by ring,
      show 1 + 3 * (2 * j + n) + 1 + 1 = 6 * j + 3 * n + 3 from by ring]
  apply stepStar_trans (r2_drain (j + n + 1) 1 (3 * j + n + 1) (6 * j + 3 * n + 3) (6 * j + 2 * n + 2))
  ring_nf; finish

theorem phase3_mod2 (j n : ℕ) :
    ⟨(3 : ℕ), 6 * j + 3 * n + 4, 0, 1, 3 * j + 2 * n + 2, 6 * j + 2 * n + 4⟩ [fm]⊢*
    ⟨3 * j + 3 * n + 5, 0, 3 * j + n + 2, 6 * j + 3 * n + 5, 0, 6 * j + 2 * n + 4⟩ := by
  rw [show 6 * j + 3 * n + 4 = 1 + 3 * (2 * j + n + 1) from by ring,
      show 3 * j + 2 * n + 2 = (j + n + 1) + (2 * j + n + 1) from by ring]
  apply stepStar_trans (inner_loop (2 * j + n + 1) 1 0 1 (j + n + 1) (6 * j + 2 * n + 4))
  step fm
  rw [show 0 + 2 * (2 * j + n + 1) + 1 = (3 * j + n + 2) + (j + n + 1) from by ring,
      show 1 + 3 * (2 * j + n + 1) + 1 = 6 * j + 3 * n + 5 from by ring]
  apply stepStar_trans (r2_drain (j + n + 1) 2 (3 * j + n + 2) (6 * j + 3 * n + 5) (6 * j + 2 * n + 4))
  ring_nf; finish

theorem main_transition (n m : ℕ) :
    ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩ [fm]⊢⁺
    ⟨3 * m + 5 * n + 3, 0, 0, 3 * m + 4 * n + 1, 0, 3 * m + 3 * n⟩ := by
  have phase1 : ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * m + 3 * n + 1, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ := by
    have := r3_chain (m + 2 * n + 1) (m + n) 0 m
    rw [show m + n + (m + 2 * n + 1) = 2 * m + 3 * n + 1 from by ring,
        show 0 + (m + 2 * n + 1) = m + 2 * n + 1 from by ring,
        show m + (m + 2 * n + 1) = 2 * m + 2 * n + 1 from by ring] at this
    exact this
  have phase2 : ⟨0, 0, 0, 2 * m + 3 * n + 1, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ [fm]⊢*
      ⟨0, 2 * m + 3 * n + 1, 0, 0, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ := by
    have := r4_chain (2 * m + 3 * n + 1) 0 (m + 2 * n + 1) (2 * m + 2 * n + 1)
    rw [show 0 + (2 * m + 3 * n + 1) = 2 * m + 3 * n + 1 from by ring] at this
    exact this
  have phase3a : ⟨0, 2 * m + 3 * n + 1, 0, 0, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ [fm]⊢⁺
      ⟨3, 2 * m + 3 * n, 0, 1, m + 2 * n, 2 * m + 2 * n⟩ := by
    step fm; step fm; step fm; finish
  have phase3b : ⟨3, 2 * m + 3 * n, 0, 1, m + 2 * n, 2 * m + 2 * n⟩ [fm]⊢*
      ⟨m + 3 * n + 3, 0, m + n, 2 * m + 3 * n + 1, 0, 2 * m + 2 * n⟩ := by
    obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, m = 3 * j ∨ m = 3 * j + 1 ∨ m = 3 * j + 2 := ⟨m / 3, by omega⟩
    · rw [show 2 * (3 * j) + 3 * n = 6 * j + 3 * n from by ring,
          show 2 * (3 * j) + 2 * n = 6 * j + 2 * n from by ring]
      exact phase3_mod0 j n
    · rw [show 2 * (3 * j + 1) + 3 * n = 6 * j + 3 * n + 2 from by ring,
          show 3 * j + 1 + 2 * n = 3 * j + 2 * n + 1 from by ring,
          show 2 * (3 * j + 1) + 2 * n = 6 * j + 2 * n + 2 from by ring,
          show 3 * j + 1 + 3 * n + 3 = 3 * j + 3 * n + 4 from by ring,
          show 3 * j + 1 + n = 3 * j + n + 1 from by ring,
          show 6 * j + 3 * n + 2 + 1 = 6 * j + 3 * n + 3 from by ring]
      exact phase3_mod1 j n
    · rw [show 2 * (3 * j + 2) + 3 * n = 6 * j + 3 * n + 4 from by ring,
          show 3 * j + 2 + 2 * n = 3 * j + 2 * n + 2 from by ring,
          show 2 * (3 * j + 2) + 2 * n = 6 * j + 2 * n + 4 from by ring,
          show 3 * j + 2 + 3 * n + 3 = 3 * j + 3 * n + 5 from by ring,
          show 3 * j + 2 + n = 3 * j + n + 2 from by ring,
          show 6 * j + 3 * n + 4 + 1 = 6 * j + 3 * n + 5 from by ring]
      exact phase3_mod2 j n
  have phase4 : ⟨m + 3 * n + 3, 0, m + n, 2 * m + 3 * n + 1, 0, 2 * m + 2 * n⟩ [fm]⊢*
      ⟨3 * m + 5 * n + 3, 0, 0, 3 * m + 4 * n + 1, 0, 3 * m + 3 * n⟩ := by
    rw [show m + 3 * n + 3 = (m + 3 * n + 2) + 1 from by ring]
    have := r3r2_alt (m + n) (m + 3 * n + 2) (2 * m + 3 * n + 1) (2 * m + 2 * n)
    rw [show m + 3 * n + 2 + 2 * (m + n) + 1 = 3 * m + 5 * n + 3 from by ring,
        show 2 * m + 3 * n + 1 + (m + n) = 3 * m + 4 * n + 1 from by ring,
        show 2 * m + 2 * n + (m + n) = 3 * m + 3 * n from by ring] at this
    exact this
  apply stepStar_stepPlus_stepPlus phase1
  apply stepStar_stepPlus_stepPlus phase2
  apply stepPlus_stepStar_stepPlus phase3a
  apply stepStar_trans phase3b
  exact phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, m⟩ ↦ ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩) ⟨0, 0⟩
  intro ⟨n, m⟩
  refine ⟨⟨n + 1, 3 * m + 3 * n⟩, ?_⟩
  show ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩ [fm]⊢⁺
    ⟨3 * m + 3 * n + 2 * (n + 1) + 1, 0, 0, 3 * m + 3 * n + (n + 1), 0, 3 * m + 3 * n⟩
  rw [show 3 * m + 3 * n + 2 * (n + 1) + 1 = 3 * m + 5 * n + 3 from by ring,
      show 3 * m + 3 * n + (n + 1) = 3 * m + 4 * n + 1 from by ring]
  exact main_transition n m

end Sz22_2003_unofficial_814

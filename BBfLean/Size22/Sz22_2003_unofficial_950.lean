import BBfLean.FM

/-!
# sz22_2003_unofficial #950: [4/15, 33/14, 275/2, 7/11, 4/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 2  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_950

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d; step fm
    have h := ih c (d + 1)
    rwa [show d + 1 + k = d + (k + 1) from by omega] at h

theorem r3_drain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e; step fm
    have h := ih (c + 2) (e + 1)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by omega,
        show e + 1 + k = e + (k + 1) from by omega] at h
    exact h

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by omega,
        show k + 1 = Nat.succ k from rfl]
    step fm; step fm
    have h := ih (a + 1) c (e + 1)
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by omega,
        show e + 1 + k = e + (k + 1) from by omega] at h
    exact h

theorem r5_step : ∀ c d, (⟨0, 0, c + 1, d, 0⟩ : Q) [fm]⊢ ⟨2, 0, c, d, 0⟩ := by
  intro c d
  rcases d with _ | d
  · unfold fm; rfl
  · unfold fm; rfl

theorem main_trans : ∀ c d,
    ⟨0, 0, c + d + 1, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * d + 4, 2 * d + 2, 0⟩ := by
  intro c d
  apply step_stepStar_stepPlus
  · rw [show c + d + 1 = (c + d) + 1 from by omega]
    exact r5_step (c + d) d
  · apply stepStar_trans
    · rw [show (2 : ℕ) = 1 + 1 from by omega]
      exact r2r1_chain d 1 c 0
    · rw [show 1 + d + 1 = d + 2 from by omega,
          show (0 : ℕ) + d = d from by omega]
      apply stepStar_trans
      · have h := r3_drain (d + 2) c d
        rwa [show c + 2 * (d + 2) = c + 2 * d + 4 from by omega,
             show d + (d + 2) = 2 * d + 2 from by omega] at h
      · have h := r4_drain (2 * d + 2) (c + 2 * d + 4) 0
        rwa [show (0 : ℕ) + (2 * d + 2) = 2 * d + 2 from by omega] at h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0 + 1 + 1, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c + d + 1, d, 0⟩) ⟨0, 1⟩
  intro ⟨c, d⟩
  refine ⟨⟨c + 1, 2 * d + 2⟩, ?_⟩
  show ⟨0, 0, c + d + 1, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 1 + (2 * d + 2) + 1, 2 * d + 2, 0⟩
  rw [show c + 1 + (2 * d + 2) + 1 = c + 2 * d + 4 from by omega]
  exact main_trans c d

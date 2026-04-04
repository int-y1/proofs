import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1760: [9/10, 22/21, 343/2, 5/11, 10/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1760

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem e_to_c : ∀ k : ℕ, ∀ c e, ⟨(0 : ℕ), 0, c, d, k + e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; finish
  · rw [show k + 1 + e = (k + e) + 1 from by ring]
    have h1 : ⟨(0 : ℕ), 0, c, d, (k + e) + 1⟩ [fm]⊢ ⟨0, 0, c + 1, d, k + e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    apply stepStar_trans (ih (c + 1) e)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

theorem r5_step : ⟨(0 : ℕ), 0, c, d + 1, 0⟩ [fm]⊢ ⟨1, 0, c + 1, d, 0⟩ := by
  simp [fm]

theorem r2r1_chain : ∀ k : ℕ, ∀ b d e, ⟨(0 : ℕ), b + 1, k, d + k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    have h1 : ⟨(0 : ℕ), b + 1, k + 1, (d + k) + 1, e⟩ [fm]⊢ ⟨1, b, k + 1, d + k, e + 1⟩ := by
      show fm ⟨0, b + 1, k + 1, (d + k) + 1, e⟩ = some ⟨0 + 1, b, k + 1, d + k, e + 1⟩
      simp [fm]
    apply stepStar_trans (step_stepStar h1)
    step fm
    apply stepStar_trans (ih (b + 1) d (e + 1))
    ring_nf; finish

theorem spiral : ∀ k : ℕ, ∀ d, ⟨(1 : ℕ), 0, k + 1, d + k, 0⟩ [fm]⊢* ⟨0, k + 2, 0, d, k⟩ := by
  intro k d
  step fm
  rw [show d + k = d + k from rfl]
  apply stepStar_trans (r2r1_chain k 1 d 0)
  ring_nf; finish

theorem r2_chain : ∀ k : ℕ, ∀ a b d e, ⟨a, b + k, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨a + k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b d (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k : ℕ, ∀ a d e, ⟨a + k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 3) e)
    ring_nf; finish

theorem drain : ∀ M : ℕ, ∀ a b d e, 4 * a + 4 * b + d = M →
    (a ≥ 1 ∨ b = 0 ∨ d ≥ 1) →
    ⟨a, b, (0 : ℕ), d, e⟩ [fm]⊢* ⟨0, 0, 0, 3 * a + 2 * b + d, e + b⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih
  intro a b d e hM hcond
  rcases a with _ | a
  · rcases b with _ | b
    · simp; finish
    · rcases d with _ | d
      · exfalso; omega
      · have h1 : ⟨(0 : ℕ), b + 1, 0, d + 1, e⟩ [fm]⊢ ⟨1, b, 0, d, e + 1⟩ := by
          show fm ⟨0, b + 1, 0, d + 1, e⟩ = some ⟨0 + 1, b, 0, d, e + 1⟩; simp [fm]
        apply stepStar_trans (step_stepStar h1)
        apply stepStar_trans (ih (4 * 1 + 4 * b + d) (by omega) 1 b d (e + 1) (by ring) (Or.inl (by omega)))
        ring_nf; finish
  · rcases b with _ | b
    · rcases d with _ | d
      · apply stepStar_trans (step_stepStar (show ⟨a + 1, 0, (0 : ℕ), 0, e⟩ [fm]⊢ ⟨a, 0, 0, 3, e⟩ from by simp [fm]))
        apply stepStar_trans (ih (4 * a + 3) (by omega) a 0 3 e (by ring) (Or.inr (Or.inr (by omega))))
        ring_nf; finish
      · apply stepStar_trans (step_stepStar (show ⟨a + 1, 0, (0 : ℕ), d + 1, e⟩ [fm]⊢ ⟨a, 0, 0, d + 1 + 3, e⟩ from by simp [fm]))
        apply stepStar_trans (ih (4 * a + (d + 1 + 3)) (by omega) a 0 (d + 1 + 3) e (by ring) (Or.inr (Or.inl rfl)))
        ring_nf; finish
    · rcases d with _ | d
      · apply stepStar_trans (step_stepStar (show ⟨a + 1, b + 1, (0 : ℕ), 0, e⟩ [fm]⊢ ⟨a, b + 1, 0, 3, e⟩ from by simp [fm]))
        apply stepStar_trans (ih (4 * a + 4 * (b + 1) + 3) (by omega) a (b + 1) 3 e (by ring) (Or.inr (Or.inr (by omega))))
        ring_nf; finish
      · step fm
        apply stepStar_trans (ih (4 * (a + 1 + 1) + 4 * b + d) (by omega) (a + 1 + 1) b d (e + 1) (by ring) (Or.inl (by omega)))
        ring_nf; finish

theorem phases_combined (G e : ℕ) :
    ⟨(0 : ℕ), 0, 0, e + G + 2, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * e + G + 5, 2 * e + 2⟩ := by
  rw [show (e : ℕ) = e + 0 from by ring]
  apply stepStar_trans (e_to_c e (d := e + G + 2) 0 0)
  rw [show 0 + e = e from by ring, show e + G + 2 = (e + G + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (r5_step (c := e) (d := e + G + 1)))
  rw [show e + G + 1 = (G + 1) + e from by ring]
  apply stepStar_trans (spiral e (G + 1))
  apply stepStar_trans (drain (4 * 0 + 4 * (e + 2) + (G + 1)) 0 (e + 2) (G + 1) e rfl (Or.inr (Or.inr (by omega))))
  have h1 : 3 * 0 + 2 * (e + 2) + (G + 1) = 2 * e + G + 5 := by ring
  have h2 : e + (e + 2) = 2 * e + 2 := by ring
  rw [h1, h2]; finish

theorem main_trans (G e : ℕ) : ⟨(0 : ℕ), 0, 0, e + G + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + G + 5, 2 * e + 2⟩ := by
  apply stepStar_stepPlus (phases_combined G e)
  simp [Q]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨G, e⟩ ↦ ⟨0, 0, 0, e + G + 2, e⟩) ⟨1, 0⟩
  intro ⟨G, e⟩
  refine ⟨⟨G + 1, 2 * e + 2⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, e + G + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, (2 * e + 2) + (G + 1) + 2, 2 * e + 2⟩
  rw [show (2 * e + 2) + (G + 1) + 2 = 2 * e + G + 5 from by ring]
  exact main_trans G e

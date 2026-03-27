import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #342: [2/15, 1/14, 297/2, 7/9, 50/11]

Vector representation:
```
 1 -1 -1  0  0
-1  0  0 -1  0
-1  3  0  0  1
 0 -2  0  1  0
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_342

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b+2, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

theorem r1_chain : ∀ k : ℕ, ∀ a b c d e,
    ⟨a, b + k, c + k, d, e⟩ [fm]⊢* ⟨a + k, b, c, d, e⟩ := by
  intro k; induction k with
  | zero => intro a b c d e; exists 0
  | succ k ih =>
    intro a b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _ _)
    ring_nf; finish

theorem r3_chain : ∀ k : ℕ, ∀ a b e,
    ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

theorem r4_chain : ∀ k : ℕ, ∀ b d e,
    ⟨0, b + 2 * k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

theorem drain : ∀ k : ℕ, ∀ c,
    ⟨1, 0, c, k, k⟩ [fm]⊢* ⟨1, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

theorem phase1 : ∀ c : ℕ, ∀ a e,
    ⟨a + 1, 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 3 * a + 3 + 2 * c, 0, 0, e + a + 1 + c⟩ := by
  intro c; induction c using Nat.strongRecOn with
  | _ c ih => match c with
    | 0 =>
      intro a e
      have hstep : fm ⟨a + 1, 0, 0, 0, e⟩ = some ⟨a, 3, 0, 0, e + 1⟩ := by
        simp [fm]
      have h := r3_chain a 0 3 (e + 1)
      simp only [Nat.zero_add] at h
      apply step_stepStar_stepPlus hstep
      apply stepStar_trans h
      ring_nf; finish
    | 1 =>
      intro a e
      have hstep : fm ⟨a + 1, 0, 1, 0, e⟩ = some ⟨a, 3, 1, 0, e + 1⟩ := by
        simp [fm]
      apply step_stepStar_stepPlus hstep
      step fm; step fm
      have h := r3_chain a 0 5 (e + 2)
      simp only [Nat.zero_add] at h
      apply stepStar_trans h
      ring_nf; finish
    | 2 =>
      intro a e
      have hstep : fm ⟨a + 1, 0, 2, 0, e⟩ = some ⟨a, 3, 2, 0, e + 1⟩ := by
        simp [fm]
      apply step_stepStar_stepPlus hstep
      have h1 := r1_chain 2 a 1 0 0 (e + 1)
      simp only [Nat.zero_add] at h1
      apply stepStar_trans h1
      step fm
      have h2 := r3_chain (a + 1) 0 4 (e + 2)
      simp only [Nat.zero_add] at h2
      apply stepStar_trans h2
      ring_nf; finish
    | c + 3 =>
      intro a e
      have hstep : fm ⟨a + 1, 0, c + 3, 0, e⟩ = some ⟨a, 3, c + 3, 0, e + 1⟩ := by
        simp [fm]
      apply step_stepStar_stepPlus hstep
      have h1 := r1_chain 3 a 0 c 0 (e + 1)
      simp only [Nat.zero_add] at h1
      apply stepStar_trans h1
      have h2 := ih c (by omega) (a + 2) (e + 1)
      apply stepStar_trans (stepPlus_stepStar h2)
      ring_nf; finish

theorem main_step : ∀ c : ℕ,
    ⟨1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 2 * c + 1, 0, 0⟩ := by
  intro c
  have h1 := phase1 c 0 0
  -- h1 : (0+1, 0, c, 0, 0) ⊢⁺ (0, 3*0+3+2*c, 0, 0, 0+0+1+c)
  have h2 := r4_chain (c + 1) 1 0 (c + 1)
  simp only [Nat.zero_add] at h1 h2
  -- Now h1 : (1, 0, c, 0, 0) ⊢⁺ (0, 3 + 2*c, 0, 0, 1 + c)
  -- h2 : (0, 1 + 2*(c+1), 0, 0, c+1) ⊢* (0, 1, 0, c+1, c+1)
  have h2' : (0, 3 + 2 * c, 0, 0, 1 + c) [fm]⊢* (0, 1, 0, c + 1, c + 1) := by
    have : 1 + 2 * (c + 1) = 3 + 2 * c := by ring
    have : (1 : ℕ) + c = c + 1 := by ring
    rw [this]; rw [show 3 + 2 * c = 1 + 2 * (c + 1) from by ring]; exact h2
  have h4 := drain c 1
  apply stepPlus_stepStar_stepPlus h1
  apply stepStar_trans h2'
  -- now at (0, 1, 0, c+1, c+1)
  -- step: (0, 1, 0, c+1, c+1) can't use r1 (b=1,c=0), can't use r2 (a=0),
  -- can't use r3 (a=0), can use r4? b=1 so b+2 doesn't match b=1.
  -- Actually none of the first 4 rules match. Rule 5: e = c+1 ≥ 1
  -- (0, 1, 0, c+1, c+1) -r5-> (1, 1, 2, c+1, c) -r1-> (2, 0, 1, c+1, c) -r2-> (1, 0, 1, c, c)
  step fm; step fm; step fm
  apply stepStar_trans h4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n => ⟨1, 0, n, 0, 0⟩) 0
  intro i
  exact ⟨2 * i + 1, main_step i⟩

end Sz22_2003_unofficial_342

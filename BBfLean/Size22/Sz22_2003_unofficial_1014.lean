import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1014: [4/15, 9/154, 35/2, 11/5, 4/7]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1 -1
-1  0  1  1  0
 0  0 -1  0  1
 2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1014

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r3_drain : ∀ A, ∀ c d, ⟨A, (0 : ℕ), c, d, 0⟩ [fm]⊢* ⟨0, 0, c + A, d + A, 0⟩ := by
  intro A; induction A with
  | zero => intro c d; exists 0
  | succ A ih =>
    intro c d; step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem r4_drain : ∀ C, ∀ d e, ⟨(0 : ℕ), 0, C, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + C⟩ := by
  intro C; induction C with
  | zero => intro d e; exists 0
  | succ C ih =>
    intro d e
    rw [show C + 1 = (C + 1) from rfl]
    step fm
    apply stepStar_trans (ih d (e + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem drain_rounds : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b, 0, d + 3 * k + 2, 2 * k + 1⟩ [fm]⊢* ⟨1, b + 4 * k + 2, 0, d, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro b d; simp; step fm; step fm; finish
  | succ k ih =>
    intro b d
    rw [show d + 3 * (k + 1) + 2 = (d + 3 * k + 2) + 3 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) d)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem interleave : ∀ B, ∀ a d,
    ⟨a, B + 1, (1 : ℕ), d + 1, 0⟩ [fm]⊢* ⟨a + B + 2, 0, 0, d + B + 1, 0⟩ := by
  intro B; induction B with
  | zero => intro a d; simp; step fm; finish
  | succ B ih =>
    intro a d
    rw [show B + 1 + 1 = (B + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem phase4 (B d : ℕ) :
    ⟨(1 : ℕ), B + 1, 0, d, 0⟩ [fm]⊢* ⟨B + 2, 0, 0, d + B + 1, 0⟩ := by
  step fm
  have h := interleave B 0 d
  rw [show (0 : ℕ) + B + 2 = B + 2 from by omega] at h
  exact h

theorem main_trans_star (k d : ℕ) :
    ⟨2 * k + 1, (0 : ℕ), 0, d + k + 1, 0⟩ [fm]⊢* ⟨4 * k + 3, 0, 0, d + 4 * k + 2, 0⟩ := by
  have h1 := r3_drain (2 * k + 1) 0 (d + k + 1)
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by omega,
      show d + k + 1 + (2 * k + 1) = d + 3 * k + 2 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r4_drain (2 * k + 1) (d + 3 * k + 2) 0
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by omega] at h2
  apply stepStar_trans h2
  have h3 := drain_rounds k 0 d
  rw [show (0 : ℕ) + 4 * k + 2 = 4 * k + 2 from by ring] at h3
  apply stepStar_trans h3
  have h4 := phase4 (4 * k + 1) d
  rw [show 4 * k + 1 + 2 = 4 * k + 3 from by ring,
      show d + (4 * k + 1) + 1 = d + 4 * k + 2 from by ring] at h4
  exact h4

theorem main_trans (k d : ℕ) :
    ⟨2 * k + 1, (0 : ℕ), 0, d + k + 1, 0⟩ [fm]⊢⁺ ⟨4 * k + 3, 0, 0, d + 4 * k + 2, 0⟩ := by
  exact stepStar_stepPlus (main_trans_star k d)
    (by intro h; have := congr_arg (fun q : Q => q.1) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 5, 0⟩) (by execute fm 31)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, d⟩ ↦ ⟨2 * k + 1, 0, 0, d + k + 1, 0⟩) ⟨3, 1⟩
  intro ⟨k, d⟩
  refine ⟨⟨2 * k + 1, d + 2 * k⟩, ?_⟩
  show ⟨2 * k + 1, (0 : ℕ), 0, d + k + 1, 0⟩ [fm]⊢⁺
    ⟨2 * (2 * k + 1) + 1, 0, 0, (d + 2 * k) + (2 * k + 1) + 1, 0⟩
  rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring,
      show (d + 2 * k) + (2 * k + 1) + 1 = d + 4 * k + 2 from by ring]
  exact main_trans k d

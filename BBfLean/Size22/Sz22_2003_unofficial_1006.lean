import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1006: [4/15, 7/3, 99/2, 25/77, 3/35]

Vector representation:
```
 2 -1 -1  0  0
 0 -1  0  1  0
-1  2  0  0  1
 0  0  2 -1 -1
 0  1 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1006

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem drain : ∀ A, ∀ d e, ⟨A, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * A, e + A⟩ := by
  intro A; induction A with
  | zero => intro d e; simp; exists 0
  | succ A ih =>
    intro d e; step fm; step fm; step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem r4 : ∀ K, ∀ c d, ⟨(0 : ℕ), 0, c, d + K, K⟩ [fm]⊢* ⟨0, 0, c + 2 * K, d, 0⟩ := by
  intro K; induction K with
  | zero => intro c d; simp; exists 0
  | succ K ih =>
    intro c d
    rw [show d + (K + 1) = d + K + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem even_chain : ∀ j, ∀ a d e,
    ⟨a, (2 : ℕ), 2 + 2 * j, d, e⟩ [fm]⊢* ⟨a + 4 + 3 * j, 0, 0, d, e + j⟩ := by
  intro j; induction j with
  | zero => intro a d e; simp; step fm; step fm; finish
  | succ j ih =>
    intro a d e
    rw [show 2 + 2 * (j + 1) = (2 + 2 * j) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) d (e + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem odd_chain : ∀ k, ∀ a d e,
    ⟨a, (2 : ℕ), 2 * k + 1, d, e⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, d + 1, e + k⟩ := by
  intro k; induction k with
  | zero => intro a d e; simp; step fm; step fm; finish
  | succ k ih =>
    intro a d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) d (e + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem trans_c0_star (d : ℕ) :
    ⟨(0 : ℕ), 0, 2, d + 1, 0⟩ [fm]⊢* ⟨0, 0, 4, d + 2, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain 1 (d + 2) 1)
  have := r4 2 0 (d + 2)
  rw [show (0 : ℕ) + 2 * 2 = 4 from by ring,
      show d + 2 + 2 = d + 4 from by ring] at this
  exact this

theorem trans_even_star (k d : ℕ) :
    ⟨(0 : ℕ), 0, 2 * k + 4, d + 1, 0⟩ [fm]⊢* ⟨0, 0, 8 * k + 12, d + 2 * k + 4, 0⟩ := by
  rw [show 2 * k + 4 = (2 + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  have h1 := even_chain k 1 d 1
  rw [show (1 : ℕ) + 4 + 3 * k = 5 + 3 * k from by ring,
      show (1 : ℕ) + k = 1 + k from rfl] at h1
  apply stepStar_trans h1
  have h2 := drain (5 + 3 * k) d (1 + k)
  rw [show d + 2 * (5 + 3 * k) = d + 6 * k + 10 from by ring,
      show 1 + k + (5 + 3 * k) = 4 * k + 6 from by ring] at h2
  apply stepStar_trans h2
  have h3 := r4 (4 * k + 6) 0 (d + 2 * k + 4)
  rw [show (0 : ℕ) + 2 * (4 * k + 6) = 8 * k + 12 from by ring,
      show d + 2 * k + 4 + (4 * k + 6) = d + 6 * k + 10 from by ring] at h3
  exact h3

theorem trans_odd_star (k d : ℕ) :
    ⟨(0 : ℕ), 0, 2 * k + 3, d + 1, 0⟩ [fm]⊢* ⟨0, 0, 8 * k + 8, d + 2 * k + 3, 0⟩ := by
  rw [show 2 * k + 3 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm
  have h1 := odd_chain k 1 d 1
  rw [show (1 : ℕ) + 3 * k + 2 = 3 * k + 3 from by ring,
      show (1 : ℕ) + k = 1 + k from rfl] at h1
  apply stepStar_trans h1
  have h2 := drain (3 * k + 3) (d + 1) (1 + k)
  rw [show d + 1 + 2 * (3 * k + 3) = d + 6 * k + 7 from by ring,
      show 1 + k + (3 * k + 3) = 4 * k + 4 from by ring] at h2
  apply stepStar_trans h2
  have h3 := r4 (4 * k + 4) 0 (d + 2 * k + 3)
  rw [show (0 : ℕ) + 2 * (4 * k + 4) = 8 * k + 8 from by ring,
      show d + 2 * k + 3 + (4 * k + 4) = d + 6 * k + 7 from by ring] at h3
  exact h3

theorem main_trans (c d : ℕ) :
    ⟨(0 : ℕ), 0, c + 2, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * c + 4, d + c + 2, 0⟩ := by
  rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rcases k with _ | k
    · simp only [Nat.zero_add]
      exact stepStar_stepPlus (trans_c0_star d)
        (by intro h; have := congr_arg (fun q : Q => q.2.2.1) h; simp at this)
    · -- goal has c = (k+1) + (k+1), need to show ⊢⁺ with 2*(k+1)
      rw [show (k + 1) + (k + 1) + 2 = 2 * k + 4 from by ring,
          show 4 * ((k + 1) + (k + 1)) + 4 = 8 * k + 12 from by ring,
          show d + ((k + 1) + (k + 1)) + 2 = d + 2 * k + 4 from by ring]
      exact stepStar_stepPlus (trans_even_star k d)
        (by intro h; have := congr_arg (fun q : Q => q.2.2.1) h; simp at this; omega)
  · subst hk
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 4 * (2 * k + 1) + 4 = 8 * k + 8 from by ring,
        show d + (2 * k + 1) + 2 = d + 2 * k + 3 from by ring]
    exact stepStar_stepPlus (trans_odd_star k d)
      (by intro h; have := congr_arg (fun q : Q => q.2.2.1) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c + 2, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨c, d⟩; exact ⟨⟨4 * c + 2, d + c + 1⟩, main_trans c d⟩

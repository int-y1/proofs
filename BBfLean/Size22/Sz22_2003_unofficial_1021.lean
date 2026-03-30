import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1021: [4/15, 99/14, 275/2, 7/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1021

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; apply stepStar_trans (ih a (c + 2) (e + 1)); ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c d (e + 1)); ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b e,
    ⟨a + k, b, (0 : ℕ), k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; apply stepStar_trans (ih a (b + 2) (e + 1)); ring_nf; finish

theorem convert_lemma : ∀ b, ∀ a e,
    ⟨a + 1, b, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, 0, e + a + 2 * b + 1⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  match b with
  | 0 =>
    have := r3_chain (a + 1) 0 0 e
    rw [show (0 : ℕ) + (a + 1) = a + 1 from by ring,
        show (0 : ℕ) + 2 * (a + 1) = 2 * a + 2 from by ring,
        show e + (a + 1) = e + a + 1 from by ring] at this
    rw [show 2 * a + 3 * 0 + 2 = 2 * a + 2 from by ring,
        show e + a + 2 * 0 + 1 = e + a + 1 from by ring]
    exact this
  | 1 =>
    rw [show 2 * a + 3 * 1 + 2 = 2 * a + 5 from by ring,
        show e + a + 2 * 1 + 1 = e + a + 3 from by ring]
    step fm; step fm
    have := r3_chain (a + 2) 0 1 (e + 1)
    rw [show (0 : ℕ) + (a + 2) = a + 2 from by ring,
        show (1 : ℕ) + 2 * (a + 2) = 2 * a + 5 from by ring,
        show e + 1 + (a + 2) = e + a + 3 from by ring] at this
    exact this
  | b + 2 =>
    rw [show 2 * a + 3 * (b + 2) + 2 = 2 * (a + 3) + 3 * b + 2 from by ring,
        show e + a + 2 * (b + 2) + 1 = (e + 1) + (a + 3) + 2 * b + 1 from by ring]
    step fm; step fm; step fm
    exact ih b (by omega) (a + 3) (e + 1)

theorem main_trans_ge (k f : ℕ) :
    ⟨(0 : ℕ), 0, 2 * f + k + 1, 0, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, k + 6 * f + 4, 0, 4 * f + 2⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 2 * f + k + 1, 0, f + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * f + k + 1, f + 1, 0⟩ := by
    have := r4_chain (f + 1) (2 * f + k + 1) 0
    rw [show (0 : ℕ) + (f + 1) = f + 1 from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * f + k + 1, f + 1, 0⟩ [fm]⊢⁺
      ⟨2, 0, 2 * f + k, f, 0⟩ := by
    rw [show 2 * f + k + 1 = (2 * f + k) + 1 from by ring,
        show f + 1 = f + 1 from rfl]
    step fm; step fm; finish
  have h3 : ⟨(2 : ℕ), 0, 2 * f + k, f, 0⟩ [fm]⊢*
      ⟨3 * f + 2, 0, k, 0, f⟩ := by
    have := r2r1r1_chain f 1 k 0 0
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show k + 2 * f = 2 * f + k from by ring,
        show (1 : ℕ) + 3 * f + 1 = 3 * f + 2 from by ring,
        show (0 : ℕ) + f = f from by ring] at this; exact this
  have h4 : ⟨3 * f + 2, (0 : ℕ), k, 0, f⟩ [fm]⊢*
      ⟨0, 0, k + 6 * f + 4, 0, 4 * f + 2⟩ := by
    have := r3_chain (3 * f + 2) 0 k f
    rw [show (0 : ℕ) + (3 * f + 2) = 3 * f + 2 from by ring,
        show k + 2 * (3 * f + 2) = k + 6 * f + 4 from by ring,
        show f + (3 * f + 2) = 4 * f + 2 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem main_trans_B1 (n t : ℕ) :
    ⟨(0 : ℕ), 0, 2 * n + 2 * t + 4, 0, n + 2 * t + 3⟩ [fm]⊢⁺
    ⟨0, 0, 6 * n + 10 * t + 15, 0, 4 * n + 8 * t + 10⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 2 * n + 2 * t + 4, 0, n + 2 * t + 3⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 2 * t + 4, n + 2 * t + 3, 0⟩ := by
    have := r4_chain (n + 2 * t + 3) (2 * n + 2 * t + 4) 0
    rw [show (0 : ℕ) + (n + 2 * t + 3) = n + 2 * t + 3 from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * n + 2 * t + 4, n + 2 * t + 3, 0⟩ [fm]⊢⁺
      ⟨2, 0, 2 * n + 2 * t + 3, n + 2 * t + 2, 0⟩ := by
    rw [show 2 * n + 2 * t + 4 = (2 * n + 2 * t + 3) + 1 from by ring,
        show n + 2 * t + 3 = (n + 2 * t + 2) + 1 from by ring]
    step fm; step fm; finish
  have h3 : ⟨(2 : ℕ), 0, 2 * n + 2 * t + 3, n + 2 * t + 2, 0⟩ [fm]⊢*
      ⟨3 * n + 3 * t + 5, 0, 1, t + 1, n + t + 1⟩ := by
    have := r2r1r1_chain (n + t + 1) 1 1 (t + 1) 0
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show (1 : ℕ) + 2 * (n + t + 1) = 2 * n + 2 * t + 3 from by ring,
        show (t + 1) + (n + t + 1) = n + 2 * t + 2 from by ring,
        show (1 : ℕ) + 3 * (n + t + 1) + 1 = 3 * n + 3 * t + 5 from by ring,
        show (0 : ℕ) + (n + t + 1) = n + t + 1 from by ring] at this; exact this
  have h4 : ⟨3 * n + 3 * t + 5, (0 : ℕ), 1, t + 1, n + t + 1⟩ [fm]⊢*
      ⟨3 * n + 3 * t + 6, 1, 0, t, n + t + 2⟩ := by
    rw [show 3 * n + 3 * t + 5 = (3 * n + 3 * t + 4) + 1 from by ring,
        show t + 1 = t + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show 3 * n + 3 * t + 6 = (3 * n + 3 * t + 4) + 2 from by ring,
        show n + t + 2 = (n + t + 1) + 1 from by ring]
    step fm; finish
  have h5 : ⟨3 * n + 3 * t + 6, (1 : ℕ), 0, t, n + t + 2⟩ [fm]⊢*
      ⟨3 * n + 2 * t + 6, 2 * t + 1, 0, 0, n + 2 * t + 2⟩ := by
    have := r2_chain t (3 * n + 2 * t + 6) 1 (n + t + 2)
    rw [show (3 * n + 2 * t + 6) + t = 3 * n + 3 * t + 6 from by ring,
        show (1 : ℕ) + 2 * t = 2 * t + 1 from by ring,
        show (n + t + 2) + t = n + 2 * t + 2 from by ring] at this; exact this
  have h6 : ⟨3 * n + 2 * t + 6, 2 * t + 1, (0 : ℕ), 0, n + 2 * t + 2⟩ [fm]⊢*
      ⟨0, 0, 6 * n + 10 * t + 15, 0, 4 * n + 8 * t + 10⟩ := by
    have := convert_lemma (2 * t + 1) (3 * n + 2 * t + 5) (n + 2 * t + 2)
    rw [show (3 * n + 2 * t + 5) + 1 = 3 * n + 2 * t + 6 from by ring,
        show 2 * (3 * n + 2 * t + 5) + 3 * (2 * t + 1) + 2 = 6 * n + 10 * t + 15 from by ring,
        show (n + 2 * t + 2) + (3 * n + 2 * t + 5) + 2 * (2 * t + 1) + 1 =
          4 * n + 8 * t + 10 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem main_trans_B2 (n t : ℕ) :
    ⟨(0 : ℕ), 0, 2 * n + 2 * t + 5, 0, n + 2 * t + 4⟩ [fm]⊢⁺
    ⟨0, 0, 6 * n + 10 * t + 20, 0, 4 * n + 8 * t + 14⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 2 * n + 2 * t + 5, 0, n + 2 * t + 4⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 2 * t + 5, n + 2 * t + 4, 0⟩ := by
    have := r4_chain (n + 2 * t + 4) (2 * n + 2 * t + 5) 0
    rw [show (0 : ℕ) + (n + 2 * t + 4) = n + 2 * t + 4 from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * n + 2 * t + 5, n + 2 * t + 4, 0⟩ [fm]⊢⁺
      ⟨2, 0, 2 * n + 2 * t + 4, n + 2 * t + 3, 0⟩ := by
    rw [show 2 * n + 2 * t + 5 = (2 * n + 2 * t + 4) + 1 from by ring,
        show n + 2 * t + 4 = (n + 2 * t + 3) + 1 from by ring]
    step fm; step fm; finish
  have h3 : ⟨(2 : ℕ), 0, 2 * n + 2 * t + 4, n + 2 * t + 3, 0⟩ [fm]⊢*
      ⟨3 * n + 3 * t + 8, 0, 0, t + 1, n + t + 2⟩ := by
    have := r2r1r1_chain (n + t + 2) 1 0 (t + 1) 0
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show (0 : ℕ) + 2 * (n + t + 2) = 2 * n + 2 * t + 4 from by ring,
        show (t + 1) + (n + t + 2) = n + 2 * t + 3 from by ring,
        show (1 : ℕ) + 3 * (n + t + 2) + 1 = 3 * n + 3 * t + 8 from by ring,
        show (0 : ℕ) + (n + t + 2) = n + t + 2 from by ring] at this; exact this
  have h4 : ⟨3 * n + 3 * t + 8, (0 : ℕ), 0, t + 1, n + t + 2⟩ [fm]⊢*
      ⟨3 * n + 2 * t + 7, 2 * t + 2, 0, 0, n + 2 * t + 3⟩ := by
    have := r2_chain (t + 1) (3 * n + 2 * t + 7) 0 (n + t + 2)
    rw [show (3 * n + 2 * t + 7) + (t + 1) = 3 * n + 3 * t + 8 from by ring,
        show (0 : ℕ) + 2 * (t + 1) = 2 * t + 2 from by ring,
        show (n + t + 2) + (t + 1) = n + 2 * t + 3 from by ring] at this; exact this
  have h5 : ⟨3 * n + 2 * t + 7, 2 * t + 2, (0 : ℕ), 0, n + 2 * t + 3⟩ [fm]⊢*
      ⟨0, 0, 6 * n + 10 * t + 20, 0, 4 * n + 8 * t + 14⟩ := by
    have := convert_lemma (2 * t + 2) (3 * n + 2 * t + 6) (n + 2 * t + 3)
    rw [show (3 * n + 2 * t + 6) + 1 = 3 * n + 2 * t + 7 from by ring,
        show 2 * (3 * n + 2 * t + 6) + 3 * (2 * t + 2) + 2 = 6 * n + 10 * t + 20 from by ring,
        show (n + 2 * t + 3) + (3 * n + 2 * t + 6) + 2 * (2 * t + 2) + 1 =
          4 * n + 8 * t + 14 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, f + n + 2, 0, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  refine ⟨⟨f + n + 2, 4 * f + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, f + n + 2, 0, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, (4 * f + 1) + (f + n + 2) + 2, 0, (4 * f + 1) + 1⟩
  rw [show (4 * f + 1) + (f + n + 2) + 2 = 5 * f + n + 5 from by ring,
      show (4 * f + 1) + 1 = 4 * f + 2 from by ring]
  rcases le_or_gt f (n + 1) with hle | hlt
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [show f + n + 2 = 2 * f + k + 1 from by omega,
        show 5 * f + n + 5 = k + 6 * f + 4 from by omega]
    exact main_trans_ge k f
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le (show n + 2 ≤ f by omega)
    rcases Nat.even_or_odd s with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [show f + n + 2 = 2 * n + 2 * t + 4 from by omega,
          show f + 1 = n + 2 * t + 3 from by omega,
          show 5 * f + n + 5 = 6 * n + 10 * t + 15 from by omega,
          show 4 * f + 2 = 4 * n + 8 * t + 10 from by omega]
      exact main_trans_B1 n t
    · rw [show f + n + 2 = 2 * n + 2 * t + 5 from by omega,
          show f + 1 = n + 2 * t + 4 from by omega,
          show 5 * f + n + 5 = 6 * n + 10 * t + 20 from by omega,
          show 4 * f + 2 = 4 * n + 8 * t + 14 from by omega]
      exact main_trans_B2 n t

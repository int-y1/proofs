import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1804: [9/10, 55/147, 22/3, 7/11, 15/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -2  1
 1 -1  0  0  1
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1804

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+2, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3_chain_d0 : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem r3_chain_d1 : ∀ k, ⟨a, k, 0, 1, e⟩ [fm]⊢* ⟨a + k, 0, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem r2_r1_chain : ∀ k, ⟨a + k, b + 1, 0, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨0, b + k, c, d + 2 * k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r3_r1_pairs_d0 : ∀ k, ⟨0, b + 1, k + 1, 0, e⟩ [fm]⊢* ⟨0, b + k + 2, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing b e
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

theorem r3_r1_pairs_d1 : ∀ k, ⟨0, b + 1, k + 1, 1, e⟩ [fm]⊢* ⟨0, b + k + 2, 0, 1, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing b e
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

theorem trans_n_even (p : ℕ) :
    ⟨2 * p + 2, 0, 0, 6 * p + 3, 0⟩ [fm]⊢⁺ ⟨2 * p + 3, 0, 0, 6 * p + 6, 0⟩ := by
  step fm; step fm
  rw [show 6 * p + 2 + 1 = 6 * p + 3 from by ring,
      show 2 * p = 0 + 2 * p from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show 6 * p + 3 = (2 * p + 3) + 2 * (2 * p) from by ring]
  apply stepStar_trans (r2_r1_chain (2 * p) (a := 0) (b := 2) (d := 2 * p + 3) (e := 0))
  rw [show 2 + 1 + 2 * p = 2 * p + 3 from by ring,
      show 0 + 2 * p = 2 * p from by ring]
  show ⟨0, 2 * p + 3, 0, 2 * p + 3, 2 * p⟩ [fm]⊢* ⟨2 * p + 3, 0, 0, 6 * p + 6, 0⟩
  rw [show (2 * p + 3 : ℕ) = (p + 2) + (p + 1) from by omega]
  nth_rewrite 2 [show (p + 2 + (p + 1) : ℕ) = 1 + 2 * (p + 1) from by omega]
  apply stepStar_trans (r2_chain (p + 1) (b := p + 2) (c := 0) (d := 1) (e := 2 * p))
  rw [show 0 + (p + 1) = p + 1 from by ring,
      show 2 * p + (p + 1) = 3 * p + 1 from by ring,
      show (p + 2 : ℕ) = (p + 1) + 1 from by ring]
  apply stepStar_trans (r3_r1_pairs_d1 p (b := p + 1) (e := 3 * p + 1))
  rw [show p + 1 + p + 2 = 2 * p + 3 from by ring,
      show 3 * p + 1 + p + 1 = 4 * p + 2 from by ring]
  rw [show p + 1 + 1 + (p + 1) = 2 * p + 3 from by ring]
  apply stepStar_trans (r3_chain_d1 (2 * p + 3) (a := 0) (e := 4 * p + 2))
  rw [show 0 + (2 * p + 3) = 2 * p + 3 from by ring,
      show 4 * p + 2 + (2 * p + 3) = 6 * p + 5 from by ring]
  apply stepStar_trans (e_to_d (6 * p + 5) (d := 1))
  ring_nf; finish

theorem trans_n_odd (p : ℕ) :
    ⟨2 * p + 3, 0, 0, 6 * p + 6, 0⟩ [fm]⊢⁺ ⟨2 * p + 4, 0, 0, 6 * p + 9, 0⟩ := by
  step fm; step fm
  rw [show 6 * p + 5 + 1 = 6 * p + 6 from by ring,
      show 2 * p + 1 = 0 + (2 * p + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show 6 * p + 6 = (2 * p + 4) + 2 * (2 * p + 1) from by ring]
  apply stepStar_trans (r2_r1_chain (2 * p + 1) (a := 0) (b := 2) (d := 2 * p + 4) (e := 0))
  rw [show 2 + 1 + (2 * p + 1) = 2 * p + 4 from by ring,
      show 0 + (2 * p + 1) = 2 * p + 1 from by ring]
  show ⟨0, 2 * p + 4, 0, 2 * p + 4, 2 * p + 1⟩ [fm]⊢* ⟨2 * p + 4, 0, 0, 6 * p + 9, 0⟩
  rw [show (2 * p + 4 : ℕ) = (p + 2) + (p + 2) from by omega]
  nth_rewrite 2 [show (p + 2 + (p + 2) : ℕ) = 0 + 2 * (p + 2) from by omega]
  apply stepStar_trans (r2_chain (p + 2) (b := p + 2) (c := 0) (d := 0) (e := 2 * p + 1))
  rw [show 0 + (p + 2) = p + 2 from by ring,
      show 2 * p + 1 + (p + 2) = 3 * p + 3 from by ring,
      show (p + 2 : ℕ) = (p + 1) + 1 from by ring]
  apply stepStar_trans (r3_r1_pairs_d0 (p + 1) (b := p + 1) (e := 3 * p + 3))
  rw [show p + 1 + (p + 1) + 2 = 2 * p + 4 from by ring,
      show 3 * p + 3 + (p + 1) + 1 = 4 * p + 5 from by ring,
      show p + 2 + (p + 2) = 2 * p + 4 from by ring]
  apply stepStar_trans (r3_chain_d0 (2 * p + 4) (a := 0) (e := 4 * p + 5))
  rw [show 0 + (2 * p + 4) = 2 * p + 4 from by ring,
      show 4 * p + 5 + (2 * p + 4) = 6 * p + 9 from by ring]
  apply stepStar_trans (e_to_d (6 * p + 9) (d := 0))
  ring_nf; finish

theorem main_trans : ∀ n, ⟨n + 2, 0, 0, 3 * n + 3, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 3 * n + 6, 0⟩ := by
  intro n
  rcases Nat.even_or_odd n with ⟨p, hp⟩ | ⟨p, hp⟩
  · subst hp
    show ⟨p + p + 2, 0, 0, 3 * (p + p) + 3, 0⟩ [fm]⊢⁺ ⟨p + p + 3, 0, 0, 3 * (p + p) + 6, 0⟩
    rw [show p + p + 2 = 2 * p + 2 from by ring,
        show 3 * (p + p) + 3 = 6 * p + 3 from by ring,
        show p + p + 3 = 2 * p + 3 from by ring,
        show 3 * (p + p) + 6 = 6 * p + 6 from by ring]
    exact trans_n_even p
  · subst hp
    show ⟨2 * p + 1 + 2, 0, 0, 3 * (2 * p + 1) + 3, 0⟩ [fm]⊢⁺
         ⟨2 * p + 1 + 3, 0, 0, 3 * (2 * p + 1) + 6, 0⟩
    rw [show 2 * p + 1 + 2 = 2 * p + 3 from by ring,
        show 3 * (2 * p + 1) + 3 = 6 * p + 6 from by ring,
        show 2 * p + 1 + 3 = 2 * p + 4 from by ring,
        show 3 * (2 * p + 1) + 6 = 6 * p + 9 from by ring]
    exact trans_n_odd p

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 3 * n + 3, 0⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 3 * (n + 1) + 3 = 3 * n + 6 from by ring]
  exact main_trans n

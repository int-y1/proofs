import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1832: [9/10, 77/2, 4/21, 25/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  1
 2 -1  0 -1  0
 0  0  2 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1832

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

theorem open_round : ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢* ⟨0, b + 5, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem open_chain : ∀ k, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b) (c := c + 3) (e := e + 1))
    apply stepStar_trans open_round
    ring_nf; finish

theorem tail_c2 : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨0, b + 3, 0, 1, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem tail_c1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, 1, e⟩ := by
  step fm; step fm
  ring_nf; finish

theorem tail_c0 : ⟨0, b, 0, 0, e + 1⟩ [fm]⊢* ⟨0, b, 0, 2, e + 1⟩ := by
  step fm; step fm
  ring_nf; finish

theorem drain_step : ⟨0, b + 1, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 2, e + 2⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

theorem drain : ∀ k, ⟨0, k, 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · apply stepStar_trans (drain_step (b := k) (d := d) (e := e))
    apply stepStar_trans (ih (d := d + 1) (e := e + 2))
    ring_nf; finish

private theorem d_to_c' (k : ℕ) :
    ⟨0, 0, 2, 3 * k, e⟩ [fm]⊢* ⟨0, 0, 6 * k + 2, 0, e⟩ := by
  rw [show (3 : ℕ) * k = 0 + 3 * k from by ring,
      show 6 * k + 2 = 2 + 2 * (3 * k) from by ring]
  exact d_to_c (3 * k) (c := 2) (d := 0) (e := e)

private theorem d_to_c'' (k : ℕ) :
    ⟨0, 0, 2, 3 * k + 1, e⟩ [fm]⊢* ⟨0, 0, 6 * k + 4, 0, e⟩ := by
  rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring,
      show 6 * k + 4 = 2 + 2 * (3 * k + 1) from by ring]
  exact d_to_c (3 * k + 1) (c := 2) (d := 0) (e := e)

private theorem d_to_c''' (k : ℕ) :
    ⟨0, 0, 2, 3 * k + 2, e⟩ [fm]⊢* ⟨0, 0, 6 * k + 6, 0, e⟩ := by
  rw [show 3 * k + 2 = 0 + (3 * k + 2) from by ring,
      show 6 * k + 6 = 2 + 2 * (3 * k + 2) from by ring]
  exact d_to_c (3 * k + 2) (c := 2) (d := 0) (e := e)

private theorem drain' (k F : ℕ) :
    ⟨0, 10 * k + 3, 0, 1, F + 1⟩ [fm]⊢* ⟨0, 0, 0, 10 * k + 4, F + 20 * k + 7⟩ := by
  have h := drain (10 * k + 3) (d := 0) (e := F + 1)
  rw [show 0 + (10 * k + 3) + 1 = 10 * k + 4 from by ring,
      show F + 1 + 2 * (10 * k + 3) = F + 20 * k + 7 from by ring] at h
  exact h

private theorem drain'' (k F : ℕ) :
    ⟨0, 10 * k + 7, 0, 1, F⟩ [fm]⊢* ⟨0, 0, 0, 10 * k + 8, F + 20 * k + 14⟩ := by
  have h := drain (10 * k + 7) (d := 0) (e := F)
  rw [show 0 + (10 * k + 7) + 1 = 10 * k + 8 from by ring,
      show F + 2 * (10 * k + 7) = F + 20 * k + 14 from by ring] at h
  exact h

private theorem drain''' (k F : ℕ) :
    ⟨0, 10 * k + 10, 0, 2, F + 1⟩ [fm]⊢* ⟨0, 0, 0, 10 * k + 12, F + 20 * k + 21⟩ := by
  have h := drain (10 * k + 10) (d := 1) (e := F + 1)
  rw [show 1 + (10 * k + 10) + 1 = 10 * k + 12 from by ring,
      show F + 1 + 2 * (10 * k + 10) = F + 20 * k + 21 from by ring] at h
  exact h

theorem case_mod1 :
    ⟨0, 0, 0, 3 * k + 1, F + 2 * k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 10 * k + 4, F + 20 * k + 7⟩ := by
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (d_to_c' k (e := F + 2 * k + 1))
  rw [show 6 * k + 2 = 2 + 3 * (2 * k) from by ring,
      show F + 2 * k + 1 = (F + 1) + 2 * k from by ring]
  apply stepStar_trans (open_chain (2 * k) (b := 0) (c := 2) (e := F + 1))
  rw [show 0 + 5 * (2 * k) = 10 * k from by ring]
  apply stepStar_trans tail_c2
  exact drain' k F

theorem case_mod2 :
    ⟨0, 0, 0, 3 * k + 2, F + 2 * k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 10 * k + 8, F + 20 * k + 14⟩ := by
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (d_to_c'' k (e := F + 2 * k + 2))
  rw [show 6 * k + 4 = 1 + 3 * (2 * k + 1) from by ring,
      show F + 2 * k + 2 = (F + 1) + (2 * k + 1) from by ring]
  apply stepStar_trans (open_chain (2 * k + 1) (b := 0) (c := 1) (e := F + 1))
  rw [show 0 + 5 * (2 * k + 1) = 10 * k + 5 from by ring]
  apply stepStar_trans (tail_c1 (b := 10 * k + 5) (e := F))
  exact drain'' k F

theorem case_mod0 :
    ⟨0, 0, 0, 3 * k + 3, F + 2 * k + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 10 * k + 12, F + 20 * k + 21⟩ := by
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (d_to_c''' k (e := F + 2 * k + 3))
  rw [show 6 * k + 6 = 0 + 3 * (2 * k + 2) from by ring,
      show F + 2 * k + 3 = (F + 1) + (2 * k + 2) from by ring]
  apply stepStar_trans (open_chain (2 * k + 2) (b := 0) (c := 0) (e := F + 1))
  rw [show 0 + 5 * (2 * k + 2) = 10 * k + 10 from by ring]
  apply stepStar_trans (tail_c0 (b := 10 * k + 10) (e := F))
  exact drain''' k F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e⟩ ∧ e ≥ d + 1)
  · intro c ⟨d, e, hq, he⟩; subst hq
    have hmod : (d + 1) % 3 = 0 ∨ (d + 1) % 3 = 1 ∨ (d + 1) % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · obtain ⟨k, hk⟩ : ∃ k, d + 1 = 3 * k + 3 := ⟨(d + 1) / 3 - 1, by omega⟩
      rw [show d + 1 = 3 * k + 3 from hk,
          show e = (e - 2 * k - 3) + 2 * k + 3 from by omega]
      refine ⟨⟨0, 0, 0, 10 * k + 12, (e - 2 * k - 3) + 20 * k + 21⟩,
        ⟨10 * k + 11, (e - 2 * k - 3) + 20 * k + 21, ?_, by omega⟩,
        case_mod0⟩
      simp [Q]
    · obtain ⟨k, hk⟩ : ∃ k, d + 1 = 3 * k + 1 := ⟨(d + 1) / 3, by omega⟩
      rw [show d + 1 = 3 * k + 1 from hk,
          show e = (e - 2 * k - 1) + 2 * k + 1 from by omega]
      refine ⟨⟨0, 0, 0, 10 * k + 4, (e - 2 * k - 1) + 20 * k + 7⟩,
        ⟨10 * k + 3, (e - 2 * k - 1) + 20 * k + 7, ?_, by omega⟩,
        case_mod1⟩
      simp [Q]
    · obtain ⟨k, hk⟩ : ∃ k, d + 1 = 3 * k + 2 := ⟨(d + 1 - 2) / 3, by omega⟩
      rw [show d + 1 = 3 * k + 2 from hk,
          show e = (e - 2 * k - 2) + 2 * k + 2 from by omega]
      refine ⟨⟨0, 0, 0, 10 * k + 8, (e - 2 * k - 2) + 20 * k + 14⟩,
        ⟨10 * k + 7, (e - 2 * k - 2) + 20 * k + 14, ?_, by omega⟩,
        case_mod2⟩
      simp [Q]
  · exact ⟨0, 1, rfl, by omega⟩

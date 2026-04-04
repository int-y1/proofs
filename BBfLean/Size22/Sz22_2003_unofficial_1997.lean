import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1997: [99/35, 5/6, 5929/3, 2/11, 3/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 0 -1  0  2  2
 1  0  0  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1997

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_a : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a + k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a := a + 1)); ring_nf; finish

theorem b_drain : ∀ k, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b := b) (d := d + 2) (e := e + 2)); ring_nf; finish

theorem r1_drain : ∀ k, ⟨a, b, c + k, d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b := b + 2)); ring_nf; finish

theorem r2_drain_0 : ∀ k, ∀ b c e, ⟨k, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    have h1 : ⟨k + 1, (b + k) + 1, c, 0, e⟩ [fm]⊢ ⟨k, b + k, c + 1, 0, e⟩ := by simp [fm]
    rw [show c + (k + 1) = c + 1 + k from by ring]
    exact stepStar_trans (step_stepStar h1) (ih b (c + 1) e)

theorem spiral : ∀ k, ⟨a + k, b, 1, d + 1 + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1)); ring_nf; finish

theorem c_phase : ∀ c, ∀ b e,
    ⟨0, b + 1, c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * b + 3 * c + 2, e + 2 * b + 5 * c + 2⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro b e
  rcases c with _ | _ | c
  · rw [show b + 1 = 0 + (b + 1) from by ring]
    apply stepStar_trans (b_drain (b + 1) (b := 0) (d := 0) (e := e))
    ring_nf; finish
  · step fm
    apply stepStar_trans (r1_drain 1 (a := 0) (b := b) (c := 0) (d := 1) (e := e + 2))
    rw [show b + 2 * 1 = 0 + (b + 2) from by ring]
    apply stepStar_trans (b_drain (b + 2) (b := 0) (d := 1) (e := e + 2 + 1))
    ring_nf; finish
  · rw [show c + 2 = c + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (r1_drain 2 (a := 0) (b := b) (c := c) (d := 0) (e := e + 2))
    rw [show b + 2 * 2 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (b + 3) (e + 2 + 2))
    ring_nf; finish

theorem main_trans_le (h : a ≤ d + 1) :
    ⟨a + 2, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨3 * a + 5, 0, 0, a + d + 5, 0⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, d + 1 - a = r := ⟨d + 1 - a, rfl⟩
  have hd : d + 2 = r + 1 + a := by omega
  rw [show a + 2 = a + 1 + 1 from by ring, hd,
      show a = 0 + a from by ring,
      show r + 1 + (0 + a) = r + 1 + a from by ring]
  step fm; step fm
  apply stepStar_trans (spiral a (a := 0) (b := 0) (d := r) (e := 0))
  step fm
  rw [show 0 + a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (b_drain (a + 2) (b := 0) (d := r) (e := 0 + a + 1))
  rw [show r + 2 * (a + 2) = a + d + 5 from by omega,
      show 0 + a + 1 + 2 * (a + 2) = 0 + (3 * a + 5) from by ring,
      show 3 * (0 + a) + 5 = 0 + (3 * a + 5) from by ring,
      show 0 + a + d + 5 = a + d + 5 from by ring]
  exact e_to_a (3 * a + 5) (a := 0) (d := a + d + 5) (e := 0)

theorem main_trans_gt (h : a ≥ d + 2) (hle : a ≤ 2 * d + 3) :
    ⟨a + 2, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨3 * a + 5, 0, 0, a + d + 5, 0⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, a = d + 2 + F := ⟨a - (d + 2), by omega⟩
  rw [show (d + 2 + F) + 2 = (d + 2 + F) + 1 + 1 from by ring]
  step fm; step fm
  rw [show d + 2 + F = (F + 1) + (d + 1) from by ring,
      show d + 2 = 0 + 1 + (d + 1) from by ring]
  apply stepStar_trans (spiral (d + 1) (a := F + 1) (b := 0) (d := 0) (e := 0))
  step fm
  rw [show 0 + (d + 1) + 2 = (d + 2 - F) + (F + 1) from by omega]
  apply stepStar_trans (r2_drain_0 (F + 1) (d + 2 - F) 0 (0 + (d + 1) + 1))
  rw [show d + 2 - F = (d + 1 - F) + 1 from by omega,
      show 0 + (F + 1) = F + 1 from by ring]
  apply stepStar_trans (c_phase (F + 1) (d + 1 - F) (0 + (d + 1) + 1))
  rw [show 2 * (d + 1 - F) + 3 * (F + 1) + 2 = (d + 2 + F) + d + 5 from by omega,
      show 0 + (d + 1) + 1 + 2 * (d + 1 - F) + 5 * (F + 1) + 2 =
        0 + (3 * (d + 2 + F) + 5) from by omega,
      show 3 * (F + 1 + (d + 1)) + 5 = 0 + (3 * (d + 2 + F) + 5) from by ring,
      show F + 1 + (d + 1) + d + 5 = (d + 2 + F) + d + 5 from by ring]
  exact e_to_a (3 * (d + 2 + F) + 5) (a := 0) (d := (d + 2 + F) + d + 5) (e := 0)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d + 2, 0⟩ ∧ a ≤ 2 * d + 3)
  · intro c ⟨a, d, hq, hle⟩; subst hq
    rcases Nat.lt_or_ge a (d + 2) with h | h
    · exact ⟨⟨3 * a + 5, 0, 0, a + d + 5, 0⟩,
        ⟨3 * a + 3, a + d + 3, by ring_nf, by omega⟩, main_trans_le (by omega)⟩
    · exact ⟨⟨3 * a + 5, 0, 0, a + d + 5, 0⟩,
        ⟨3 * a + 3, a + d + 3, by ring_nf, by omega⟩, main_trans_gt h hle⟩
  · exact ⟨0, 0, rfl, by omega⟩

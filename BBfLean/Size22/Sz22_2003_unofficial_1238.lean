import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1238: [5/6, 77/2, 16/35, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 4  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1238

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+4, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem spiral_round : ⟨0, b + 5, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 4, 0, e⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  finish

theorem spiral_chain : ∀ k, ⟨0, b + 5 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 4 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show b + 5 * (k + 1) = (b + 5) + 5 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 5) (e := e + 1))
    apply stepStar_trans spiral_round
    ring_nf; finish

theorem drain_step : ⟨(0 : ℕ), 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 4, e + 4⟩ := by
  step fm; step fm; step fm; step fm; step fm
  rw [show d + 1 + 1 + 1 + 1 = d + 4 from by ring,
      show e + 1 + 1 + 1 + 1 = e + 4 from by ring]
  finish

theorem drain : ∀ c, ⟨(0 : ℕ), 0, c, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + 3 * c + 1, e + 4 * c⟩ := by
  intro c; induction' c with c ih generalizing d e
  · exists 0
  · apply stepStar_trans drain_step
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 4))
    ring_nf; finish

theorem tail_b0 : ⟨0, 0, c, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * c + 2, 4 * c + e + 1⟩ := by
  step fm; step fm
  apply stepStar_trans (drain c (d := 1) (e := e + 1))
  ring_nf; finish

theorem tail_b1 : ⟨0, 1, c, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * c + 4, 4 * c + e + 4⟩ := by
  step fm; step fm
  apply stepStar_trans (drain (c + 1) (d := 0) (e := e))
  ring_nf; finish

theorem tail_b2 : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * c + 6, 4 * c + e + 7⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  apply stepStar_trans (drain (c + 1) (d := 2) (e := e + 3))
  ring_nf; finish

theorem tail_b3 : ⟨0, 3, c, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * c + 8, 4 * c + e + 10⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  apply stepStar_trans (drain (c + 2) (d := 1) (e := e + 2))
  ring_nf; finish

theorem tail_b4 : ⟨0, 4, c, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * c + 10, 4 * c + e + 13⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  apply stepStar_trans (drain (c + 3) (d := 0) (e := e + 1))
  ring_nf; finish

private theorem trans_helper (r : ℕ) :
    ⟨0, 0, 0, 5 * k + r, E + k + 1⟩ [fm]⊢* ⟨0, r + 5 * k, 0, 0, E + 1 + k⟩ := by
  rw [show 5 * k + r = 0 + (5 * k + r) from by ring,
      show E + k + 1 = E + 1 + k from by ring,
      show r + 5 * k = 0 + (r + 5 * k) from by ring]
  rw [show 5 * k + r = r + 5 * k from by ring]
  exact d_to_b (r + 5 * k) (b := 0) (d := 0) (e := E + 1 + k)

theorem trans_r0 : ⟨0, 0, 0, 5 * k, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * k + 2, E + 16 * k + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (trans_helper 0)
  apply stepStar_stepPlus_stepPlus (spiral_chain k (b := 0) (c := 0) (e := E + 1))
  simp only [Nat.zero_add]
  apply stepPlus_stepStar_stepPlus (tail_b0 (c := 4 * k) (e := E))
  ring_nf; finish

theorem trans_r1 : ⟨0, 0, 0, 5 * k + 1, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * k + 4, E + 16 * k + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (trans_helper 1)
  apply stepStar_stepPlus_stepPlus (spiral_chain k (b := 1) (c := 0) (e := E + 1))
  simp only [Nat.zero_add]
  apply stepPlus_stepStar_stepPlus (tail_b1 (c := 4 * k) (e := E))
  ring_nf; finish

theorem trans_r2 : ⟨0, 0, 0, 5 * k + 2, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * k + 6, E + 16 * k + 7⟩ := by
  apply stepStar_stepPlus_stepPlus (trans_helper 2)
  apply stepStar_stepPlus_stepPlus (spiral_chain k (b := 2) (c := 0) (e := E + 1))
  simp only [Nat.zero_add]
  apply stepPlus_stepStar_stepPlus (tail_b2 (c := 4 * k) (e := E))
  ring_nf; finish

theorem trans_r3 : ⟨0, 0, 0, 5 * k + 3, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * k + 8, E + 16 * k + 10⟩ := by
  apply stepStar_stepPlus_stepPlus (trans_helper 3)
  apply stepStar_stepPlus_stepPlus (spiral_chain k (b := 3) (c := 0) (e := E + 1))
  simp only [Nat.zero_add]
  apply stepPlus_stepStar_stepPlus (tail_b3 (c := 4 * k) (e := E))
  ring_nf; finish

theorem trans_r4 : ⟨0, 0, 0, 5 * k + 4, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * k + 10, E + 16 * k + 13⟩ := by
  apply stepStar_stepPlus_stepPlus (trans_helper 4)
  apply stepStar_stepPlus_stepPlus (spiral_chain k (b := 4) (c := 0) (e := E + 1))
  simp only [Nat.zero_add]
  apply stepPlus_stepStar_stepPlus (tail_b4 (c := 4 * k) (e := E))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d)
  · intro q ⟨d, e, hq, hd, he⟩; subst hq
    have hk : e ≥ d / 5 + 1 := by omega
    obtain ⟨k, r, hkr, hr5⟩ : ∃ k r, d = 5 * k + r ∧ r < 5 :=
      ⟨d / 5, d % 5, (Nat.div_add_mod d 5).symm, Nat.mod_lt _ (by omega)⟩
    obtain ⟨E, hE⟩ : ∃ E, e = E + k + 1 := ⟨e - k - 1, by omega⟩
    subst hkr; subst hE
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 from by omega) with
      rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, ⟨12 * k + 2, E + 16 * k + 1, rfl, by omega, by omega⟩, trans_r0⟩
    · exact ⟨_, ⟨12 * k + 4, E + 16 * k + 4, rfl, by omega, by omega⟩, trans_r1⟩
    · exact ⟨_, ⟨12 * k + 6, E + 16 * k + 7, rfl, by omega, by omega⟩, trans_r2⟩
    · exact ⟨_, ⟨12 * k + 8, E + 16 * k + 10, rfl, by omega, by omega⟩, trans_r3⟩
    · exact ⟨_, ⟨12 * k + 10, E + 16 * k + 13, rfl, by omega, by omega⟩, trans_r4⟩
  · exact ⟨1, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1238

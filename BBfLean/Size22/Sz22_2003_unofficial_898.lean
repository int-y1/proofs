import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #898: [4/15, 27/14, 55/2, 7/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  3  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_898

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1) (e := e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c) (d := d + 1) (e := e))
    ring_nf; finish

theorem a_to_de (A E : ℕ) : ⟨A, 0, 0, 0, E⟩ [fm]⊢* ⟨0, 0, 0, A, A + E⟩ := by
  have h1 := r3_chain A (a := 0) (c := 0) (e := E)
  simp at h1
  have h2 := r4_chain A (c := 0) (d := 0) (e := A + E)
  simp at h2
  rw [show (E : ℕ) + A = A + E from by ring] at h1
  exact stepStar_trans h1 h2

theorem drain_round_b0 : ⟨0, 0, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, 8, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem drain_round_b1 : ⟨0, b + 1, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, b + 9, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem drain_rem : ∀ k b, ⟨0, b, 0, 3 * k + r, e + k⟩ [fm]⊢* ⟨0, b + 8 * k, 0, r, e⟩ := by
  intro k; induction' k with k ih generalizing e
  · intro b; simp; finish
  · intro b
    rw [show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    rcases b with _ | b
    · apply stepStar_trans (drain_round_b0 (d := 3 * k + r) (e := e + k))
      apply stepStar_trans (ih (b := 8) (e := e))
      ring_nf; finish
    · apply stepStar_trans (drain_round_b1 (b := b) (d := 3 * k + r) (e := e + k))
      apply stepStar_trans (ih (b := b + 9) (e := e))
      ring_nf; finish

theorem d_tail_1_b0 : ⟨0, 0, 0, 1, e + 1⟩ [fm]⊢* ⟨2, 2, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem d_tail_1_b1 : ⟨0, b + 1, 0, 1, e + 1⟩ [fm]⊢* ⟨2, b + 3, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem d_tail_1 : ⟨0, b, 0, 1, e + 1⟩ [fm]⊢* ⟨2, b + 2, 0, 0, e⟩ := by
  rcases b with _ | b
  · exact d_tail_1_b0
  · apply stepStar_trans (d_tail_1_b1 (b := b) (e := e))
    rw [show b + 3 = (b + 1) + 2 from by ring]; finish

theorem d_tail_2_b0 : ⟨0, 0, 0, 2, e + 1⟩ [fm]⊢* ⟨1, 5, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem d_tail_2_b1 : ⟨0, b + 1, 0, 2, e + 1⟩ [fm]⊢* ⟨1, b + 6, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem d_tail_2 : ⟨0, b, 0, 2, e + 1⟩ [fm]⊢* ⟨1, b + 5, 0, 0, e⟩ := by
  rcases b with _ | b
  · exact d_tail_2_b0
  · apply stepStar_trans (d_tail_2_b1 (b := b) (e := e))
    rw [show b + 6 = (b + 1) + 5 from by ring]; finish

theorem r3r1_chain : ∀ k, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem phase4_a0 : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢* ⟨b + 3, 0, 0, 0, e + b⟩ := by
  step fm; step fm
  show ⟨2 + 1, b, 0, 0, e⟩ [fm]⊢* ⟨b + 3, 0, 0, 0, e + b⟩
  apply stepStar_trans (r3r1_chain b (a := 2) (e := e))
  ring_nf; finish

theorem phase4_a1 : ⟨1, b + 1, 0, 0, e⟩ [fm]⊢* ⟨b + 2, 0, 0, 0, e + b + 1⟩ := by
  step fm; step fm
  show ⟨1 + 1, b, 0, 0, e + 1⟩ [fm]⊢* ⟨b + 2, 0, 0, 0, e + b + 1⟩
  apply stepStar_trans (r3r1_chain b (a := 1) (e := e + 1))
  ring_nf; finish

theorem phase4_a2 : ⟨2, b + 1, 0, 0, e⟩ [fm]⊢* ⟨b + 3, 0, 0, 0, e + b + 1⟩ := by
  step fm; step fm
  show ⟨2 + 1, b, 0, 0, e + 1⟩ [fm]⊢* ⟨b + 3, 0, 0, 0, e + b + 1⟩
  apply stepStar_trans (r3r1_chain b (a := 2) (e := e + 1))
  ring_nf; finish

theorem trans_mod0 (m E : ℕ) :
    ⟨3 * (m + 1), 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * m + 10, 0, 0, 0, 10 * m + E + 8⟩ := by
  apply stepStar_stepPlus
  · apply stepStar_trans (a_to_de (3 * (m + 1)) E)
    have hd := drain_rem (r := 0) (m + 1) 0 (e := 2 * m + 2 + E)
    rw [show 2 * m + 2 + E + (m + 1) = 3 * (m + 1) + E from by ring,
        show (0 : ℕ) + 8 * (m + 1) = 8 * m + 8 from by ring,
        show 3 * (m + 1) + 0 = 3 * (m + 1) from by ring] at hd
    apply stepStar_trans hd; clear hd
    rw [show 2 * m + 2 + E = (2 * m + 1 + E) + 1 from by ring,
        show 8 * m + 8 = (8 * m + 7) + 1 from by ring]
    apply stepStar_trans (phase4_a0 (b := 8 * m + 7) (e := 2 * m + 1 + E))
    ring_nf; finish
  · simp [Q]; omega

theorem trans_mod1 (m E : ℕ) :
    ⟨3 * m + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * m + 4, 0, 0, 0, 10 * m + E + 2⟩ := by
  apply stepStar_stepPlus
  · apply stepStar_trans (a_to_de (3 * m + 1) E)
    have hd := drain_rem (r := 1) m 0 (e := 2 * m + 1 + E)
    rw [show 2 * m + 1 + E + m = 3 * m + 1 + E from by ring,
        show (0 : ℕ) + 8 * m = 8 * m from by ring] at hd
    apply stepStar_trans hd
    rw [show 2 * m + 1 + E = (2 * m + E) + 1 from by ring]
    apply stepStar_trans (d_tail_1 (b := 8 * m) (e := 2 * m + E))
    rw [show 8 * m + 2 = (8 * m + 1) + 1 from by ring]
    apply stepStar_trans (phase4_a2 (b := 8 * m + 1) (e := 2 * m + E))
    ring_nf; finish
  · simp [Q]; omega

theorem trans_mod2 (m E : ℕ) :
    ⟨3 * m + 2, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * m + 6, 0, 0, 0, 10 * m + E + 6⟩ := by
  apply stepStar_stepPlus
  · apply stepStar_trans (a_to_de (3 * m + 2) E)
    have hd := drain_rem (r := 2) m 0 (e := 2 * m + 2 + E)
    rw [show 2 * m + 2 + E + m = 3 * m + 2 + E from by ring,
        show (0 : ℕ) + 8 * m = 8 * m from by ring] at hd
    apply stepStar_trans hd
    rw [show 2 * m + 2 + E = (2 * m + 1 + E) + 1 from by ring]
    apply stepStar_trans (d_tail_2 (b := 8 * m) (e := 2 * m + 1 + E))
    rw [show 8 * m + 5 = (8 * m + 4) + 1 from by ring]
    apply stepStar_trans (phase4_a1 (b := 8 * m + 4) (e := 2 * m + 1 + E))
    ring_nf; finish
  · simp [Q]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = ⟨A, 0, 0, 0, E⟩ ∧ A ≥ 1)
  · intro c ⟨A, E, hq, hA⟩; subst hq
    obtain ⟨m, rfl | rfl | rfl⟩ :
        ∃ m, A = 3 * m + 1 ∨ A = 3 * m + 2 ∨ A = 3 * m + 3 := by
      refine ⟨(A - 1) / 3, ?_⟩
      have : (A - 1) % 3 < 3 := Nat.mod_lt _ (by omega)
      rcases (show (A - 1) % 3 = 0 ∨ (A - 1) % 3 = 1 ∨ (A - 1) % 3 = 2 from by omega)
        with h0 | h1 | h2
      · left; omega
      · right; left; omega
      · right; right; omega
    · exact ⟨_, ⟨8 * m + 4, 10 * m + E + 2, rfl, by omega⟩, trans_mod1 m E⟩
    · exact ⟨_, ⟨8 * m + 6, 10 * m + E + 6, rfl, by omega⟩, trans_mod2 m E⟩
    · rw [show 3 * m + 3 = 3 * (m + 1) from by ring]
      exact ⟨_, ⟨8 * m + 10, 10 * m + E + 8, rfl, by omega⟩, trans_mod0 m E⟩
  · show ∃ A E, c₀ = ⟨A, 0, 0, 0, E⟩ ∧ A ≥ 1
    exact ⟨1, 0, rfl, by omega⟩

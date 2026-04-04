import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1929: [9/70, 25/21, 22/5, 7/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  2 -1  0
 1  0 -1  0  1
 0  0  0  1 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1929

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_d' : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem c_to_ae : ∀ k, ⟨a, b, k, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem rebuild_round : ⟨a, b + 1, 2, 0, e⟩ [fm]⊢* ⟨a + 2, b, 2, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem rebuild_loop : ∀ b, ⟨a, b, 2, 0, e⟩ [fm]⊢* ⟨a + 2 * b, 0, 2, 0, e + b⟩ := by
  intro b; induction' b with b ih generalizing a e
  · exists 0
  · apply stepStar_trans rebuild_round
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem rebuild_end : ⟨a, 0, 2, 0, e⟩ [fm]⊢* ⟨a + 2, 0, 0, e + 2, 0⟩ := by
  apply stepStar_trans (c_to_ae (a := a) (b := 0) (e := e) (k := 2))
  rw [show e + 2 = 0 + (e + 2) from by omega,
      show (0 : ℕ) = 0 + 0 from by omega]
  exact e_to_d' (e := 0) (d := 0) (k := e + 2)

theorem rebuild : ⟨a, b, 2, 0, e⟩ [fm]⊢* ⟨a + 2 * b + 2, 0, 0, e + b + 2, 0⟩ := by
  apply stepStar_trans (rebuild_loop b)
  apply stepStar_trans (rebuild_end (a := a + 2 * b) (e := e + b))
  ring_nf; finish

theorem drain_round : ⟨a + 2, b, 2, d + 3, 0⟩ [fm]⊢* ⟨a, b + 3, 2, d, 0⟩ := by
  step fm; step fm; step fm; finish

theorem drain_loop : ∀ k, ⟨a + 2 * k, b, 2, d + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 2, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a := a + 2) (d := d + 3))
    apply stepStar_trans (drain_round (a := a) (b := b + 3 * k) (d := d))
    ring_nf; finish

theorem tail_d1 : ⟨a + 1, b, 2, 1, 0⟩ [fm]⊢* ⟨a + 1, b + 1, 2, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem tail_d2 : ⟨a + 3, b, 2, 2, 0⟩ [fm]⊢* ⟨a, b + 4, 2, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem trans_mod0 : ⟨a + 2 * m + 4, 0, 0, 3 * (m + 1), 0⟩ [fm]⊢⁺
    ⟨a + 6 * m + 9, 0, 0, 3 * m + 5, 0⟩ := by
  rw [show a + 2 * m + 4 = (a + 2 * m + 3) + 1 from by omega]
  step fm; step fm
  show ⟨a + 2 * m + 3, 0, 2, 3 * (m + 1), 0⟩ [fm]⊢* _
  rw [show a + 2 * m + 3 = (a + 1) + 2 * (m + 1) from by ring,
      show 3 * (m + 1) = 0 + 3 * (m + 1) from by ring]
  apply stepStar_trans (drain_loop (m + 1) (a := a + 1) (b := 0) (d := 0))
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring]
  apply stepStar_trans (rebuild (a := a + 1) (b := 3 * m + 3) (e := 0))
  ring_nf; finish

theorem trans_mod1 : ⟨a + 2 * m + 5, 0, 0, 3 * m + 4, 0⟩ [fm]⊢⁺
    ⟨a + 6 * m + 12, 0, 0, 3 * m + 6, 0⟩ := by
  rw [show a + 2 * m + 5 = (a + 2 * m + 4) + 1 from by omega]
  step fm; step fm
  show ⟨a + 2 * m + 4, 0, 2, 3 * m + 4, 0⟩ [fm]⊢* _
  rw [show a + 2 * m + 4 = (a + 2) + 2 * (m + 1) from by ring,
      show 3 * m + 4 = 1 + 3 * (m + 1) from by ring]
  apply stepStar_trans (drain_loop (m + 1) (a := a + 2) (b := 0) (d := 1))
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring]
  apply stepStar_trans (tail_d1 (a := a + 1) (b := 3 * m + 3))
  apply stepStar_trans (rebuild (a := a + 2) (b := 3 * m + 4) (e := 0))
  ring_nf; finish

theorem trans_mod2 : ⟨a + 2 * m + 4, 0, 0, 3 * m + 2, 0⟩ [fm]⊢⁺
    ⟨a + 6 * m + 10, 0, 0, 3 * m + 6, 0⟩ := by
  rw [show a + 2 * m + 4 = (a + 2 * m + 3) + 1 from by omega]
  step fm; step fm
  show ⟨a + 2 * m + 3, 0, 2, 3 * m + 2, 0⟩ [fm]⊢* _
  rw [show a + 2 * m + 3 = (a + 3) + 2 * m from by ring,
      show 3 * m + 2 = 2 + 3 * m from by ring]
  apply stepStar_trans (drain_loop m (a := a + 3) (b := 0) (d := 2))
  rw [show 0 + 3 * m = 3 * m from by ring]
  apply stepStar_trans (tail_d2 (a := a) (b := 3 * m))
  apply stepStar_trans (rebuild (a := a) (b := 3 * m + 4) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 0⟩) (by execute fm 21)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 3 * a ≥ 2 * d + 6 ∧ d ≥ 2)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, d = 3 * m ∨ d = 3 * m + 1 ∨ d = 3 * m + 2 :=
      ⟨d / 3, by omega⟩
    · -- d = 3*m, m >= 1
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m + 4 := ⟨a - (2 * m + 4), by omega⟩
      exact ⟨⟨F + 6 * m + 9, 0, 0, 3 * m + 5, 0⟩,
        ⟨F + 6 * m + 9, 3 * m + 5, rfl, by omega, by omega⟩, trans_mod0⟩
    · -- d = 3*m + 1, m >= 1
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m + 5 := ⟨a - (2 * m + 5), by omega⟩
      refine ⟨⟨F + 6 * m + 12, 0, 0, 3 * m + 6, 0⟩,
        ⟨F + 6 * m + 12, 3 * m + 6, rfl, by omega, by omega⟩, ?_⟩
      show ⟨F + 2 * m + 5, 0, 0, 3 * m + 4, 0⟩ [fm]⊢⁺ _
      exact trans_mod1
    · -- d = 3*m + 2, m >= 0
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m + 4 := ⟨a - (2 * m + 4), by omega⟩
      exact ⟨⟨F + 6 * m + 10, 0, 0, 3 * m + 6, 0⟩,
        ⟨F + 6 * m + 10, 3 * m + 6, rfl, by omega, by omega⟩, trans_mod2⟩
  · exact ⟨5, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1929

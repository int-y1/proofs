import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #663: [35/6, 16/55, 77/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 4  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_663

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+4, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

theorem a_drain : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1)); ring_nf; finish

theorem r1_repeat : ∀ k, ⟨a + k, k, c, d, e⟩ [fm]⊢* ⟨a, 0, c + k, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1) (d := d + 1)); ring_nf; finish

theorem r2_drain : ∀ k, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 4 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 4) (c := c) (d := d) (e := e)); ring_nf; finish

theorem inner_loop : ∀ F, ⟨4, B + 4 * F, C, D, E + F⟩ [fm]⊢* ⟨4, B, C + 3 * F, D + 4 * F, E⟩ := by
  intro F; induction' F with F ih generalizing B C D E
  · exists 0
  · rw [show B + 4 * (F + 1) = (B + 4 * F) + 4 from by ring,
        show E + (F + 1) = (E + F) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (B := B) (C := C + 3) (D := D + 4) (E := E))
    ring_nf; finish

theorem c_drain : ∀ k, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 3) (d := d + 1)); ring_nf; finish

-- r2_drain variant with concrete 0 for e
theorem r2_drain' : ∀ k, ⟨a, 0, G + k, d, k⟩ [fm]⊢* ⟨a + 4 * k, 0, G, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a G d
  · exists 0
  · rw [show G + (k + 1) = (G + k) + 1 from by ring, show k + 1 = (k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 4) (G := G) (d := d)); ring_nf; finish

-- Main transition using F = E - N - 1 (>= 0) to avoid natural subtraction.
-- From (0, 0, 0, 4*N+4, N+1+F) with F <= 3*N+3.
-- Target: (0, 0, 0, 16*N+16, 9*N+10+F).
theorem main_trans_aux (hF : F ≤ 3 * N + 3) :
    ⟨0, 0, 0, 4 * N + 4, N + 1 + F⟩ [fm]⊢⁺ ⟨0, 0, 0, 16 * N + 16, 9 * N + 10 + F⟩ := by
  -- Phase 1: d_to_b
  rw [show (4 * N + 4 : ℕ) = 0 + (4 * N + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * N + 4) (b := 0) (d := 0) (e := N + 1 + F))
  -- Phase 2: R5
  rw [show 0 + (4 * N + 4) = (4 * N + 3) + 1 from by ring]
  step fm
  -- R2
  rw [show N + 1 + F = (N + F) + 1 from by ring]
  step fm
  -- Now at (4, 4*N+3, 0, 0, N+F)
  -- Phase 3: inner_loop N
  rw [show 4 * N + 3 = 3 + 4 * N from by ring,
      show N + F = F + N from by ring]
  apply stepStar_trans (inner_loop N (B := 3) (C := 0) (D := 0) (E := F))
  -- Now at (4, 3, 0+3*N, 0+4*N, F)
  -- Phase 4: r1_repeat 3
  show ⟨1 + 3, 3, 0 + 3 * N, 0 + 4 * N, F⟩ [fm]⊢* _
  apply stepStar_trans (r1_repeat 3 (a := 1) (c := 0 + 3 * N) (d := 0 + 4 * N) (e := F))
  -- Now at (1, 0, 0+3*N+3, 0+4*N+3, F)
  -- Phase 5: r2_drain' F
  -- Need: 0+3*N+3 = (3*N+3-F) + F
  have h5a : 0 + 3 * N + 3 = (3 * N + 3 - F) + F := by omega
  rw [h5a]
  apply stepStar_trans (r2_drain' F (a := 1) (G := 3 * N + 3 - F) (d := 0 + 4 * N + 3))
  -- Now at (1+4*F, 0, 3*N+3-F, 0+4*N+3, 0)
  -- Phase 6: c_drain (3*N+3-F)
  rw [show 1 + 4 * F = 4 * F + 1 from by ring]
  apply stepStar_trans (c_drain (3 * N + 3 - F) (a := 4 * F) (d := 0 + 4 * N + 3))
  -- Phase 7: a_drain
  -- 4*F+1+3*(3*N+3-F) = F+9*N+10
  rw [show 4 * F + 1 + 3 * (3 * N + 3 - F) = F + 9 * N + 10 from by omega]
  apply stepStar_trans (a_drain (F + 9 * N + 10) (d := 0 + 4 * N + 3 + (3 * N + 3 - F)) (e := 0))
  rw [show 0 + 4 * N + 3 + (3 * N + 3 - F) + (F + 9 * N + 10) = 16 * N + 16 from by omega,
      show 0 + (F + 9 * N + 10) = 9 * N + 10 + F from by omega]
  finish

theorem main_trans (hE1 : E ≥ N + 1) (hE2 : E ≤ 4 * N + 4) :
    ⟨0, 0, 0, 4 * N + 4, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 16 * N + 16, E + 8 * N + 9⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, E = N + 1 + F := ⟨E - (N + 1), by omega⟩
  rw [show N + 1 + F + 8 * N + 9 = 9 * N + 10 + F from by ring]
  exact main_trans_aux (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 4⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ N E, q = ⟨0, 0, 0, 4 * N + 4, E⟩ ∧ E ≥ N + 1 ∧ E ≤ 4 * N + 4)
  · intro c ⟨N, E, hq, hE1, hE2⟩; subst hq
    refine ⟨⟨0, 0, 0, 16 * N + 16, E + 8 * N + 9⟩,
      ⟨4 * N + 3, E + 8 * N + 9, ?_, by omega, by omega⟩,
      main_trans hE1 hE2⟩
    show (0, 0, 0, 16 * N + 16, E + 8 * N + 9) = (0, 0, 0, 4 * (4 * N + 3) + 4, E + 8 * N + 9)
    ring_nf
  · exact ⟨0, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_663

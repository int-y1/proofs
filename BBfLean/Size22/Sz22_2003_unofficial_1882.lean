import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1882: [9/35, 5/33, 2662/5, 7/121, 5/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1  0 -1  0  3
 0  0  0  1 -2
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1882

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (d := d) (e := e + 2))
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 = e + 1 + 1 from by ring]
    step fm; finish

theorem drain_loop : ∀ K, ⟨K, b + 1, 1, K, 0⟩ [fm]⊢* ⟨0, b + 2 * K + 1, 1, 0, 0⟩ := by
  intro K; induction' K with K ih generalizing b
  · exists 0
  · step fm; step fm
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

theorem r3_chain : ∀ C, ⟨A, 0, C, 0, E⟩ [fm]⊢* ⟨A + C, 0, 0, 0, E + 3 * C⟩ := by
  intro C; induction' C with C ih generalizing A E
  · exists 0
  · step fm
    apply stepStar_trans (ih (A := A + 1) (E := E + 3))
    ring_nf; finish

theorem r2r3_round : ⟨A, B + 3, C, 0, 3⟩ [fm]⊢* ⟨A + 1, B, C + 2, 0, 3⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem r2r3_chain : ∀ k, ⟨A, B + 3 * k, C, 0, 3⟩ [fm]⊢* ⟨A + k, B, C + 2 * k, 0, 3⟩ := by
  intro k; induction' k with k ih generalizing A B C
  · exists 0
  · rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (A := A) (B := B + 3) (C := C))
    apply stepStar_trans (r2r3_round (A := A + k) (B := B) (C := C + 2 * k))
    ring_nf; finish

theorem end_r1 : ⟨A, 1, C, 0, 3⟩ [fm]⊢* ⟨A + C + 1, 0, 0, 0, 3 * C + 5⟩ := by
  step fm
  apply stepStar_trans (r3_chain (C + 1) (A := A) (E := 2))
  ring_nf; finish

theorem end_r2 : ⟨A, 2, C, 0, 3⟩ [fm]⊢* ⟨A + C + 2, 0, 0, 0, 3 * C + 7⟩ := by
  step fm; step fm
  apply stepStar_trans (r3_chain (C + 2) (A := A) (E := 1))
  ring_nf; finish

theorem full_drain : ⟨K + 1, 0, 0, K + 1, 1⟩ [fm]⊢* ⟨0, 2 * K + 1, 1, 0, 0⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (drain_loop K (b := 0))
  ring_nf; finish

theorem phases123 (K : ℕ) : ⟨K + 1, 0, 0, 0, 2 * K + 3⟩ [fm]⊢⁺ ⟨1, 2 * K + 1, 0, 0, 3⟩ := by
  rw [show 2 * K + 3 = 1 + 2 * (K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (K + 1) (a := K + 1) (d := 0) (e := 1))
  rw [show 0 + (K + 1) = K + 1 from by ring]
  apply stepStar_step_stepPlus (full_drain (K := K))
  simp [fm]

theorem trans_mod0 (m : ℕ) : ⟨3 * m + 1, 0, 0, 0, 6 * m + 3⟩ [fm]⊢⁺ ⟨6 * m + 2, 0, 0, 0, 12 * m + 5⟩ := by
  rw [show 3 * m + 1 = (3 * m) + 1 from by ring,
      show 6 * m + 3 = 2 * (3 * m) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (phases123 (3 * m))
  rw [show 2 * (3 * m) + 1 = 1 + 3 * (2 * m) from by ring]
  apply stepStar_trans (r2r3_chain (2 * m) (A := 1) (B := 1) (C := 0))
  apply stepStar_trans (end_r1 (A := 1 + 2 * m) (C := 0 + 2 * (2 * m)))
  rw [show 1 + 2 * m + (0 + 2 * (2 * m)) + 1 = 6 * m + 2 from by ring,
      show 3 * (0 + 2 * (2 * m)) + 5 = 12 * m + 5 from by ring]
  finish

theorem trans_mod1 (m : ℕ) : ⟨3 * m + 2, 0, 0, 0, 6 * m + 5⟩ [fm]⊢⁺ ⟨6 * m + 4, 0, 0, 0, 12 * m + 9⟩ := by
  rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring,
      show 6 * m + 5 = 2 * (3 * m + 1) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (phases123 (3 * m + 1))
  rw [show 2 * (3 * m + 1) + 1 = 0 + 3 * (2 * m + 1) from by ring]
  apply stepStar_trans (r2r3_chain (2 * m + 1) (A := 1) (B := 0) (C := 0))
  apply stepStar_trans (r3_chain (0 + 2 * (2 * m + 1)) (A := 1 + (2 * m + 1)) (E := 3))
  rw [show 1 + (2 * m + 1) + (0 + 2 * (2 * m + 1)) = 6 * m + 4 from by ring,
      show 3 + 3 * (0 + 2 * (2 * m + 1)) = 12 * m + 9 from by ring]
  finish

theorem trans_mod2 (m : ℕ) : ⟨3 * m + 3, 0, 0, 0, 6 * m + 7⟩ [fm]⊢⁺ ⟨6 * m + 6, 0, 0, 0, 12 * m + 13⟩ := by
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring,
      show 6 * m + 7 = 2 * (3 * m + 2) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (phases123 (3 * m + 2))
  rw [show 2 * (3 * m + 2) + 1 = 2 + 3 * (2 * m + 1) from by ring]
  apply stepStar_trans (r2r3_chain (2 * m + 1) (A := 1) (B := 2) (C := 0))
  apply stepStar_trans (end_r2 (A := 1 + (2 * m + 1)) (C := 0 + 2 * (2 * m + 1)))
  rw [show 1 + (2 * m + 1) + (0 + 2 * (2 * m + 1)) + 2 = 6 * m + 6 from by ring,
      show 3 * (0 + 2 * (2 * m + 1)) + 7 = 12 * m + 13 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a, q = ⟨a + 1, 0, 0, 0, 2 * a + 3⟩)
  · intro c ⟨a, hq⟩; subst hq
    obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 :=
      ⟨a / 3, by omega⟩
    · refine ⟨⟨6 * m + 2, 0, 0, 0, 12 * m + 5⟩, ⟨6 * m + 1, ?_⟩, ?_⟩
      · show (6 * m + 2, 0, 0, 0, 12 * m + 5) = (6 * m + 1 + 1, 0, 0, 0, 2 * (6 * m + 1) + 3)
        ring_nf
      · show ⟨3 * m + 1, 0, 0, 0, 2 * (3 * m) + 3⟩ [fm]⊢⁺ ⟨6 * m + 2, 0, 0, 0, 12 * m + 5⟩
        rw [show 2 * (3 * m) + 3 = 6 * m + 3 from by ring]
        exact trans_mod0 m
    · refine ⟨⟨6 * m + 4, 0, 0, 0, 12 * m + 9⟩, ⟨6 * m + 3, ?_⟩, ?_⟩
      · show (6 * m + 4, 0, 0, 0, 12 * m + 9) = (6 * m + 3 + 1, 0, 0, 0, 2 * (6 * m + 3) + 3)
        ring_nf
      · show ⟨3 * m + 1 + 1, 0, 0, 0, 2 * (3 * m + 1) + 3⟩ [fm]⊢⁺ ⟨6 * m + 4, 0, 0, 0, 12 * m + 9⟩
        rw [show 3 * m + 1 + 1 = 3 * m + 2 from by ring,
            show 2 * (3 * m + 1) + 3 = 6 * m + 5 from by ring]
        exact trans_mod1 m
    · refine ⟨⟨6 * m + 6, 0, 0, 0, 12 * m + 13⟩, ⟨6 * m + 5, ?_⟩, ?_⟩
      · show (6 * m + 6, 0, 0, 0, 12 * m + 13) = (6 * m + 5 + 1, 0, 0, 0, 2 * (6 * m + 5) + 3)
        ring_nf
      · show ⟨3 * m + 2 + 1, 0, 0, 0, 2 * (3 * m + 2) + 3⟩ [fm]⊢⁺ ⟨6 * m + 6, 0, 0, 0, 12 * m + 13⟩
        rw [show 3 * m + 2 + 1 = 3 * m + 3 from by ring,
            show 2 * (3 * m + 2) + 3 = 6 * m + 7 from by ring]
        exact trans_mod2 m
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_1882

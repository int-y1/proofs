import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1565: [7/45, 242/15, 3/11, 175/2, 3/7]

Vector representation:
```
 0 -2 -1  1  0
 1 -1 -1  0  2
 0  1  0  0 -1
-1  0  2  1  0
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1565

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: transfer e to b (c=0 ensures R3 fires)
theorem e_to_b : ∀ k b, (⟨a, b, 0, d, e + k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (b + 1)); ring_nf; finish

-- R4 cascade
theorem r4_cascade : ∀ j c D, (⟨j, 0, c, D, 0⟩ : Q) [fm]⊢* ⟨0, 0, c + 2 * j, D + j, 0⟩ := by
  intro j; induction j with
  | zero => intro c D; ring_nf; finish
  | succ j ih =>
    intro c D; step fm
    apply stepStar_trans (ih (c + 2) (D + 1)); ring_nf; finish

-- R4+R1+R1 loop
theorem r4r1r1_loop : ∀ k a b D,
    (⟨a + k, b + 4 * k, 0, D, 0⟩ : Q) [fm]⊢* ⟨a, b, 0, D + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b D; ring_nf; finish
  | succ k ih =>
    intro a b D
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a b (D + 3)); ring_nf; finish

-- R3+R2 interleaved chain: k rounds consuming c, each round R3 then R2
-- Net effect per round: a += 1, c -= 1, e += 1
theorem r3r2_chain : ∀ k a d e,
    (⟨a, 0, k, d, e + 1⟩ : Q) [fm]⊢* ⟨a + k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro a d e; ring_nf; finish
  | succ k ih =>
    intro a d e
    step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d (e + 1))
    ring_nf; finish

-- Phase 1: opening
theorem phase1 (C D : ℕ) :
    (⟨0, 0, C + 1, D + 1, 0⟩ : Q) [fm]⊢⁺ ⟨C + 1, C + 2, 0, D, 0⟩ := by
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain C 1 D 1)
  rw [show 1 + C = C + 1 from by ring,
      show C + 1 + 1 = 0 + (C + 2) from by ring]
  apply stepStar_trans (e_to_b (C + 2) 0 (a := C + 1) (d := D) (e := 0))
  ring_nf; finish

theorem tail_r0 (m D : ℕ) :
    (⟨3 * m + 3, 1, 0, D, 0⟩ : Q) [fm]⊢* ⟨0, 0, 6 * m + 7, D + 3 * m + 8, 0⟩ := by
  step fm; step fm; step fm; step fm
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_trans (e_to_b 3 0 (a := 3 * m + 4) (d := D + 1) (e := 0))
  step fm; step fm; step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (e_to_b 2 0 (a := 3 * m + 4) (d := D + 3) (e := 0))
  step fm; step fm
  apply stepStar_trans (r4_cascade (3 * m + 3) 1 (D + 5))
  ring_nf; finish

theorem tail_r1 (m D : ℕ) :
    (⟨3 * m + 4, 2, 0, D, 0⟩ : Q) [fm]⊢* ⟨0, 0, 6 * m + 7, D + 3 * m + 5, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r4_cascade (3 * m + 3) 1 (D + 2))
  ring_nf; finish

theorem tail_r2 (m D : ℕ) :
    (⟨3 * m + 5, 3, 0, D, 0⟩ : Q) [fm]⊢* ⟨0, 0, 6 * m + 9, D + 3 * m + 8, 0⟩ := by
  step fm; step fm; step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (e_to_b 2 0 (a := 3 * m + 5) (d := D + 2) (e := 0))
  step fm; step fm
  apply stepStar_trans (r4_cascade (3 * m + 4) 1 (D + 4))
  ring_nf; finish

theorem tail_r3 (m D : ℕ) :
    (⟨3 * m + 5, 0, 0, D, 0⟩ : Q) [fm]⊢* ⟨0, 0, 6 * m + 10, D + 3 * m + 5, 0⟩ := by
  apply stepStar_trans (r4_cascade (3 * m + 5) 0 D)
  ring_nf; finish

theorem trans_mod0 (M d : ℕ) :
    (⟨0, 0, 4 * M + 4, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * M + 7, d + 6 * M + 11, 0⟩ := by
  rw [show 4 * M + 4 = (4 * M + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase1 (4 * M + 3) d)
  rw [show 4 * M + 3 + 1 = (3 * M + 3) + (M + 1) from by ring,
      show 4 * M + 3 + 2 = 1 + 4 * (M + 1) from by ring]
  apply stepStar_trans (r4r1r1_loop (M + 1) (3 * M + 3) 1 d)
  rw [show d + 3 * (M + 1) = d + 3 * M + 3 from by ring]
  apply stepStar_trans (tail_r0 M (d + 3 * M + 3))
  ring_nf; finish

theorem trans_mod1 (M d : ℕ) :
    (⟨0, 0, 4 * M + 5, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * M + 7, d + 6 * M + 8, 0⟩ := by
  rw [show 4 * M + 5 = (4 * M + 4) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase1 (4 * M + 4) d)
  rw [show 4 * M + 4 + 1 = (3 * M + 4) + (M + 1) from by ring,
      show 4 * M + 4 + 2 = 2 + 4 * (M + 1) from by ring]
  apply stepStar_trans (r4r1r1_loop (M + 1) (3 * M + 4) 2 d)
  rw [show d + 3 * (M + 1) = d + 3 * M + 3 from by ring]
  apply stepStar_trans (tail_r1 M (d + 3 * M + 3))
  ring_nf; finish

theorem trans_mod2 (M d : ℕ) :
    (⟨0, 0, 4 * M + 6, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * M + 9, d + 6 * M + 11, 0⟩ := by
  rw [show 4 * M + 6 = (4 * M + 5) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase1 (4 * M + 5) d)
  rw [show 4 * M + 5 + 1 = (3 * M + 5) + (M + 1) from by ring,
      show 4 * M + 5 + 2 = 3 + 4 * (M + 1) from by ring]
  apply stepStar_trans (r4r1r1_loop (M + 1) (3 * M + 5) 3 d)
  rw [show d + 3 * (M + 1) = d + 3 * M + 3 from by ring]
  apply stepStar_trans (tail_r2 M (d + 3 * M + 3))
  ring_nf; finish

theorem trans_mod3 (M d : ℕ) :
    (⟨0, 0, 4 * M + 7, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * M + 10, d + 6 * M + 11, 0⟩ := by
  rw [show 4 * M + 7 = (4 * M + 6) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase1 (4 * M + 6) d)
  rw [show 4 * M + 6 + 1 = (3 * M + 5) + (M + 2) from by ring,
      show 4 * M + 6 + 2 = 0 + 4 * (M + 2) from by ring]
  apply stepStar_trans (r4r1r1_loop (M + 2) (3 * M + 5) 0 d)
  rw [show d + 3 * (M + 2) = d + 3 * M + 6 from by ring]
  apply stepStar_trans (tail_r3 M (d + 3 * M + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 9, 0⟩) (by execute fm 31)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c + 4, d + 1, 0⟩)
  · intro q ⟨c, d, hq⟩; subst hq
    have h4 : c % 4 < 4 := Nat.mod_lt _ (by omega)
    obtain ⟨M, hM⟩ : ∃ M, c = 4 * M + c % 4 := ⟨c / 4, by omega⟩
    interval_cases (c % 4)
    · rw [show c = 4 * M from by omega]
      exact ⟨⟨0, 0, 6 * M + 7, d + 6 * M + 11, 0⟩,
        ⟨6 * M + 3, d + 6 * M + 10, by ring_nf⟩, trans_mod0 M d⟩
    · rw [show c = 4 * M + 1 from by omega]
      exact ⟨⟨0, 0, 6 * M + 7, d + 6 * M + 8, 0⟩,
        ⟨6 * M + 3, d + 6 * M + 7, by ring_nf⟩, trans_mod1 M d⟩
    · rw [show c = 4 * M + 2 from by omega]
      exact ⟨⟨0, 0, 6 * M + 9, d + 6 * M + 11, 0⟩,
        ⟨6 * M + 5, d + 6 * M + 10, by ring_nf⟩, trans_mod2 M d⟩
    · rw [show c = 4 * M + 3 from by omega]
      exact ⟨⟨0, 0, 6 * M + 10, d + 6 * M + 11, 0⟩,
        ⟨6 * M + 6, d + 6 * M + 10, by ring_nf⟩, trans_mod3 M d⟩
  · exact ⟨0, 8, by ring_nf⟩

end Sz22_2003_unofficial_1565

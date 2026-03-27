import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_323

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

theorem r1r3_chain : ∀ j a b,
    ⟨a, b, 1, j, 0⟩ [fm]⊢* ⟨a + j, b + j, 1, 0, 0⟩ := by
  intro j; induction j with
  | zero => intro a b; simp; exists 0
  | succ j ih =>
    intro a b
    step fm; step fm
    rw [show a + (j + 1) = (a + 1) + j from by ring,
        show b + (j + 1) = (b + 1) + j from by ring]
    exact ih (a + 1) (b + 1)

theorem r3_drain : ∀ b a c,
    ⟨a, b, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c + b, 0, 0⟩ := by
  intro b; induction b with
  | zero => intro a c; simp; exists 0
  | succ b ih =>
    intro a c
    step fm
    rw [show c + (b + 1) = (c + 1) + b from by ring]
    exact ih a (c + 1)

theorem r4_chain : ∀ j a c e,
    ⟨a, 0, c + 2 * j, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro a c e; simp; exists 0
  | succ j ih =>
    intro a c e
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
    step fm
    rw [show e + 2 * (j + 1) = (e + 2) + 2 * j from by ring]
    exact ih a c (e + 2)

theorem r5r2_chain : ∀ j a d,
    ⟨a + j, 0, 0, d, j⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * j, 0⟩ := by
  intro j; induction j with
  | zero => intro a d; simp; exists 0
  | succ j ih =>
    intro a d
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm; step fm
    rw [show d + 2 * (j + 1) = (d + 2) + 2 * j from by ring]
    exact ih a (d + 2)

theorem main_trans (d : ℕ) :
    ⟨0, 0, 1, 2 * d + 6, 0⟩ [fm]⊢⁺ ⟨0, 0, 1, 8 * d + 22, 0⟩ := by
  -- Phase 1: R1, R3, then R1+R3 loop
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · show ⟨1, 2, 0, 2 * d + 5, 0⟩ [fm]⊢* ⟨1, 1, 1, 2 * d + 5, 0⟩
    step fm; finish
  apply stepStar_trans (r1r3_chain (2 * d + 5) 1 1)
  rw [show 1 + (2 * d + 5) = 2 * d + 6 from by ring]
  -- Phase 2: R3 drain
  apply stepStar_trans (r3_drain (2 * d + 6) (2 * d + 6) 1)
  rw [show 1 + (2 * d + 6) = 1 + 2 * (d + 3) from by ring]
  -- Phase 3: R4
  apply stepStar_trans (r4_chain (d + 3) (2 * d + 6) 1 0)
  rw [show 0 + 2 * (d + 3) = 2 * d + 6 from by ring]
  -- Phase 4: setup (5 steps)
  rw [show 2 * d + 6 = (2 * d + 3) + 3 from by ring]
  apply stepStar_trans
  · show ⟨(2 * d + 3) + 3, 0, 1, 0, (2 * d + 3) + 3⟩ [fm]⊢*
         ⟨(2 * d + 3) + 3, 0, 0, 1, 2 * d + 3⟩
    step fm; step fm; step fm; step fm; step fm; finish
  -- Phase 5: R5+R2 chain
  rw [show (2 * d + 3) + 3 = 3 + (2 * d + 3) from by ring]
  apply stepStar_trans (r5r2_chain (2 * d + 3) 3 1)
  rw [show 1 + 2 * (2 * d + 3) = 4 * d + 7 from by ring]
  -- Phase 6: R5 then R3
  apply stepStar_trans
  · show ⟨3, 0, 0, 4 * d + 7, 0⟩ [fm]⊢* ⟨2, 0, 1, 4 * d + 9, 0⟩
    rw [show (3 : ℕ) = 2 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 7: R1, R3, then R1+R3 loop
  apply stepStar_trans
  · show ⟨2, 0, 1, 4 * d + 9, 0⟩ [fm]⊢* ⟨3, 1, 1, 4 * d + 8, 0⟩
    rw [show 4 * d + 9 = (4 * d + 8) + 1 from by ring]
    step fm; step fm; finish
  apply stepStar_trans (r1r3_chain (4 * d + 8) 3 1)
  rw [show 3 + (4 * d + 8) = 4 * d + 11 from by ring,
      show 1 + (4 * d + 8) = 4 * d + 9 from by ring]
  -- Phase 8: R3 drain
  apply stepStar_trans (r3_drain (4 * d + 9) (4 * d + 11) 1)
  rw [show 1 + (4 * d + 9) = 0 + 2 * (2 * d + 5) from by ring]
  -- Phase 9: R4
  apply stepStar_trans (r4_chain (2 * d + 5) (4 * d + 11) 0 0)
  rw [show 0 + 2 * (2 * d + 5) = 4 * d + 10 from by ring]
  -- Phase 10: R5+R2 chain
  rw [show 4 * d + 11 = 1 + (4 * d + 10) from by ring]
  apply stepStar_trans (r5r2_chain (4 * d + 10) 1 0)
  rw [show 0 + 2 * (4 * d + 10) = 8 * d + 20 from by ring]
  -- Phase 11: R5 then R3
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 6, 0⟩)
  · unfold c₀
    execute fm 24
  · apply progress_nonhalt_simple (fun d => (⟨0, 0, 1, 2 * d + 6, 0⟩ : Q)) 0
    intro d; exact ⟨4 * d + 8, by rw [show 2 * (4 * d + 8) + 6 = 8 * d + 22 from by ring]; exact main_trans d⟩

end Sz22_2003_unofficial_323

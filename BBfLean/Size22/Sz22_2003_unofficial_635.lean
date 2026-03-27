import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #635: [35/6, 143/2, 4/55, 3/7, 30/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_635

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  have many_step : ∀ k b, ⟨(0:ℕ), b, (0:ℕ), d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3,R2,R2 drain: convert c to e and f
theorem drain : ∀ k, ∀ e f, ⟨(0:ℕ), (0:ℕ), k, d, e+1, f⟩ [fm]⊢* ⟨0, 0, 0, d, e+1+k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro e f
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Combined R3/R1 interleave and R3/R2/R2 drain by strong induction
theorem interleave_drain : ∀ N, ∀ c d E F, N ≤ 2 * E →
    ⟨(0:ℕ), N, c+1, d, E+1, F⟩ [fm]⊢* ⟨0, 0, 0, d+N, E+c+2, F+2*c+N+2⟩ := by
  intro N; induction' N using Nat.strongRecOn with N ih
  intro c d E F hNE
  rcases N with _ | _ | N
  · apply stepStar_trans (drain (c+1) E F)
    ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (drain (c+1) E (F+1))
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show E = (E - 1) + 1 from by omega]
    apply stepStar_trans (ih N (by omega) (c+1) (d+2) (E-1) F (by omega))
    rw [show d + 2 + N = d + (N + 1 + 1) from by omega]
    rw [show E - 1 + (c + 1) + 2 = E - 1 + 1 + c + 2 from by omega]
    rw [show F + 2 * (c + 1) + N + 2 = F + 2 * c + (N + 1 + 1) + 2 from by omega]
    finish

-- Main transition: (0,0,0,n,2n+1,f) →⁺ (0,0,0,n+1,2(n+1)+1,f+n+3)
theorem main_trans (hf : f ≥ 1) :
    ⟨0, 0, 0, n, 2*n+1, f⟩ [fm]⊢⁺ ⟨(0:ℕ), 0, 0, n+1, 2*(n+1)+1, f+n+3⟩ := by
  rw [show n = 0 + n from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  rw [show f = (f - 1) + 1 from by omega]
  step fm; step fm
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  apply stepStar_trans (interleave_drain n 1 1 (2*n) (f-1) (by omega))
  rw [show 1 + n = n + 1 from by ring]
  rw [show 2 * n + 1 + 2 = 2 * (n + 1) + 1 from by ring]
  rw [show f - 1 + 2 * 1 + n + 2 = f - 1 + 1 + n + 3 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨0, 0, 0, n, 2*n+1, f⟩ ∧ f ≥ 1)
  · intro c ⟨n, f, hq, hf⟩; subst hq
    exact ⟨⟨0, 0, 0, n+1, 2*(n+1)+1, f+n+3⟩,
      ⟨n+1, f+n+3, rfl, by omega⟩, main_trans hf⟩
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_635

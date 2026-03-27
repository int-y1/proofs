import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #407: [25/18, 22/35, 49/2, 3/11, 25/7]

Vector representation:
```
-1 -2  2  0  0
 1  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_407

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R2+R1 combo: (0, b+2, c+1, d+1, e) ->* (0, b, c+2, d, e+1)
private theorem combo : ∀ b c d e,
    ⟨(0:ℕ), b+2, c+1, d+1, e⟩ [fm]⊢* ⟨(0:ℕ), b, c+2, d, e+1⟩ := by
  intro b c d e; step fm; step fm; ring_nf; finish

-- Iterate the combo n times
private theorem combo_iter : ∀ n, ∀ b c d e,
    ⟨(0:ℕ), b+2*n, c+1, d+n, e⟩ [fm]⊢* ⟨(0:ℕ), b, c+1+n, d, e+n⟩ := by
  intro n; induction' n with n ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (n + 1) = (b + 2 * n) + 2 from by ring,
        show d + (n + 1) = (d + n) + 1 from by ring]
    apply stepStar_trans
    · exact combo (b + 2 * n) c (d + n) e
    have h := ih b (c + 1) d (e + 1)
    rw [show c + 1 + 1 + n = c + 1 + (n + 1) from by ring,
        show e + 1 + n = e + (n + 1) from by ring] at h
    exact h

-- R3 cascade with b=0, c=0: k steps of rule 3
private theorem r3_cascade : ∀ k, ∀ a d e,
    ⟨a+k, (0:ℕ), (0:ℕ), d, e⟩ [fm]⊢* ⟨a, (0:ℕ), (0:ℕ), d+2*k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    rw [show d + 2 + 2 * k = d + 2 * k + 2 from by ring]; finish

-- R4 chain: transfer e to b (with c=0)
private theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0:ℕ), b, (0:ℕ), d, e+k⟩ [fm]⊢* ⟨(0:ℕ), b+k, (0:ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    have h := ih (b + 1) d e
    rw [show b + 1 + k = b + (k + 1) from by ring] at h
    exact h

-- Phase 2 sub-step when c >= 2: R3+R2+R2
private theorem phase2_sub : ∀ k c e,
    ⟨k+1, (0:ℕ), c+2, (0:ℕ), e⟩ [fm]⊢* ⟨k+2, (0:ℕ), c, (0:ℕ), e+2⟩ := by
  intro k c e; step fm; step fm; step fm; ring_nf; finish

-- Phase 2: (k+1, 0, c, 0, e) ->* (0, 0, 0, 2*(k+1)+c, e+c)
private theorem phase2 : ∀ c, ∀ k e,
    ⟨k+1, (0:ℕ), c, (0:ℕ), e⟩ [fm]⊢* ⟨(0:ℕ), (0:ℕ), (0:ℕ), 2*(k+1)+c, e+c⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih
  rcases c with _ | _ | c
  · -- c = 0
    intro k e
    have h := r3_cascade (k+1) 0 0 e
    simp only [Nat.zero_add] at h
    rw [show 2 * (k + 1) + 0 = 2 * (k + 1) from by ring,
        show e + 0 = e from by ring]
    exact h
  · -- c = 1: R3, R2, then R3 cascade
    intro k e
    step fm; step fm
    have h := r3_cascade (k+1) 0 1 (e+1)
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * (k + 1) = 2 * (k + 1) + 1 from by ring] at h
    exact h
  · -- c >= 2
    intro k e
    apply stepStar_trans (phase2_sub k c e)
    have h := ih c (by omega) (k+1) (e+2)
    rw [show k + 1 + 1 = k + 2 from by ring,
        show 2 * (k + 2) + c = 2 * (k + 1) + (c + 2) from by ring,
        show e + 2 + c = e + (c + 2) from by ring] at h
    exact h

-- Phase 1 as stepPlus: (0, 2n, 0, n+2, 0) ->⁺ (1, 0, n+1, 0, n+1)
private theorem phase1 : ∀ n,
    ⟨(0:ℕ), 2*n, (0:ℕ), n+2, (0:ℕ)⟩ [fm]⊢⁺ ⟨(1:ℕ), (0:ℕ), n+1, (0:ℕ), n+1⟩ := by
  intro n
  rw [show n + 2 = (n + 1) + 1 from by ring]
  -- R5: first step
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * n, 0, (n + 1) + 1, 0⟩ = _; rfl
  apply stepStar_trans
  · have h := combo_iter n 0 1 1 0
    rw [show 0 + 2 * n = 2 * n from by ring,
        show 1 + n = n + 1 from by ring,
        show 1 + 1 + n = n + 2 from by ring,
        show 0 + n = n from by ring] at h
    exact h
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm; ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1) where C(n) = (0, 2n, 0, n+2, 0)
private theorem main_trans (n : ℕ) :
    ⟨(0:ℕ), 2*n, (0:ℕ), n+2, (0:ℕ)⟩ [fm]⊢⁺ ⟨(0:ℕ), 2*(n+1), (0:ℕ), (n+1)+2, (0:ℕ)⟩ := by
  -- Phase 1: ⊢⁺ (1, 0, n+1, 0, n+1)
  apply stepPlus_stepStar_stepPlus (phase1 n)
  -- Phase 2: (1, 0, n+1, 0, n+1) ⊢* (0, 0, 0, n+3, 2n+2)
  apply stepStar_trans
  · have h := phase2 (n+1) 0 (n+1)
    rw [show 0 + 1 = 1 from by ring,
        show 2 * 1 + (n + 1) = n + 3 from by ring,
        show n + 1 + (n + 1) = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 3: (0, 0, 0, n+3, 2n+2) ⊢* (0, 2n+2, 0, n+3, 0)
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
      show (n + 1) + 2 = n + 3 from by ring]
  have h := r4_chain (2*n+2) 0 (n+3) 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2*n, 0, n+2, 0⟩) 0
  intro n
  exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_407

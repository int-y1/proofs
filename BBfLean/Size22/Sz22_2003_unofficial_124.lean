import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #124: [1/405, 98/15, 3/7, 25/2, 7/5]

Vector representation:
```
 0 -4 -1  0
 1 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_124

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+4, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R3 chain: (a, b, 0, d+k) →* (a, b+k, 0, d). c=0 so R1 and R2 don't match.
theorem r3_chain : ∀ k a b d,
    ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: (a+k, b, c, 0) →* (a, b, c+2*k, 0). d=0 and b=0 so R1-R3 don't match.
theorem r4_chain : ∀ k a c,
    ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Climb step: (j, 1, c+1, j) → R2 → R3 → (j+1, 1, c, j+1)
-- b=1<4 so R1 no. b=1>=1 and c+1>=1 so R2 fires.
-- Then (j+1, 0, c, j+2): b=0 so R1,R2 no. c could be >=1, but R3 checks d+1 first.
-- d=j+2>=1 so R3 fires.
theorem climb_step : ∀ j c,
    ⟨j, 1, c+1, j⟩ [fm]⊢* ⟨j+1, 1, c, j+1⟩ := by
  intro j c
  step fm; step fm
  ring_nf; finish

-- Climb iteration
theorem climb_iter : ∀ c j,
    ⟨j, 1, c, j⟩ [fm]⊢* ⟨j+c, 1, 0, j+c⟩ := by
  intro c; induction' c with c ih <;> intro j
  · simp; exists 0
  rw [show j + (c + 1) = (j + 1) + c from by ring]
  apply stepStar_trans (climb_step j c)
  apply stepStar_trans (ih (j + 1))
  ring_nf; finish

-- Full climb from (0, 0, N+2, 0) to (N+1, N+2, 0, 0)
theorem full_climb : ∀ N,
    ⟨0, 0, N+2, 0⟩ [fm]⊢* ⟨N+1, N+2, 0, 0⟩ := by
  intro N
  step fm; step fm
  apply stepStar_trans
  · have h := climb_iter (N+1) 0
    simp only [Nat.zero_add] at h
    exact h
  have h := r3_chain (N+1) (N+1) 1 0
  simp only [Nat.zero_add] at h
  rw [show 1 + (N + 1) = N + 2 from by ring] at h
  exact h

-- Big reduce as stepPlus: (a+1, b+8, 0, 0) →⁺ (a, b, 0, 0)
theorem big_reduce_plus : ∀ a b,
    ⟨a+1, b+8, 0, 0⟩ [fm]⊢⁺ ⟨a, b, 0, 0⟩ := by
  intro a b; execute fm 3

-- Tail b=0: drain + climb
theorem tail_b0 : ∀ a,
    ⟨a+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*a+1, 2*a+2, 0, 0⟩ := by
  intro a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0⟩ = some ⟨a, 0, 2, 0⟩; rfl
  apply stepStar_trans
  · have h := r4_chain a 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * a = 2 * a + 2 from by ring] at h
    exact h
  exact full_climb (2*a)

-- Tail b=1
theorem tail_b1 : ∀ a,
    ⟨a+1, 1, 0, 0⟩ [fm]⊢⁺ ⟨a+2, 3, 0, 0⟩ := by
  intro a; execute fm 7

-- Tail b=2
theorem tail_b2 : ∀ a,
    ⟨a+1, 2, 0, 0⟩ [fm]⊢⁺ ⟨a+2, 4, 0, 0⟩ := by
  intro a; execute fm 7

-- Tail b=3
theorem tail_b3 : ∀ a,
    ⟨a+1, 3, 0, 0⟩ [fm]⊢⁺ ⟨a+2, 5, 0, 0⟩ := by
  intro a; execute fm 7

-- Tail b=4: drain + climb
theorem tail_b4 : ∀ a,
    ⟨a+2, 4, 0, 0⟩ [fm]⊢⁺ ⟨2*a+2, 2*a+3, 0, 0⟩ := by
  intro a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 2, 4, 0, 0⟩ = some ⟨a + 1, 4, 2, 0⟩; rfl
  step fm
  apply stepStar_trans
  · have h := r4_chain (a+1) 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * (a + 1) = 2 * a + 3 from by ring] at h
    exact h
  exact full_climb (2*a+1)

-- Tail b=5
theorem tail_b5 : ∀ a,
    ⟨a+1, 5, 0, 0⟩ [fm]⊢⁺ ⟨a+1, 2, 0, 0⟩ := by
  intro a; execute fm 5

-- Tail b=6
theorem tail_b6 : ∀ a,
    ⟨a+1, 6, 0, 0⟩ [fm]⊢⁺ ⟨a+1, 3, 0, 0⟩ := by
  intro a; execute fm 5

-- Tail b=7
theorem tail_b7 : ∀ a,
    ⟨a+1, 7, 0, 0⟩ [fm]⊢⁺ ⟨a+1, 4, 0, 0⟩ := by
  intro a; execute fm 5

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fun q ↦ ∃ a b, q = (⟨a+1, b, 0, 0⟩ : Q) ∧ 3*(a+1) > b)
  · intro q ⟨a, b, hq, hab⟩
    subst hq
    rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b
    · -- b = 0
      exact ⟨_, ⟨2*a, 2*a+2, by ring_nf, by omega⟩, tail_b0 a⟩
    · -- b = 1
      exact ⟨_, ⟨a+1, 3, by ring_nf, by omega⟩, tail_b1 a⟩
    · -- b = 2
      exact ⟨_, ⟨a+1, 4, by ring_nf, by omega⟩, tail_b2 a⟩
    · -- b = 3
      exact ⟨_, ⟨a+1, 5, by ring_nf, by omega⟩, tail_b3 a⟩
    · -- b = 4
      have ha : a ≥ 1 := by omega
      have h := tail_b4 (a - 1)
      rw [show a - 1 + 2 = a + 1 from by omega] at h
      have heq1 : 2 * (a - 1) + 2 = 2 * a := by omega
      have heq2 : 2 * (a - 1) + 3 = 2 * a + 1 := by omega
      refine ⟨_, ⟨2*a-1, 2*a+1, ?_, ?_⟩, h⟩
      · show (2*(a-1)+2, 2*(a-1)+3, 0, 0) = (2*a-1+1, 2*a+1, 0, 0)
        rw [heq1, heq2]; congr 1; omega
      · have h2 : 2 * a - 1 + 1 = 2 * a := by omega
        rw [h2]; omega
    · -- b = 5
      exact ⟨_, ⟨a, 2, rfl, by omega⟩, tail_b5 a⟩
    · -- b = 6
      exact ⟨_, ⟨a, 3, rfl, by omega⟩, tail_b6 a⟩
    · -- b = 7
      exact ⟨_, ⟨a, 4, rfl, by omega⟩, tail_b7 a⟩
    · -- b = b + 8
      have ha : a ≥ 2 := by omega
      have heq : a - 1 + 1 = a := by omega
      refine ⟨_, ⟨a-1, b, ?_, ?_⟩, big_reduce_plus a b⟩
      · show (a, b, 0, 0) = (a - 1 + 1, b, 0, 0); rw [heq]
      · rw [heq]; omega
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_124

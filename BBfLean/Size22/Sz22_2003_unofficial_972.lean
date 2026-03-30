import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #972: [4/15, 33/14, 5/2, 7/11, 84/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_972

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b+1, c, d+1, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 2, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 + k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n + 1, n, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 1, n + 1, 0⟩ := by
  rcases n with _ | _ | n
  · -- n = 0
    execute fm 10
  · -- n = 1
    execute fm 14
  · -- n + 2
    -- Phase 1: R5: (0,0,2(n+2)+1,(n+2),0) -> (2,1,2(n+2),(n+2)+1,0)
    have h1 : ⟨0, 0, 2 * (n + 2) + 1, n + 2, 0⟩ [fm]⊢⁺ ⟨2, 1, 2 * (n + 2), n + 3, 0⟩ := by
      rw [show 2 * (n + 2) + 1 = (2 * (n + 2)) + 1 from by ring]
      apply step_stepPlus
      show fm ⟨0, 0, (2 * (n + 2)) + 1, n + 2, 0⟩ = some ⟨2, 1, 2 * (n + 2), n + 3, 0⟩
      unfold fm; simp only
    -- Phase 2: R1: (2,1,2(n+2),n+3,0) -> (4,0,2(n+2)-1,n+3,0)
    have h2 : ⟨2, 1, 2 * (n + 2), n + 3, 0⟩ [fm]⊢* ⟨4, 0, 2 * n + 3, n + 3, 0⟩ := by
      rw [show 2 * (n + 2) = (2 * n + 3) + 1 from by ring]
      step fm; ring_nf; finish
    -- Phase 3: R2R1 chain n rounds: (4,0,2n+3,n+3,0) -> (n+4,0,n+3,3,n)
    -- Using r2r1_chain with k=n: (a+2,0,c+n,d+n,e) -> (a+2+n,0,c,d,e+n)
    -- a+2=4, c+n=2n+3 -> c=n+3, d+n=n+3 -> d=3, e=0
    have h3 : ⟨4, 0, 2 * n + 3, n + 3, 0⟩ [fm]⊢* ⟨n + 4, 0, n + 3, 3, n⟩ := by
      have := r2r1_chain n 2 (n + 3) 3 0
      simp only [show (n + 3) + n = 2 * n + 3 from by ring,
          show 3 + n = n + 3 from by ring,
          show 2 + 2 + n = n + 4 from by ring,
          show 0 + n = n from by ring] at this
      exact this
    -- Phase 4: 3 more R2R1 rounds: (n+4,0,n+3,3,n) -> (n+7,0,n,0,n+3)
    have h4 : ⟨n + 4, 0, n + 3, 3, n⟩ [fm]⊢* ⟨n + 7, 0, n, 0, n + 3⟩ := by
      have := r2r1_chain 3 (n + 2) n 0 n
      simp only [show (n + 2) + 2 = n + 4 from by ring,
          show 0 + 3 = 3 from by ring,
          show (n + 2) + 2 + 3 = n + 7 from by ring] at this
      exact this
    -- Phase 5: R3 drain: (n+7,0,n,0,n+3) -> (0,0,2n+7,0,n+3)
    have h5 : ⟨n + 7, 0, n, 0, n + 3⟩ [fm]⊢* ⟨0, 0, 2 * n + 7, 0, n + 3⟩ := by
      have := r3_drain (n + 7) n (n + 3)
      rw [show n + (n + 7) = 2 * n + 7 from by ring] at this
      exact this
    -- Phase 6: R4 drain: (0,0,2n+7,0,n+3) -> (0,0,2n+7,n+3,0)
    have h6 : ⟨0, 0, 2 * n + 7, 0, n + 3⟩ [fm]⊢* ⟨0, 0, 2 * n + 7, n + 3, 0⟩ := by
      have := r4_drain (n + 3) (2 * n + 7) 0
      rw [show 0 + (n + 3) = n + 3 from by ring] at this
      exact this
    -- Compose: 2*(n+2+1)+1 = 2n+7, n+2+1 = n+3
    have goal_rw : 2 * (n + 2 + 1) + 1 = 2 * n + 7 := by ring
    have goal_rw2 : n + 2 + 1 = n + 3 := by ring
    rw [goal_rw, goal_rw2]
    exact stepPlus_stepStar_stepPlus h1
      (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 1, n, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, 2 * n + 1, n, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 1, n + 1, 0⟩
  exact main_trans n

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #933: [4/15, 33/14, 25/2, 7/11, 242/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_933

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n * n + 2 * n + 3, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨0, 0, n * n + 4 * n + 6, 2 * n + 4, 0⟩ := by
  -- R5 step
  rw [show n * n + 2 * n + 3 = (n * n + 2 * n + 2) + 1 from by ring]
  step fm
  -- After step fm, state is (1, 0, n*n+2*n+2, d', 2) where d' = 2*n+2 in some form
  -- R2/R1 chain: (1, 0, n²+2n+2, 2n+2, 2) ⊢* (2n+3, 0, n², 0, 2n+4)
  -- Use r2r1_chain with K=2n+2, a=0, c=n², e=1
  -- (0+1, 0, n²+(2n+2), 2n+2, 1+1) ⊢* (0+(2n+2)+1, 0, n², 0, 1+(2n+2)+1)
  have h2 := r2r1_chain (2 * n + 2) 0 (n * n) 1
  simp only [Nat.zero_add] at h2
  rw [show n * n + (2 * n + 2) = n * n + 2 * n + 2 from by ring] at h2
  -- h2: (1, 0, n²+2n+2, 2n+2, 1+1) ⊢* (2n+3, 0, n², 0, 2n+4)
  -- R3 drain
  have h3 := r3_drain (2 * n + 3) (n * n) (1 + (2 * n + 2) + 1)
  rw [show n * n + 2 * (2 * n + 3) = n * n + 4 * n + 6 from by ring] at h3
  -- R4 drain
  have h4 := r4_drain (1 + (2 * n + 2) + 1) (n * n + 4 * n + 6) 0
  -- Compose: h2 then h3 then h4
  -- Need to match the goal after step fm with h2's LHS
  -- After step fm, d is in some normal form. Let's use convert.
  apply stepStar_trans
  · convert h2 using 2
  apply stepStar_trans
  · convert h3 using 2
  convert h4 using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n * n + 2 * n + 3, 2 * n + 2, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, n * n + 2 * n + 3, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨0, 0, (n + 1) * (n + 1) + 2 * (n + 1) + 3, 2 * (n + 1) + 2, 0⟩
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 3 = n * n + 4 * n + 6 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_933

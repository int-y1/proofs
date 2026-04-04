import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1904: [9/35, 65/33, 14/3, 11/13, 507/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1904

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | _ => none

theorem f_to_e : ∀ k, ⟨a, 0, 0, d, e, f + k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih generalizing e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1) (f := f))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e f,
    ⟨a, b + 1, 0, d + k, e + k, f⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ (b + 1) _ _ (f + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b c e f,
    ⟨a, b + k, c, 0, e + k, f⟩ [fm]⊢* ⟨a, b, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b c e f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ (c + 1) _ (f + 1))
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a b f,
    ⟨a, b + 1, k, 0, 0, f⟩ [fm]⊢* ⟨a + k, b + k + 1, 0, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b f
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 1) _)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ a b d f,
    ⟨a, b + k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) _ (d + 1) _)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n * n + n + 1, 0, 0, n + 1, 0, 2 * n + 2⟩ [fm]⊢⁺
    ⟨n * n + 3 * n + 3, 0, 0, n + 2, 0, 2 * n + 4⟩ := by
  -- Phase 1: f_to_e (2n+2 steps)
  have h1 := f_to_e (2 * n + 2) (a := n * n + n + 1) (d := n + 1) (e := 0) (f := 0)
  -- h1 : (n*n+n+1, 0, 0, n+1, 0, 0+(2*n+2)) →* (n*n+n+1, 0, 0, n+1, 0+(2*n+2), 0)
  -- Phase 2: R5 step
  have h2 : ⟨(n * n + n) + 1, 0, 0, n + 1, 0 + (2 * n + 2), 0⟩ [fm]⊢
             ⟨n * n + n, 1, 0, n + 1, 0 + (2 * n + 2), 2⟩ := by simp [fm]
  -- Phase 3: R2,R1 chain (k = n+1)
  have h3 := r2r1_chain (n + 1) (n * n + n) 0 0 (n + 1) 2
  -- h3 : (n*n+n, 0+1, 0, 0+(n+1), (n+1)+(n+1), 2) →* (n*n+n, 0+(n+1)+1, 0, 0, n+1, 2+(n+1))
  -- Phase 4: R2 drain (k = n+1)
  have h4 := r2_drain (n + 1) (n * n + n) 1 0 0 (2 + (n + 1))
  -- h4 : (n*n+n, 1+(n+1), 0, 0, 0+(n+1), 2+(n+1)) →* (n*n+n, 1, 0+(n+1), 0, 0, 2+(n+1)+(n+1))
  -- Phase 5: R3,R1 chain (k = 0+(n+1))
  have h5 := r3r1_chain (0 + (n + 1)) (n * n + n) 0 (2 + (n + 1) + (n + 1))
  -- h5 : (n*n+n, 0+1, 0+(n+1), 0, 0, ...) →* (n*n+n+(0+(n+1)), 0+(0+(n+1))+1, 0, 0, 0, ...)
  -- Phase 6: R3 drain (k = n+2)
  have h6 := r3_drain (n + 2) (n * n + n + (0 + (n + 1))) 0 0 (2 + (n + 1) + (n + 1))
  -- h6 : (..., 0+(n+2), 0, 0, 0, ...) →* (...+(n+2), 0, 0, 0+(n+2), 0, ...)
  -- Compose: h1 + h2 + h3 + h4 + h5 + h6
  -- First connect h1 to the ⊢⁺ goal
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus h1
  rw [show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply step_stepStar_stepPlus h2
  -- Now goal: (n*n+n, 1, 0, n+1, 0+(2*n+2), 2) [fm]⊢* target
  -- Need to connect to h3. h3 starts from (n*n+n, 0+1, 0, 0+(n+1), (n+1)+(n+1), 2)
  -- 1 = 0+1 ✓ (by def)
  -- n+1 = 0+(n+1) ✓ (by def? no, 0+n+1 = n+1 yes)
  -- 0+(2*n+2) = (n+1)+(n+1) ✓
  -- So we need show these are equal
  have eq3 : (⟨n * n + n, 1, 0, n + 1, 0 + (2 * n + 2), 2⟩ : Q) =
              ⟨n * n + n, 0 + 1, 0, 0 + (n + 1), (n + 1) + (n + 1), 2⟩ := by
    simp; omega
  rw [eq3]
  apply stepStar_trans h3
  -- Now: (n*n+n, 0+(n+1)+1, 0, 0, n+1, 2+(n+1)) to target
  -- Need to connect to h4: (n*n+n, 1+(n+1), 0, 0, 0+(n+1), 2+(n+1))
  have eq4 : (⟨n * n + n, 0 + (n + 1) + 1, 0, 0, n + 1, 2 + (n + 1)⟩ : Q) =
              ⟨n * n + n, 1 + (n + 1), 0, 0, 0 + (n + 1), 2 + (n + 1)⟩ := by
    simp; omega
  rw [eq4]
  apply stepStar_trans h4
  -- Now: (n*n+n, 1, 0+(n+1), 0, 0, 2+(n+1)+(n+1)) to target
  -- Connect to h5: (n*n+n, 0+1, 0+(n+1), 0, 0, 2+(n+1)+(n+1))
  have eq5 : (⟨n * n + n, 1, 0 + (n + 1), 0, 0, 2 + (n + 1) + (n + 1)⟩ : Q) =
              ⟨n * n + n, 0 + 1, 0 + (n + 1), 0, 0, 2 + (n + 1) + (n + 1)⟩ := by
    simp
  rw [eq5]
  apply stepStar_trans h5
  -- Now: (n*n+n+(0+(n+1)), 0+(0+(n+1))+1, 0, 0, 0, ...) to target
  -- Connect to h6: (..., 0+(n+2), 0, 0, 0, ...)
  have eq6 : (⟨n * n + n + (0 + (n + 1)), 0 + (0 + (n + 1)) + 1, 0, 0, 0, 2 + (n + 1) + (n + 1)⟩ : Q) =
              ⟨n * n + n + (0 + (n + 1)), 0 + (n + 2), 0, 0, 0, 2 + (n + 1) + (n + 1)⟩ := by
    simp
  rw [eq6]
  apply stepStar_trans h6
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + n + 1, 0, 0, n + 1, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  have h := main_trans n
  convert h using 2; ring_nf

import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #190: [1/6, 2/35, 275/2, 9/55, 98/3]

Vector representation:
```
-1 -1  0  0  0
 1  0 -1 -1  0
-1  0  2  0  1
 0  2 -1  0 -1
 1 -1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_190

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

private theorem r2_chain : ∀ k a c d e,
    ⟨a, (0:ℕ), c+k, d+k, e⟩ [fm]⊢* ⟨a+k, (0:ℕ), c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

private theorem flush : ∀ k a c e,
    ⟨a+k, (0:ℕ), c, (0:ℕ), e⟩ [fm]⊢* ⟨a, (0:ℕ), c+2*k, (0:ℕ), e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

private theorem r4_chain : ∀ k b c e,
    ⟨(0:ℕ), b, c+k, (0:ℕ), e+k⟩ [fm]⊢* ⟨(0:ℕ), b+2*k, c, (0:ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

private theorem r5r1_chain : ∀ k d,
    ⟨(0:ℕ), 2*k+1, (0:ℕ), d, (0:ℕ)⟩ [fm]⊢* ⟨(1:ℕ), (0:ℕ), (0:ℕ), d+2*k+2, (0:ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro d
  · step fm; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

private theorem phase : ∀ d, ∀ a e,
    ⟨a, (0:ℕ), (2:ℕ), d, e⟩ [fm]⊢* ⟨(0:ℕ), (0:ℕ), 2*a+d+2, (0:ℕ), a+d+e⟩ := by
  intro d; induction' d using Nat.strongRecOn with d ih; intro a e
  rcases d with _ | _ | d
  · -- d = 0: flush
    have h := flush a 0 2 e
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * a = 2 * a + 0 + 2 from by ring,
        show e + a = a + 0 + e from by ring] at h
    exact h
  · -- d = 1: R2 then flush
    have h1 := r2_chain 1 a 1 0 e
    simp only [show 1 + 1 = 2 from rfl, show 0 + 1 = 1 from rfl] at h1
    have h2 := flush (a + 1) 0 1 e
    simp only [Nat.zero_add] at h2
    apply stepStar_trans h1
    rw [show 1 + 2 * (a + 1) = 2 * a + 1 + 2 from by ring,
        show e + (a + 1) = a + 1 + e from by ring] at h2
    exact h2
  · -- d ≥ 2: R2×2, R3, then IH on d
    have h1 := r2_chain 2 a 0 d e
    simp only [show 0 + 2 = 2 from rfl] at h1
    apply stepStar_trans h1
    -- Now at ⟨a+2, 0, 0, d, e⟩. R3 fires.
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm  -- R3: ⟨a+1, 0, 2, d, e+1⟩
    apply stepStar_trans (ih d (by omega) (a + 1) (e + 1))
    rw [show 2 * (a + 1) + d + 2 = 2 * a + (d + 2) + 2 from by ring,
        show a + 1 + d + (e + 1) = a + (d + 2) + e from by ring]; finish

private theorem main_trans (d : ℕ) :
    ⟨(1:ℕ), (0:ℕ), (0:ℕ), d+1, (0:ℕ)⟩ [fm]⊢⁺ ⟨(1:ℕ), (0:ℕ), (0:ℕ), 2*d+3, (0:ℕ)⟩ := by
  -- R3: ⟨0, 0, 2, d+1, 1⟩
  step fm
  -- Phase: ⟨0, 0, 2, d+1, 1⟩ →* ⟨0, 0, d+3, 0, d+2⟩
  apply stepStar_trans (c₂ := ⟨(0:ℕ), (0:ℕ), d+3, (0:ℕ), d+2⟩)
  · have h := phase (d + 1) 0 1
    simp only [show 2 * 0 + (d + 1) + 2 = d + 3 from by ring,
               show 0 + (d + 1) + 1 = d + 2 from by ring] at h
    exact h
  -- R4 chain: ⟨0, 0, d+3, 0, d+2⟩ →* ⟨0, 2*d+4, 1, 0, 0⟩
  apply stepStar_trans (c₂ := ⟨(0:ℕ), 2*d+4, (1:ℕ), (0:ℕ), (0:ℕ)⟩)
  · have h := r4_chain (d + 2) 0 1 0
    simp only [show 1 + (d + 2) = d + 3 from by ring,
               show 0 + (d + 2) = d + 2 from by ring,
               show 0 + 2 * (d + 2) = 2 * d + 4 from by ring] at h
    exact h
  -- 4 steps: R5, R1, R2, R1
  rw [show 2 * d + 4 = (2 * d + 1) + 1 + 1 + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  rw [show (2:ℕ) = 1 + 1 from by ring]
  step fm  -- R2
  step fm  -- R1
  -- R5+R1 chain: ⟨0, 2*d+1, 0, 1, 0⟩ →* ⟨1, 0, 0, 2*d+3, 0⟩
  apply stepStar_trans (r5r1_chain d 1)
  rw [show 1 + 2 * d + 2 = 2 * d + 3 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨(1:ℕ), (0:ℕ), (0:ℕ), d+1, (0:ℕ)⟩) 0
  intro d
  exact ⟨2*d+2, main_trans d⟩

end Sz22_2003_unofficial_190

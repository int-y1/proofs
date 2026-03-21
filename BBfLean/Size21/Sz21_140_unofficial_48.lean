import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #48: [35/6, 4/55, 143/2, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_48

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

-- R3 repeated: (a+k, 0, 0, d, e, f) →* (a, 0, 0, d, e+k, f+k)
theorem r3_repeat : ∀ k, ∀ a e f, ⟨a+k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e+k, f+k⟩ := by
  intro k; induction' k with k h <;> intro a e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: (0, b, 0, d+k, e, f) →* (0, b+k, 0, d, e, f)
theorem r4_repeat : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2 chain: (a, 0, c+k, d, k, f) →* (a+2*k, 0, c, d, 0, f)
theorem r2_chain : ∀ k, ∀ a c, ⟨a, 0, c+k, d, k, f⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1R1R2 rounds
theorem r1r1r2_rounds : ∀ k, ∀ c d e g, ⟨2, b+2*k, c, d, e+k, g⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, g⟩ := by
  intro k; induction' k with k h <;> intro c d e g
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  rw [show e + k + 1 = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Full cycle from (n+2, 0, 0, n+1, 0, G) →⁺ (n+3, 0, 0, n+2, 0, G+n+1)
-- This handles n ≥ 0 (the canonical state has a ≥ 2, d ≥ 1)
theorem cycle (n G : ℕ) : ⟨n+2, 0, 0, n+1, 0, G⟩ [fm]⊢⁺ ⟨n+3, 0, 0, n+2, 0, G+n+1⟩ := by
  -- Phase 1: R3 (n+2) times: → (0, 0, 0, n+1, n+2, G+n+2)
  -- First step gives stepPlus
  apply step_stepStar_stepPlus (c₂ := ⟨n+1, 0, 0, n+1, 1, G+1⟩)
  · show fm ⟨(n+1)+1, 0, 0, n+1, 0, G⟩ = some ⟨n+1, 0, 0, n+1, 1, G+1⟩; simp [fm]
  -- Remaining n+1 R3 steps
  apply stepStar_trans (c₂ := ⟨0, 0, 0, n+1, n+2, G+n+2⟩)
  · have h := r3_repeat (d := n+1) (n+1) 0 1 (G+1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  -- Phase 2: R4 (n+1) times: → (0, n+1, 0, 0, n+2, G+n+2)
  apply stepStar_trans (c₂ := ⟨0, n+1, 0, 0, n+2, G+n+2⟩)
  · have h := r4_repeat (e := n+2) (f := G+n+2) (n+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 one step: → (0, n+1, 1, 1, n+2, G+n+1)
  apply stepStar_trans (c₂ := ⟨0, n+1, 1, 1, n+2, G+n+1⟩)
  · have h5 : fm ⟨0, n+1, 0, 0, n+2, (G+n+1)+1⟩ = some ⟨0, n+1, 1, 1, n+2, G+n+1⟩ := by
      simp [fm]
    rw [show (G+n+1)+1 = G+n+2 from by ring] at h5
    exact step_stepStar h5
  -- Phase 4: R2 one step: → (2, n+1, 0, 1, n+1, G+n+1)
  apply stepStar_trans (c₂ := ⟨2, n+1, 0, 1, n+1, G+n+1⟩)
  · have h2 : fm ⟨0, n+1, 0+1, 1, (n+1)+1, G+n+1⟩ = some ⟨0+2, n+1, 0, 1, n+1, G+n+1⟩ := by
      simp [fm]
    simp only [Nat.zero_add] at h2
    rw [show (n+1)+1 = n+2 from by ring] at h2
    exact step_stepStar h2
  -- Phase 5: Interleaved phase, case split on parity of n+1
  rcases Nat.even_or_odd (n+1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n+1 = 2K
    rw [show K + K = 2 * K from by ring] at hK
    -- (2, 2K, 0, 1, 2K, G+n+1)
    -- R1R1R2 K rounds: → (2, 0, K, 1+2K, K, G+n+1)
    apply stepStar_trans (c₂ := ⟨2, 0, K, 1+2*K, K, G+n+1⟩)
    · have h := r1r1r2_rounds (b := 0) K 0 1 K (G+n+1)
      rw [show (0 : ℕ) + 2 * K = 2 * K from by ring,
          show K + K = 2 * K from by ring,
          show (0 : ℕ) + K = K from by ring] at h
      rw [hK]; exact h
    -- R2 chain K steps: → (2+2K, 0, 0, 1+2K, 0, G+n+1)
    apply stepStar_trans (c₂ := ⟨2+2*K, 0, 0, 1+2*K, 0, G+n+1⟩)
    · have h := r2_chain (d := 1+2*K) (f := G+n+1) K 2 0
      rw [show (0 : ℕ) + K = K from by ring] at h; exact h
    -- Match target: need (2+2*K, 0, 0, 1+2*K, 0, G+n+1) = (n+3, 0, 0, n+2, 0, G+n+1)
    have h2k : 2 + 2 * K = n + 3 := by omega
    have h1k : 1 + 2 * K = n + 2 := by omega
    rw [h2k, h1k]; finish
  · -- n+1 = 2K+1
    -- (2, 2K+1, 0, 1, 2K+1, G+n+1)
    -- R1R1R2 K rounds: → (2, 1, K, 2K+1, K+1, G+n+1)
    apply stepStar_trans (c₂ := ⟨2, 1, K, 2*K+1, K+1, G+n+1⟩)
    · have h := r1r1r2_rounds (b := 1) K 0 1 (K+1) (G+n+1)
      rw [show (1 : ℕ) + 2 * K = 2 * K + 1 from by ring,
          show K + 1 + K = 2 * K + 1 from by ring,
          show (0 : ℕ) + K = K from by ring] at h
      rw [hK]; exact h
    -- R1 step: → (1, 0, K+1, 2+2K, K+1, G+n+1)
    apply stepStar_trans (c₂ := ⟨1, 0, K+1, 2+2*K, K+1, G+n+1⟩)
    · have h1 : fm ⟨1+1, 0+1, K, 2*K+1, K+1, G+n+1⟩ = some ⟨1, 0, K+1, (2*K+1)+1, K+1, G+n+1⟩ := by
        simp [fm]
      rw [show (2*K+1)+1 = 2+2*K from by ring] at h1
      exact step_stepStar h1
    -- R2 chain (K+1) steps: → (1+2*(K+1), 0, 0, 2+2K, 0, G+n+1)
    apply stepStar_trans (c₂ := ⟨1+2*(K+1), 0, 0, 2+2*K, 0, G+n+1⟩)
    · have h := r2_chain (d := 2+2*K) (f := G+n+1) (K+1) 1 0
      rw [show (0 : ℕ) + (K + 1) = K + 1 from by ring] at h; exact h
    -- Match target
    have h3k : 1 + 2 * (K + 1) = n + 3 := by omega
    have h2k : 2 + 2 * K = n + 2 := by omega
    rw [h3k, h2k]; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0,0) →* (2,0,0,1,0,0) in 3 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 3)
  -- Canonical form: (n+2, 0, 0, n+1, 0, G) parameterized by (n, G)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, G⟩ ↦ ⟨n+2, 0, 0, n+1, 0, G⟩) ⟨0, 0⟩
  intro ⟨n, G⟩; exact ⟨⟨n+1, G+n+1⟩, cycle n G⟩

end Sz21_140_unofficial_48

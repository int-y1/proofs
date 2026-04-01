import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1240: [5/6, 77/2, 4/35, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  0
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1240

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (0, b, 0, k, e) →* (0, b + 2k, 0, 0, e)
theorem r4_drain : ∀ k b e, ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) e)
    ring_nf; finish

-- R3R2R2 drain: (0, 0, c + k, d + 1, e) →* (0, 0, c, d + k + 1, e + 2k)
theorem r3r2r2_drain : ∀ k c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih c (d + 1) (e + 1 + 1))
    ring_nf; finish

-- Spiral round: (0, b + 3, c, 0, e + 1) →* (0, b, c + 2, 0, e)
theorem spiral_round : ∀ b c e,
    ⟨(0 : ℕ), b + 3, c, 0, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2, 0, e⟩ := by
  intro b c e
  -- R5: (0, b+3, c, 0, e+1) → (1, b+3, c, 1, e)
  step fm
  -- R1: (1, b+3, c, 1, e) → (0, b+2, c+1, 1, e)
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm
  -- R3: (0, b+2, c+1, 1, e) → (2, b+2, c, 0, e)
  step fm
  -- R1: (2, b+2, c, 0, e) → (1, b+1, c+1, 0, e)
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm
  -- R1: (1, b+1, c+1, 0, e) → (0, b, c+2, 0, e)
  step fm
  finish

-- Spiral chain: k rounds
theorem spiral_chain : ∀ k b c e,
    ⟨(0 : ℕ), b + 3 * k, c, 0, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) c (e + 1))
    apply stepStar_trans (spiral_round b (c + 2 * k) e)
    ring_nf; finish

-- Tail for remainder 0: (0, 0, c, 0, e + 1) →⁺ (0, 0, 0, c + 2, e + 2c + 1)
theorem tail_r0 (c e : ℕ) :
    ⟨(0 : ℕ), 0, c, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, c + 2, e + 2 * c + 1⟩ := by
  -- R5: (0,0,c,0,e+1) → (1,0,c,1,e)
  step fm
  -- R2: (1,0,c,1,e) → (0,0,c,2,e+1)
  step fm
  -- Drain c rounds from (0,0,c,2,e+1): (0,0,0+c,1+1,e+1) → (0,0,0,c+2,e+2c+1)
  rw [show c = 0 + c from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain c 0 1 (e + 1))
  ring_nf; finish

-- Tail for remainder 1: (0, 1, c, 0, e + 1) →⁺ (0, 0, 0, c + 2, e + 2c + 2)
theorem tail_r1 (c e : ℕ) :
    ⟨(0 : ℕ), 1, c, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, c + 2, e + 2 * c + 2⟩ := by
  -- R5: (0,1,c,0,e+1) → (1,1,c,1,e)
  step fm
  -- R1: (1,1,c,1,e) → (0,0,c+1,1,e)
  step fm
  -- Drain c+1 rounds from (0,0,c+1,1,e): (0,0,0+(c+1),0+1,e) → (0,0,0,c+2,e+2c+2)
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (c + 1) 0 0 e)
  ring_nf; finish

-- Tail for remainder 2: (0, 2, c, 0, e + 1) →⁺ (0, 0, 0, c + 2, e + 2c + 3)
theorem tail_r2 (c e : ℕ) :
    ⟨(0 : ℕ), 2, c, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, c + 2, e + 2 * c + 3⟩ := by
  -- R5: (0,2,c,0,e+1) → (1,2,c,1,e)
  step fm
  -- R1: (1,2,c,1,e) → (0,1,c+1,1,e)
  step fm
  -- R3: (0,1,c+1,1,e) → (2,1,c,0,e)
  step fm
  -- R1: (2,1,c,0,e) → (1,0,c+1,0,e)
  step fm
  -- R2: (1,0,c+1,0,e) → (0,0,c+1,1,e+1)
  step fm
  -- Drain c+1 rounds from (0,0,c+1,1,e+1): → (0,0,0,c+2,e+2c+3)
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (c + 1) 0 0 (e + 1))
  ring_nf; finish

-- Combined spiral + tail + drain: (0, B, C, 0, E) →⁺ (0, 0, 0, D, E + 2C + B)
-- where D exists and D ≥ 2 (when C ≥ 2)
-- Requires 3 * E > B (ensures enough fuel for spiral rounds)
theorem spiral_tail_drain : ∀ B, ∀ C E, 3 * E > B → C ≥ 2 →
    ∃ D, D ≥ 2 ∧ E + 2 * C + B ≥ D + 1 ∧
    (⟨(0 : ℕ), B, C, 0, E⟩ : Q) [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D, E + 2 * C + B⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ihB
  intro C E hE hC
  rcases B with _ | _ | _ | B'
  · -- B = 0
    obtain ⟨e', rfl⟩ : ∃ e', E = e' + 1 := ⟨E - 1, by omega⟩
    refine ⟨C + 2, by omega, by omega, ?_⟩
    have := tail_r0 C e'
    convert this using 2; ring_nf
  · -- B = 1
    obtain ⟨e', rfl⟩ : ∃ e', E = e' + 1 := ⟨E - 1, by omega⟩
    refine ⟨C + 2, by omega, by omega, ?_⟩
    have := tail_r1 C e'
    convert this using 2; ring_nf
  · -- B = 2
    obtain ⟨e', rfl⟩ : ∃ e', E = e' + 1 := ⟨E - 1, by omega⟩
    refine ⟨C + 2, by omega, by omega, ?_⟩
    have := tail_r2 C e'
    convert this using 2; ring_nf
  · -- B = B' + 3
    obtain ⟨e', rfl⟩ : ∃ e', E = e' + 1 := ⟨E - 1, by omega⟩
    obtain ⟨D, hD2, hDe, hstep⟩ := ihB B' (by omega) (C + 2) e' (by omega) (by omega)
    refine ⟨D, hD2, by omega, ?_⟩
    apply stepStar_stepPlus_stepPlus (spiral_round B' C e')
    convert hstep using 2; ring_nf

-- Opening: (0, 2d, 0, 0, e) →* (0, 2d - 3, 2, 0, e - 1), needs d ≥ 2, e ≥ 1
-- More precisely: (0, b + 3, 0, 0, e + 1) →* (0, b, 2, 0, e)
theorem opening (b e : ℕ) :
    ⟨(0 : ℕ), b + 3, 0, 0, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, 2, 0, e⟩ := by
  -- R5: (0, b+3, 0, 0, e+1) → (1, b+3, 0, 1, e)
  step fm
  -- R1: (1, b+3, 0, 1, e) → wait, b+3 ≥ 1, so R1 fires
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm
  -- (0, b+2, 1, 1, e)
  -- R3: (0, b+2, 1, 1, e) → (2, b+2, 0, 0, e)
  step fm
  -- R1: (2, b+2, 0, 0, e) → (1, b+1, 1, 0, e)
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm
  -- R1: (1, b+1, 1, 0, e) → but b+1 ≥ 1, R1 fires
  -- Wait: (1, b+1, 1, 0, e): a=1, b=b+1 ≥ 1. R1: (0, b, 2, 0, e)
  step fm
  finish

-- Main transition: (0,0,0,d,e+1) →⁺ (0,0,0,D,e+2d+1) for some D ≥ 2
-- Requires d ≥ 2 and e ≥ d
theorem main_trans (d e : ℕ) (hd : d ≥ 2) (he : e ≥ d) :
    ∃ D, D ≥ 2 ∧ e + 2 * d ≥ D ∧
    (⟨(0 : ℕ), 0, 0, d, e + 1⟩ : Q) [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D, e + 2 * d + 1⟩ := by
  -- Phase 1: R4 drain, d steps: (0,0,0,d,e+1) →* (0,2d,0,0,e+1)
  -- Phase 2: Opening, 5 steps: (0,2d,0,0,e+1) →* (0,2d-3,2,0,e)
  -- Phase 3: spiral_tail_drain with B=2d-3, C=2, E=e
  have hb : 2 * d ≥ 3 := by omega
  -- Express d as appropriate form
  obtain ⟨b, rfl⟩ : ∃ b, d = b + 2 := ⟨d - 2, by omega⟩
  -- Now d = b + 2, so 2d = 2b + 4, 2d - 3 = 2b + 1
  -- R4 drain: (0, 0, 0, b+2, e+1) →* (0, 2(b+2), 0, 0, e+1)
  have hr4 : (⟨(0 : ℕ), 0, 0, b + 2, e + 1⟩ : Q) [fm]⊢* ⟨0, 2 * (b + 2), 0, 0, e + 1⟩ := by
    have := r4_drain (b + 2) 0 (e + 1)
    simpa using this
  -- Opening: (0, 2b+4, 0, 0, e+1) →* (0, 2b+1, 2, 0, e)
  have hopen : (⟨(0 : ℕ), 2 * (b + 2), 0, 0, e + 1⟩ : Q) [fm]⊢* ⟨0, 2 * b + 1, 2, 0, e⟩ := by
    rw [show 2 * (b + 2) = (2 * b + 1) + 3 from by ring]
    exact opening (2 * b + 1) e
  -- spiral_tail_drain with B = 2b+1, C = 2, E = e
  have hfuel : 3 * e > 2 * b + 1 := by omega
  obtain ⟨D, hD2, hDe, hspiral⟩ := spiral_tail_drain (2 * b + 1) 2 e hfuel (by omega)
  refine ⟨D, hD2, by omega, ?_⟩
  apply stepStar_stepPlus_stepPlus hr4
  apply stepStar_stepPlus_stepPlus hopen
  convert hspiral using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 3⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e + 1⟩ ∧ d ≥ 2 ∧ e ≥ d)
  · intro q ⟨d, e, hq, hd, he⟩
    subst hq
    obtain ⟨D, hD2, hDe, htrans⟩ := main_trans d e hd he
    exact ⟨⟨0, 0, 0, D, e + 2 * d + 1⟩,
      ⟨D, e + 2 * d, rfl, hD2, by omega⟩, htrans⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1240

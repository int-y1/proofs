import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #805: [35/6, 605/2, 8/77, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 3  0  0 -1 -1
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_805

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem c_to_b : ∀ k b, ⟨0, b, k, 0, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ c₀ e₀, ⟨k, 0, c₀, d, e₀⟩ [fm]⊢* ⟨0, 0, c₀ + k, d, e₀ + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c₀ e₀
  · exists 0
  · step fm
    apply stepStar_trans (ih (c₀ + 1) (e₀ + 2))
    ring_nf; finish

theorem r1_chain : ∀ k, ∀ a₀ b₀ c₀ d₀,
    ⟨a₀ + k, b₀ + k, c₀, d₀, e⟩ [fm]⊢* ⟨a₀, b₀, c₀ + k, d₀ + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a₀ b₀ c₀ d₀
  · exists 0
  · rw [show a₀ + (k + 1) = (a₀ + k) + 1 from by ring,
        show b₀ + (k + 1) = (b₀ + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a₀ b₀ (c₀ + 1) (d₀ + 1))
    ring_nf; finish

-- Round chain: k rounds of (R3 + R2x3) with e >= k constraint.
-- Each round: d -= 1, c += 3, e += 5. Only need e >= 1 for R3, and e grows.
theorem round_chain_v3 : ∀ k, ∀ c₀ E, E ≥ k →
    ⟨0, 0, c₀, k, E⟩ [fm]⊢* ⟨0, 0, c₀ + 3 * k, 0, E + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c₀ E hE
  · exists 0
  · obtain ⟨E', rfl⟩ : ∃ E', E = E' + (k + 1) := ⟨E - (k + 1), by omega⟩
    rw [show E' + (k + 1) = (E' + k) + 1 from by ring]
    step fm
    apply stepStar_trans (r2_drain 3 c₀ (E' + k))
    show ⟨0, 0, c₀ + 3, k, E' + k + 2 * 3⟩ [fm]⊢* _
    rw [show E' + k + 2 * 3 = E' + k + 6 from by ring]
    apply stepStar_trans (ih (c₀ + 3) (E' + k + 6) (by omega))
    rw [show c₀ + 3 + 3 * k = c₀ + 3 * (k + 1) from by ring,
        show E' + k + 6 + 5 * k = E' + (k + 1) + 5 * (k + 1) from by ring]
    finish

-- Mixed phase by strong induction on B. For B <= 2: drain a, then round_chain_v3.
-- For B+3: R1x3, R3, then recurse. Constraint: F + 2 >= B + d.

theorem mixed : ∀ B, ∀ c d F, F + 2 ≥ B + d →
    ⟨3, B, c, d, F⟩ [fm]⊢* ⟨0, 0, c + 3 * (B + d + 1), 0, F + 3 * B + 5 * d + 6⟩ := by
  intro B
  induction B using Nat.strongRecOn with
  | _ B ih => ?_
  intro c d F hF
  rcases B with _ | _ | _ | B
  · -- B = 0: R2 x 3 then round_chain_v3 d
    apply stepStar_trans (r2_drain 3 c F)
    show ⟨0, 0, c + 3, d, F + 2 * 3⟩ [fm]⊢* _
    rw [show F + 2 * 3 = F + 6 from by ring]
    apply stepStar_trans (round_chain_v3 d (c + 3) (F + 6) (by omega))
    ring_nf; finish
  · -- B = 1: R1, R2 x 2, then round_chain_v3 (d+1)
    step fm -- R1
    apply stepStar_trans (r2_drain 2 (c + 1) F)
    show ⟨0, 0, c + 1 + 2, d + 1, F + 2 * 2⟩ [fm]⊢* _
    rw [show c + 1 + 2 = c + 3 from by ring,
        show F + 2 * 2 = F + 4 from by ring]
    apply stepStar_trans (round_chain_v3 (d + 1) (c + 3) (F + 4) (by omega))
    ring_nf; finish
  · -- B = 2: R1 x 2, R2, then round_chain_v3 (d+2)
    step fm; step fm
    apply stepStar_trans (r2_drain 1 (c + 2) F)
    show ⟨0, 0, c + 2 + 1, d + 2, F + 2 * 1⟩ [fm]⊢* _
    rw [show c + 2 + 1 = c + 3 from by ring,
        show F + 2 * 1 = F + 2 from by ring]
    apply stepStar_trans (round_chain_v3 (d + 2) (c + 3) (F + 2) (by omega))
    ring_nf; finish
  · -- B + 3: R1 x 3, R3, then recurse with B
    show ⟨3, B + 3, c, d, F⟩ [fm]⊢* ⟨0, 0, c + 3 * (B + 3 + d + 1), 0, F + 3 * (B + 3) + 5 * d + 6⟩
    have hF1 : F ≥ 1 := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [show (3 : ℕ) = 0 + 3 from by ring]
    apply stepStar_trans (r1_chain 3 0 B c d)
    -- At (0, B, c + 3, d + 3, F'+1)
    show ⟨0, B, c + 3, d + 3, F' + 1⟩ [fm]⊢* _
    rw [show d + 3 = (d + 2) + 1 from by ring]
    step fm -- R3: (3, B, c+3, d+2, F')
    apply stepStar_trans (ih B (by omega) (c + 3) (d + 2) F' (by omega))
    show ⟨0, 0, c + 3 + 3 * (B + (d + 2) + 1), 0,
      F' + 3 * B + 5 * (d + 2) + 6⟩ [fm]⊢* _
    rw [show c + 3 + 3 * (B + (d + 2) + 1) = c + 3 * (B + 3 + d + 1) from by ring,
        show F' + 3 * B + 5 * (d + 2) + 6 = F' + 1 + 3 * (B + 3) + 5 * d + 6 from by ring]
    finish

theorem main_trans :
    ⟨0, 0, c + 1, 0, c + f + 2⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 6, 0, 4 * c + f + 9⟩ := by
  apply stepStar_stepPlus_stepPlus (c_to_b (c + 1) 0 (e := c + f + 2))
  show ⟨0, 0 + (c + 1), 0, 0, c + f + 2⟩ [fm]⊢⁺ _
  rw [show 0 + (c + 1) = c + 1 from by ring,
      show c + f + 2 = (c + f + 1) + 1 from by ring]
  step fm -- R5
  rw [show c + f + 1 = (c + f) + 1 from by ring]
  step fm -- R3
  apply stepStar_trans (mixed (c + 1) 0 0 (c + f) (by omega))
  show ⟨0, 0, 0 + 3 * (c + 1 + 0 + 1), 0, c + f + 3 * (c + 1) + 5 * 0 + 6⟩ [fm]⊢* _
  rw [show 0 + 3 * (c + 1 + 0 + 1) = 3 * c + 6 from by ring,
      show c + f + 3 * (c + 1) + 5 * 0 + 6 = 4 * c + f + 9 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, f⟩ ↦ ⟨0, 0, c + 1, 0, c + f + 2⟩) ⟨0, 0⟩
  intro ⟨c, f⟩
  refine ⟨⟨3 * c + 5, c + f + 2⟩, ?_⟩
  show ⟨0, 0, c + 1, 0, c + f + 2⟩ [fm]⊢⁺ ⟨0, 0, (3 * c + 5) + 1, 0, (3 * c + 5) + (c + f + 2) + 2⟩
  rw [show (3 * c + 5) + 1 = 3 * c + 6 from by ring,
      show (3 * c + 5) + (c + f + 2) + 2 = 4 * c + f + 9 from by ring]
  exact main_trans

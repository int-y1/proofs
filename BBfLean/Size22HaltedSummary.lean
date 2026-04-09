import BBfLean.Size22Halted.Sz22_halted_692_1 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_2 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_3 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_4 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_5 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_6 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_7 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_8 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_9 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_10 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_11 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_12 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_13 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_14 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_15 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_16 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_17 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_18 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_19 -- author: Claude Opus 4.6
import BBfLean.Size22Halted.Sz22_halted_692_20 -- author: Claude Opus 4.6

/-!
# Size 22 halted summary

Summary of all proofs in `Size22Halted`.
This file provides extra confidence that the halted FMs are properly stated, and the number of steps
is correct.
-/

theorem haltsIn1 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 114613926700260640237968442298168949531348819453104518623702295 := Sz22_halted_692_1.fm_haltsIn

theorem haltsIn2 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 114613926700260640237968442298168949531348819453104518623702295 := Sz22_halted_692_2.fm_haltsIn

theorem haltsIn3 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 114613926700260640237968442298168949531348819453104518623702294 := Sz22_halted_692_3.fm_haltsIn

theorem haltsIn4 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+2, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 114613926700260640237968442298168949531348819453104518623702294 := Sz22_halted_692_4.fm_haltsIn

theorem haltsIn5 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 114613926700260640237968442298168949531348819453104518623702293 := Sz22_halted_692_5.fm_haltsIn

theorem haltsIn6 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 114613926700260640237968442298168949531348819453104518623702293 := Sz22_halted_692_6.fm_haltsIn

theorem haltsIn7 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+3, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 7548863488598188537 := Sz22_halted_692_7.fm_haltsIn

theorem haltsIn8 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 505335817223 := Sz22_halted_692_8.fm_haltsIn

theorem haltsIn9 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 213713825473 := Sz22_halted_692_9.fm_haltsIn

theorem haltsIn10 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 213713825473 := Sz22_halted_692_10.fm_haltsIn

theorem haltsIn11 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 213713825473 := Sz22_halted_692_11.fm_haltsIn

theorem haltsIn12 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 113517251374 := Sz22_halted_692_12.fm_haltsIn

theorem haltsIn13 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 83495859887 := Sz22_halted_692_13.fm_haltsIn

theorem haltsIn14 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 83495859887 := Sz22_halted_692_14.fm_haltsIn

theorem haltsIn15 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 83495859886 := Sz22_halted_692_15.fm_haltsIn

theorem haltsIn16 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 83495859886 := Sz22_halted_692_16.fm_haltsIn

theorem haltsIn17 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 8742409840 := Sz22_halted_692_17.fm_haltsIn

theorem haltsIn18 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b+1, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 8742409840 := Sz22_halted_692_18.fm_haltsIn

theorem haltsIn19 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 1463418236 := Sz22_halted_692_19.fm_haltsIn

theorem haltsIn20 : haltsIn (Q := ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | _ => none) ⟨1, 0, 0, 0⟩ 1463418236 := Sz22_halted_692_20.fm_haltsIn

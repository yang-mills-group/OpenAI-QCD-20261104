import YM.Vest.Ore
import YM.Rebus.Bread
/-! Semantics ALL comparison log at common terminal. `parties` V polynomial convolution exact. choose even-P oct.Or. -/
set_option autoImplicit false
noncomputable section
namespace YM.Vest
open Function
open scoped BigOperators ContDiff Classical
open QCD QCD.Creek QCD.Bera QCD.Anomaly QCD.Grass QCD.Cove Finset Next.Rank Next.Rank.Normal
open MassiveQCD.Play MassiveQCD.Play.Chamber MassiveQCD.FlareV
variable {A B C D U V X Y Z I:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype U][Fintype V][Fintype X][Fintype Y][Fintype Z][Fintype I]
variable {n m l:ℕ}{s t y e:ℝ}
namespace Tuck
local notation "V₀"=> Papers A (Patio X)
local notation "V₁"=> Papers B (Patio Y)
variable (T:Tone A X B Y)(S:Tone B Y C Z)
variable (f: Finset I→ Papers A (Patio X))(w:I→ℝ)(Z':Finset I)
private lemma stipendV {Z: Finset I}{D:Finset (Finset I)}(hd:D∈ registry Z): (∏ i∈D, give w i)= give w Z:=by
   obtain ⟨_,_,he,hg⟩:=mem_filter.mp hd; rw [← he]; unfold give; rw [Finset.prod_biUnion hg]; rfl
section Tilt
variable {K: Type} [CommRing K] [Algebra ℂ K] (φ:Finset I→ K)
lemma richens (Z:Finset I): parties (fun i=>give w i • φ i) Z = give w Z • parties φ Z:=by
     unfold parties; rw [Finset.smul_sum]; refine sum_congr rfl fun j hj=> ?_; rw [Finset.prod_smul,stipendV w hj] -- name
end Tilt
-- comparison.Weave.K monpol use log unweighed. grade ledger all subsets not just supported. at constant.Parties satisfy scaled log
lemma noticed (i:Finset I) : parties (switch f T.P T.Q T.M T.V) i=T.read (parties f i):= by
   apply carries (fun i=> T.read (parties f i)); rw [hollow,T.noneW]
def tilt (T:Tone A X B Y)(w:I→ℝ) (f:Finset I→Papers A (Patio X)) (Z:Finset I):= give w Z • switch f T.P T.Q T.M T.V Z
lemma tilted : parties (tilt T w f) Z'=give w Z' • T.read (parties f Z'):=by unfold tilt; rw [richens,noticed]
lemma born : tilt T w f ∅=0:=by unfold tilt switch; rw [cet]; simp
variable (z:I→ℝ)
lemma plus : tilt S z (tilt T w f) = tilt (T.after S) (w*z) f:=by
    let q:= tilt S z (tilt T w f); let k:= tilt (T.after S) (w*z) f; let g x:= parties k x
    funext i; change q i=k i; have hp:k i=cetacea g i:=only g k i (fun _ _=>rfl) (born ..) _ (Subset.refl i); rw [hp]
    refine only g q i (fun s hs=>?_) (born ..) _ (Subset.refl i); unfold q g k; rw [tilted,tilted,tilted,T.spoke]; rw [map_smul,smul_smul]; congr 1; unfold give; simp [Finset.prod_mul_distrib,mul_comm]
end Tuck
end YM.Vest

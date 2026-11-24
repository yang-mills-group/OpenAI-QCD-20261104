import YM.Alum.Citrus
import YM.Sprig.Eyre
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Ibis
open QCD.Lat QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
open YM.Bank.Jule YM.Bank.Kith YM.Bloom.Jar
open MintV Suburb.Melt Suburb.Melt.Lobby
-- any coords, use Root footprints/all powers. existence across Type-B/A layout on pure.Inputs only Euclidean inequalities. schedule.Authentic seam copies respect Θ. 
variable {S:Scheme}{D i ℓ j₀ m K N p w Uq:ℕ}{L:Side}{Hp:Dial D}{R:Side}{z e v:ℝ}
variable (H:Tier S L Hp z i ℓ j₀ p w)(A:Room L Hp w Uq m K e v z) (hp:Even R.val)
-- μ or compact.A.Face parallel bounds from layout margins only. 
local notation "ω"=>measureV L
local notation "Θ"=>sharpM S L Hp z i
local notation "V" m:arg=> S.side R m
local notation "T" n:arg=> screen S n Θ
variable {I:Type}[Fintype I](y: I→ Cover)

local notation "λN"=> ratioTo S N ℓ
open Tarot Tarot.Vista
include A H hp
-- flattens arbitrary placements heterogenous array.
variable (K':ℕ)
open Pilgrim Column
omit A
lemma flanks {X:ℝ}(B:Promises L Hp w Uq m K K' e v X z)(hℓ:ℓ ≤ N)(hv:screen S N (sharpM S L Hp z i) ∘ y∈ Ibis.flats I (2*e) (v/2))(hn:2*(v*measureV L Hp.e z)<((S.side R ℓ).val:ℝ))(hI:Fintype.card I≤K)(ht:0<v): ∃ (a:Site (S.side R ℓ))(P:I→Site (S.side R p)), Injective P∧∀ i,wrap _ (y i)∈ (Column.sky S R p N (H.ascend.le.trans hℓ) (evenW S R hp p) a).margin (P i) (Tarot.Vista.softerT S ℓ p N Uq m):=by
     choose x d hX he using fun j:I=> Goblet.near_c (y j) (ratioTo S N ℓ) (odd_to hℓ)
     let F:=(T N) ∘ y; let G:=(T ℓ) ∘ x
     have hx: G∈flats I e v:=by
           have hv' : ‖G-F‖ ≤ lapT L Hp z:=by
                 have hZ:0 ≤ (measureV L Hp.e z)⁻¹:= inv_nonneg.mpr ((χone ..).le)
                 refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num:(0:ℝ)≤200) hZ)).mpr fun i=>?_ ; rw [Pi.sub_apply,norm_sub_rev]; exact (shiftW H (x i) (y i) _ hℓ (hX i) (he i)).trans (mul_le_mul_of_nonneg_right (by norm_num:(4:ℝ)≤200) hZ)
           obtain ⟨h',h''⟩:= le_min_iff.mp B.dust; exact puff _ _ F hv G _ _ _ hv' (by linarith only[h'']) (by linarith only[h',ht])
     obtain ⟨a,P,h,h₁,h₂⟩:= slant H B.hue hp x (fun i=> (perim e v G hx ht.le i).trans (le_of_lt (half_lt_self ht))) (iris e v G hx ht.le) hn (H.lower.trans H.ascend.le) H.ascend.le hI
     let hw:= H.ascend.le; let T':= Column.sky S R p N (H.ascend.le.trans hℓ) (evenW S R hp p) a
     refine ⟨a,P,h,fun j=>?_⟩; let E:= ratioTo S N ℓ; let Y:=unveil L Hp z; let x' := E • x j; let f:=y j-x'; let t:= marginM S Uq p ℓ; let w:= t+110+m+4*Y; let k:= Tarot.Vista.softerT S ℓ p N Uq m
     have h1:2*E+1+k≤ E*w:=by
          have hv:0<E:= (odd_to hℓ).pos; unfold w k softerT; change 2*E+1+E*(t+104+m)≤ E*(t+110+m+4*Y); nlinarith only[hv,Nat.zero_le (E*(4*Y))]
     rw [show y j= x'+f from (by unfold f; abel)]
     have ht'(i:Axis) : (f i).natAbs< 2*E+1:=by
           have hh:=he j i; change y j i =x' i + _ at hh; have h:(d j i)≤ E:= hX j i; unfold f; rw[Pi.sub_apply]; omega
     exact Goblet.shifted T' _ (padding _ _ _ _ _ (viewOdd S R (hw.trans hℓ)) (bitter hw hℓ hp a (P j) _ (x j) (h₂ j)) h1) ht'
end Ibis
end YM.Intag
#print axioms YM.Intag.Ibis.flanks

import YM.Alum.Lamp
import YM.Alum.Ibis
import YM.Alum.Cords
import YM.Alum.Lit
import YM.Alum.Hoist
/-! Reading scales & geometry at vintage. Universal euclidean coordinates native stencil lifts presented at physical `resolution` r, independent of regulator beyond i. -/
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
local notation "t"=> unveil L Hp z
variable {I:Type}[Fintype I](x: I→ Cover)
-- relative positions including coords.Any hV.Requires individual ≤ v maybe h=b.L continuum patch define small v.A.
include H hp A
variable (hx:∀ j, ‖screen S ℓ (sharpM S L Hp z i) (x j)‖ ≤ v)(hX:∀ j k,j≠k→ screen S ℓ (sharpM S L Hp z i) (x j)-screen S ℓ (sharpM S L Hp z i) (x k)∈ Oasis e v)
variable (hn:2*(v*measureV L Hp.e z) < ((S.side R ℓ).val:ℝ))
open Tarot Tarot.Vista
local notation "Rz" n hv z=> mural (viewW S R hv) (evenW S R hp n) z
include hx hX hn
set_option quotPrecheck false
lemma slant (hk:j₀ ≤ ℓ)(hh:p ≤ ℓ)(hI:Fintype.card I ≤ K):∃ (a:Site (S.side R ℓ)) (P:I→Site (S.side R p)), Injective P ∧(∀ j, wrap _ (x j)∈(mural (viewW S R hk) (evenW S R hp j₀) a).margin (0:Site (S.side R j₀)) (marginM S Uq j₀ ℓ+102+ratioTo S ℓ p)) ∧ ∀ j,wrap _ (x j)∈ (mural (viewW S R hh) (evenW S R hp p) a).margin (P j) (marginM S Uq p ℓ+110+m+4*unveil L Hp z):=by
      let G:= viewW S R hk; let P:= viewW S R hh; let y:=wrap (S.side R ℓ) ∘ x; obtain ⟨hY,hR⟩:= A.bars (ratioTo S ℓ p) (ratioTo S ℓ j₀) H.repB H.rep; have hM:=A.marks _ H.repB; let η:=ω Hp.e z; let C (z:Cover):=posT η 1 z; have hN:2*(v*η^1)<((S.side R ℓ).val:ℝ):=by rw[pow_one]; exact hn
      let v0:=marginM S Uq j₀ ℓ+102+P.count.val; let X:= pitchC L Hp v z; let B:=marginM S Uq p ℓ+110+m+4*unveil L Hp z; have hz:C 0=0:=by unfold C posT; rw [show rock 0=0 from PiLp.ext fun _=>by simp[rock],smul_zero]
      have he₀(j:I): separation (y j) (wrap (S.side R ℓ) 0) ≤ X:=by
           have hx:=hx j; rw [H.scaleL] at hx; have h:C (x j)-C 0 ∈ Oasis 0 v:=by
                  rw [hz,sub_zero]; apply YM.Bloom.Jar.disc _ hx; positivity
           have hu:= Consent.rootV (x j) 0 η 1 (χone ..) 0 v h hN
           rw [pow_one] at hu; exact_mod_cast hu.2.trans (Nat.le_ceil (v*η))
      have hE(i j)(hi:i≠j):ratioTo S ℓ p < separation (y i) (y j):=by
           specialize hX i j hi; rw [H.scaleL,H.scaleL] at hX; have hu:= Consent.rootV (x i) (x j) η 1 (χone ..) e v hX hN; rw [pow_one] at hu; exact_mod_cast (lt_of_mul_lt_mul_left (hM.trans_le hu.1) (by norm_num:(0:ℝ) ≤ 2))
      obtain ⟨a,U,hD,he⟩:= wells G P (evenW S R hp _) (evenW S R hp _) (viewOdd ..) (viewOdd ..) y (wrap (S.side R ℓ) 0) X B v0 he₀ hY (by unfold B; omega) (lt_of_le_of_lt (Nat.mul_le_mul_right (2*B) (Nat.add_le_add_right hI 1)) hR) hE; exact ⟨a,U,hD,fun i=>(he i).1,fun i=>(he i).2⟩ -- h deps smoke.
omit hx hX hn hp A
open CardsT
lemma steeperP(n:ℕ)(x':Fin n→ Cover)(u:Fin n→ ↥(Lattice.box (CardsT.flex S ℓ i)))(j:Fin n): ‖optionR S i ℓ n L Hp z x' u j-(screen S ℓ (sharpM S L Hp z i) (x' j))‖ ≤ 200 * (measureV L Hp.e z)⁻¹:=by
      rw [H.aims]; unfold optionR displayR offsetA; rw [Function.comp_apply, YM.Bloom.Jar.spread,add_sub_cancel_left]; let f:= (u j).val; let X:= ω Hp.ν z; let R:= Rf L Hp z
      have h:= Consent.solo X (2*Hp.H) (χone ..) f _ (u j).property -- arg
      have hF: CardsT.flex S ℓ i ≤100 * ratioTo S i ℓ:=Nat.mul_le_mul_left _ (Nat.sub_le ..)
      apply h.trans; have hf:= Tier.realG L Hp z; have hx: X^(2*Hp.H)=R:=by unfold R Rf X WTop; rw[Nat.mul_comm 2,pow_mul]
      have hh:= le_of_lt (χone L z Hp.e); rw [hx,div_le_iff₀ hf]; refine le_trans (mul_le_mul_of_nonneg_left (show ((CardsT.flex S ℓ i):ℝ) ≤ 100*(ratioTo S i ℓ:ℝ) from by exact_mod_cast hF) (by norm_num:(0:ℝ) ≤ 2)) (le_of_eq ?_); rw [H.counts, div_eq_mul_inv]; ring
omit H
end Ibis
end YM.Intag
#print axioms YM.Intag.Ibis.slant
#print axioms YM.Intag.Ibis.steeperP

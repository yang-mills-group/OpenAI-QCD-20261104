import YM.Oars.Turnout
import YM.Oars.Canyon
import YM.Oars.FicusL
/-! # Revenue bundle.Sizes output from each k to all compatibles by Fleet.X.Ed -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {c f:Side}{η M t t' μ θ :ℝ}{I E J :Type}[Fintype I]
variable (q:I→Bool)(X:Reel c 6 I E)(Taper:Massive.SourceRead.TaperHol) {U: YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U)(i:I)(k:Cover)(P:BudgetPoint){d n Dx nL r:ℕ}
local notation "Sp"=>LoomT.Single X i
local notation "K"=> Keys c 6
set_option quotPrecheck false
local notation "o"=>wrap c k
variable (p:Label d)
-- reputation.E.L uses Film too
variable (x:I→Site c)(he:X.Book x q)
namespace Gel
open Counting
variable [Fintype J](s:I→J→Prop)(q':J→Bool)(g:I→J→ℝ)(p0:Set (Finset J))(D:Set (Finset I))(hq:Pledge q q' s p0 D)(hp:∀ j:J,{j}∈ p0)
local notation "Γ" j=>To s j
local notation "E!"=> Fellows X s p0
local notation "F!"=> swirl (P:=p0) q q' g s X
local notation "Vp" j=> translateK q q' g s hq X j hp
variable (V:J→ℝ)
include hp hq he
-- economic. e errors lengths. at same scale.
set_option maxHeartbeats 420000 in
lemma accounts (j:J)(W:To s j→ℝ)(v:To s j→ℝ)(P':To s j→ Label d)
   (h:∀ i: To s j,Gel q X Taper i.val k P (P' i) t t' (W i) (v i) Dx nL r):
   Gel q' F! Taper j k P (∑ i: Γ j,(↑(g i.val j):ℂ) • P' i) t t' (∑ i:To s j, |g i.val j| * W i) (∑ i:To s j, |g i.val j| * v i) Dx nL r:=by
      choose S p hs ht' hz hS hZ Xa₁ f' hM hQ using fun i: To s j=> (h i).support
      choose f hF hG using Xa₁
      let v0 := Single X; let G' := Γ j; let D':= Sigma (fun i:G'=> v0 i.val); let e:=Vp j; let Y':= F!; let S'(u:D'):=S u.1 u.2; let α(i:G') := |g i.val j|; let ρ (i:G') :ℂ:=g i.val j; let z(i:D'):= ρ i.fst • p i.1 i.2; have h₁(u:G')(i:LoomT.Single X u.val): Reel.speaker q' Y' (e ⟨u,i⟩).val = ρ u • Reel.speaker q X i.val:= postage q q' g s hq x X he j hp u i -- binder order
      have hh(u:D'): Reel.speaker q' Y' (e u).val= ρ u.1 • Reel.speaker q X u.2.val:=h₁ u.fst u.2
      have hU(u:D'): (Y'.addr (e u).val) = X.addr u.2.val:=locPrint q q' g s hq X j hp ..
      have ha (i:G'):‖ρ i‖ = α i:= Complex.norm_real _
      have hTv: HasSum z (∑ i: G', ρ i • P' i):=by
          have h(i:G'): HasSum (fun j:Single X i.val=> z ⟨i,j⟩) (ρ i • P' i):=by
             rw [← hZ]; exact (hS i).hasSum.const_smul _

          have hm: Summable z:=by
              apply Summable.of_norm; apply (summable_sigma_of_nonneg ?_).mpr; exact ⟨fun i=> (h i).summable.norm,Summable.of_finite⟩; exact fun _=>norm_nonneg _
          have hh(i:G'): Summable fun j:Single X i.val=>z ⟨i,j⟩:=(h i).summable
          rw [← (show (∑' i:G',ρ i • P' i)=∑ i:G',ρ i • P' i from tsum_fintype _), show (∑' i:G',ρ i • P' i)=∑' i,z i from Eq.trans (tsum_congr (fun i=>(h i).tsum_eq.symm)) hm.tsum_sigma.symm]; exact hm.hasSum
      let B i:=α i*W i; let C i:=α i*v i; refine Sample.candied q' F! Taper j k P _ D' (∑ i,B i) (∑ i,C i) t' S' e z (fun i=>?_) hTv.summable hTv.tsum_eq (fun i=> α i.1*f i.1 i.2) (fun i=>α i.1*f' i.1 i.2) (fun i=>?_) (fun i=>?_) (fun i=>?_) (fun i=>ht' ..) (fun i=>?_) (fun i=>?_)
      · rw [hh]; exact Orientation.acting Taper k d _ _ (hz i.1 i.2) _
      · rw [hh,← ha]; exact Girdle.flare_by _ _ _ (hF ..) _
      · rw [hU,hh,←ha]; exact Terrain.scaledL (hM ..) _
      · rw [hU]; exact hs ..
      · apply Stags.sigmaBud _ B ?_
        · exact Push.AbsoluteSums.budget_finite (fun j=> mul_nonneg ((show 0≤ α j from abs_nonneg _)) (budget_nonneg (hG j i))) le_rfl
        intro i'; convert! budget_scale (show 0 ≤ α i' from abs_nonneg _) (hG i' i) using 1; funext j; dsimp only; split
        next h=> exact mul_assoc ..
        next h=> rw [mul_zero]
      · apply Stags.sigmaBud _ C ?_
        · exact Push.AbsoluteSums.budget_finite (fun j=> mul_nonneg ((show 0≤ α j from abs_nonneg _)) (budget_nonneg (hQ j i))) le_rfl
        intro i'; convert! budget_scale (show 0 ≤ α i' from abs_nonneg _) (hQ i' i) using 1; funext j; dsimp only; split
        next h=> exact mul_assoc ..
        next h=> rw [mul_zero]
-- test poses from these. mixed.J subsite predictor
omit he hq hp
lemma relents (H:Gel q X Taper i k P p η θ M t Dx nL r) {V' P':ℝ}(h:M ≤ V')(hp: t ≤ P') : Gel q X Taper i k P p η θ V' P' Dx nL r:=by
   obtain ⟨S,z,h₁,h₂,h₃,h₄,h₅,⟨g,h6,h7⟩,h8,h9,h10⟩:=H.support; exact ⟨S,z,h₁,h₂,h₃,h₄,h₅,⟨g,h6,fun i=>budget_loosen (h7 i) h⟩,h8,h9,fun i=>budget_loosen (h10 i) hp⟩ -- syntax nested
end Gel
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Gel.accounts

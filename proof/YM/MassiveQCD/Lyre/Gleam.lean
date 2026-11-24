import YM.MassiveQCD.Lyre.Elevator
import YM.MassiveQCD.Lyre.Harmony
/-! # Beam comparison of full-spin Tine a passenger. Chamber on occupancy of hull. Important allowed ranks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Lyre
open Function Lattice Wilson QCD QCD.Creek Grass Ledge Lat Kit Finset NormedSpace RG QCD.Cove QCD.Cove.Send Filter Run Jets
open QCD.Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open QCD.Jets.Sun QCD.Cove.Fj QCD.Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
open Spice QCD.Stew Stitch Ribbon
open Dust Brick Garden Sway OrbitG Revolve
open Plate Cupola Elevator
-- analytic left derivative, preserve supports even at discontinuities
variable {J Z:Type}
lemma stays_left {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](S:Submodule ℝ E)(V:Grid f→E)(h:∀ U,V U∈ S)(u:List (Directions su f)) :∀ g, RG.leftDerivs V u g∈S:=by
    induction u with
    | nil=> exact h
    | cons i l ih=>
       intro Z; let f(x:ℝ):=leftDerivs V l (increment Z (x • i)); by_cases he:DifferentiableAt ℝ f 0; swap; · change deriv f 0∈ S; rw [deriv_zero_of_not_differentiableAt he]; exact S.zero_mem
       change deriv f 0 ∈ S; have hh:= hasDerivAt_iff_tendsto_slope.1 he.hasDerivAt
       apply IsClosed.mem_of_tendsto (Submodule.closed_of_finiteDimensional S) hh; exact Eventually.of_forall fun i=>show slope f 0 i∈ S from S.smul_mem _ (S.sub_mem (ih _) (ih _))
variable {T:Grid f→Sheet f} (P:Sun G c f h δ v q u a l T)
-- rewrite Berry lemma.R. fingerprint. no B positions expense in final principal BILL occupation.
variable {E J:Type} [Countable E][Countable J]
variable (H:Rise f F E J)(I:BudgetPoint) (s:Finset (Fj (Tr f) E J))(i:E)
set_option quotPrecheck false
local notation "D₀"=> P.equip F b
local notation "A'"=> H.row i
local notation "o'"=> (H.row i).site
local notation "M"=> coreW D₀ H s
variable {τ p Λ:ℝ}
variable (hp: Peak (P.equip F b) I.threshold x y ξ (fun i=> Real.exp 1*terra P F b x y i))(hh:leftE s={i})(HK:Grid f→Fields f F)(hv:Sight (H.row i).support (H.row i).site 2 I x HK τ)
variable (Q:Fields c F→L[ℝ]ℝ)(hw:rootBill ((sliceL G h).parent (H.row i).site) y Q)
variable (W:Grid f)(hW:Healthy I.threshold (brimW (P.equip F b) H s) W)
variable (z:ℕ)(hz:∀ i' ∈(halo b (coreW (P.equip F b) H s)).image (sliceL G h).parent,separation i' ((sliceL G h).parent (H.row i).site) ≤ z)
open PhysicalNext.JointLoad MultiNext.SignedSource
include hv hh
lemma ruke (Y:Fields f F →L[ℝ]ℝ)(hy: ∀ z, z∈ region (limits (H.row i).support)→ ‖Y z‖ ≤ Λ*plank (H.row i).site x z)(hT:0≤Λ)(hK:0<x): let Z:=brimW (P.equip F b) H s; let r:= Y ∘ HK; LocalOn Z r ∧ Ease.Charm I Z r ∧ I.supBounds (H.row i).site Z r (Λ*τ) ∧ Measurable r :=by
    intro X q; have hX:(H.row i).support⊆ X:=Subset.trans (leafSub P H s i hh) (native_sub D₀ H _)
    have ht:= occupies hv hX le_rfl; have hm:= (show Ease.Charm I X HK from ⟨ht.room,ht.use⟩).scales Y; refine ⟨hm.sites,hm,⟨mul_nonneg hT hv.travels,?_⟩,Y.continuous.measurable.comp hv.borel⟩
    intro V h l hl hL; rw [Push.Local.left_linear Y _ (ht.use _ h) hl]; let S:=((region (limits (F:=F) (H.row i).support)).toSubmodule).restrictScalars ℝ
    have hz: RG.leftDerivs HK l V ∈ S:= (stays_left S HK hv.gate l _) -- restrict simplification
    have he:= ht.pole V h l hl hL; rw [Plate.viewSen _ _ _ hK.le] at he; exact (hy _ hz).trans (mul_le_mul_of_nonneg_left he hT)
local notation "pix"=> Q.comp ((Stitch.Tablet.tunnel D₀ s W).restrictScalars ℝ)
include hp hW hw
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 420000 in
lemma bore (hv':0 ≤ u) (ht:y*fingers F*q ≤ ξ*x) (hc:∀ i,terra P F b x y i≤1) (U:Grid f) (hU:Healthy I.threshold (brimW (P.equip F b) H s) U) (hh':beamAt (brimW D₀ H s) U W w)(hA:0 ≤ w)(hκ:w<δ/2)(hZ:∀ i' ∈(halo b (coreW (P.equip F b) H s)).image (sliceL G h).parent,separation i' ((sliceL G h).parent (H.row i).site) ≤ z):
    let K:=pix ∘HK; let X':=Stitch.Tablet.tunnel D₀ s; let m:=∏ i∈ops s,(Real.exp 1*terra P F b x y i); let j:= w/(δ/2); let Z':=((1+(z:ℝ))^2)
    Ease.Charm I (brimW D₀ H s) K ∧ I.supBounds (H.row i).site (brimW D₀ H s) K ((Z'*m)*τ) ∧ Measurable K ∧
    ‖Q (X' U (HK U))-K U‖ ≤ Z'*((m*τ) *( (((hooks (F:=F) (sliceL G h) M).card:ℝ)*(ξ*j)+(ops s).card*j))) :=by
    intro K X m j Z'
    have hm:0≤ m:=prod_nonneg fun i _=> (hp.spare i U).nn; let z₁:= (halo b M).image (sliceL G h).parent; let H₁:= (sliceL G h).parent o'; let Y:=pix
    have hh' z (hz:z∈region (limits (H.row i).support)): (z:Fields f F)∈region (limits (coreW D₀ H s)):= regionMon (limitsMon _ _ (leafSub _ _ _ _ hh)) hz
    have hk (z:Fields f F)(he:z∈region (limits (H.row i).support))(r:Grid f): X r z∈region (limits z₁):= tunnel_gate D₀ H s r _ (hh' z he)
    have hp' i' (h:i'∈region (limits (H.row i).support)): ‖Y i'‖ ≤ Z'*m*plank o' x i':=by
       apply (hw _).trans ((shutter z₁ H₁ z hZ (X _ _) hp.cup (hk _ h W)).trans ?_); apply (mul_le_mul_of_nonneg_left ((tunnel_cap D₀ H s W hp hW _ (hh' _ h)).trans (mul_le_mul_of_nonneg_left (Stew.shot (Stew.lens o') i' _ hp.bud) hm)) (sq_nonneg _)).trans_eq; change Z' * (m * plank o' x i')=Z'*m* plank o' x i'; ring
    obtain ⟨hQ,hK,hL,hX⟩:= ruke P H I s i hh HK hv _ hp' (mul_nonneg (sq_nonneg _) hm) hp.bud; refine ⟨hK,hL,hX,?_⟩; let i' := HK U
    have hτ: plank o' x i' ≤ τ:= (viewSen _ i' x hp.bud.le).ge.trans (hv.pole U (hU.mono_left ((leafSub P H _ i hh).trans (native_sub D₀ H _))) [] (by simp) (by simp)) -- `≥` reversed? view=plank. .ge=plank≤view. 
    let Y' W:= X W i'; change ‖Q (Y' U)- Q (Y' W)‖ ≤ _; rw [← map_sub]; have hE:0≤j:= div_nonneg hA (half_pos P.positive).le; have hξ:0≤ξ:= zero_le_one.trans hp.post
    let σ:=(((hooks (F:=F) (sliceL G h) (coreW D₀ H s)).card:ℝ)*(ξ*j)+(ops s).card*j)
    have hzB:load (fun _=>y) (Y' U- Y' W) ≤ σ*(m*τ):= (tunnel_bill D₀ H s U W hp hU hW (mul_nonneg (Nat.cast_nonneg (α:=ℝ) (ops s).card) hE) (mul_nonneg hξ hE) (sassy P _ _ _ b H hp (by assumption) hA hκ hc) (fun l hl'=> (swept P hp U W H s hU hW (by assumption) hA hκ hv' ht l hl').2.2) i' (hh' i' (hv.gate U))).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((Stew.shot (Stew.lens o') i' x hp.bud).trans hτ) hm) (by positivity))
    exact (hw _).trans ((shutter z₁ H₁ z hZ (Y' U-Y' W) hp.cup (Subalgebra.sub_mem _ (hk i' (hv.gate U) _) (hk i' (hv.gate U) _))).trans ((mul_le_mul_of_nonneg_left hzB (sq_nonneg _)).trans_eq (congr_arg (Z' * ·) (mul_comm ..))))
lemma grand (p':ℝ) (he: Sea G h b δ p' q I.threshold P.Z P.V 2) (hm:ops s=∅)(hh':4*((fingers F*p')*y)≤ x/4):
    I.supBounds (H.row i).site (brimW D₀ H s) (pix ∘ HK) τ :=by
     let T:= (D₀).shortP W
     have hq i (hi:i∈limits M): amount T i (sliceL G h) ≤ fingers F*p':= freezeQ P i W b 2 p' he (hW.mono_left (by rw [brim_eq]; exact Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr (mem_filter.mp hi).2)))
     let J:= pix; have hz v (h':v ∈ region (limits (H.row i).support)): ‖J v‖≤ 1*plank o' x v:=by
        apply (hw (Stitch.Tablet.tunnel D₀ s W v)).trans; rw [Stitch.Tablet.tunnel,show axle D₀ W s=1 by simp [Cove.axle,hm]]; change QCD.Stew.plank _ _ (wipe _ _ _ (near _ _ _)) ≤ _; rw [echo (sliceL G h),one_mul]; exact petals _ _ _ (regionMon (limitsMon _ _ (leafSub P H _ _ hh)) h') hq hp.cup hh' hp.bud
     simpa only [one_mul] using (ruke P H I s i hh HK hv _ hz zero_le_one hp.bud).2.2.1
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.bore

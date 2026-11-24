import YM.Clink.Furze
import YM.Clink.Roses
/-! Price sections. Basic ledgers plus experimental with l interference. Compression to arguments Aroma.K. -/
set_option autoImplicit false
set_option quotPrecheck false
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
variable {I J D E :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Basal.Surge
open QCD.Ruby Cove NormedSpace
open Massive.PCAC Massive.PCAC.Oren WindowU
variable {c f' L:Side}{v t x δ α β κ ρ C C' ξ M B3 G3 σ B1 G1 a D_:ℝ}{P:BudgetPoint}{k n l m N B:ℕ}
variable (o:I → Cover)(W S:St c)(p:Set (Finset I))(F:Flavor 6)(X:Axis)(W':St c)
local notation "R'"=> Flavor 6
local notation "u"=> wrap c ∘ o
local notation "b₂"=> (25/256:ℝ)
local notation "μ"=> (1/512:ℝ)
local notation "ε"=> (1/256:ℝ)
local notation "BK"=>mCash P.B P.power P.order k μ b₂ (M *ξ)*(Basal.anth ε (b₂+2*ε) P.B*(a*v^2))
local notation "BZ"=> (B:ℝ)*(ξ* cashZ v b₂)
local notation "vk"=> cleanA P k B M a ξ 1 v
variable (f g:R'→ℂ)
open Rails.Tantra
variable (ht:1 ≤ v)(hz:0 ≤ ξ)(hP:∀ i∈ p,i.card≤1)(h0:1 < P.B*P.B)(hp:Fintype.card I ≤ B)(hr: BudgetB P.order P.power M)(hQ:Fires (wrap c∘o) k)(hF:∀ i∈p,Spaced (wrap c∘o) i P.B)(hw: 0 ≤ a)(hY: ColorDuty W a v P)
include ht hz hP h0 hp hr hQ hF hw hY
lemma Éclore (hg:hullP P.B k*(Real.exp (b₂+μ)*(M *ξ*2^P.order))≤μ): Owns (solo F c X) o P W p b₂ v M ξ (vk) vk ∧ Owns (hark F c X) o P W p b₂ v M ξ vk vk ∧ Owns (pole F c) o P W p b₂ v M ξ vk vk:=by
        let T:= BK; let w0:= BZ; have hC:0≤ cashZ v b₂:=by unfold cashZ veinFare; positivity
        have hQ':0≤T:=by
           unfold T; apply mul_nonneg; · have hx:=hr.nng; unfold mCash mRent beamFee polyPrice hullP; dsimp only; positivity
           exact mul_nonneg (earnA ..) (mul_nonneg hw (sq_nonneg _))
        have hF': (Fintype.card I:ℝ)*(ξ*cashZ v b₂)≤ vk:= (mul_le_mul_of_nonneg_right (show (Fintype.card I:ℝ) ≤ B from by exact_mod_cast hp) (mul_nonneg hz hC)).trans (le_add_of_nonneg_left hQ')
        have hk:T≤ vk:=le_add_of_nonneg_right (show 0≤w0 from by unfold w0; positivity)
        refine ⟨swings _ _ _ _ (owns0 o W p (solo F c X) ht k hY hz hr.nng hQ h0 hF rfl (fun i=> (hr.b P le_rfl le_rfl c _ X F).1) hg) le_rfl hk hk,swings _ _ _ _ (δZ o W p F X hP ht hr.nng) le_rfl hF' hF', swings _ _ _ _ (owns0 o W p (Surge.pole F c) ht k hY hz hr.nng hQ h0 hF rfl (fun i=> (hr.b P le_rfl le_rfl c _ X F).2.1) hg) le_rfl hk hk⟩
local notation "U_'"=> M + 6*(M+M)
variable (T:ℝ)(h:∀ i:I,WindowU.Given (wrap c (o i)) P v (25/256) (T*v^2*P.threshold) (T*v^2) (Entr.Meridian.aurasigmaMont F ((wrap c ∘ o) i) X S+Entr.Meridian.sourceT F ((wrap c ∘ o) i) X W'))(he:0 ≤ T)(hk:W = S+W')
local notation "Bh"=> pl P k B M a T ξ t v
local notation "PV"=> pu P k B M a T ξ t v
include h hk he
lemma sprats (hv:hullP P.B k*(Real.exp (b₂+μ)*(U_' *ξ*2^P.order))≤μ)(hS:‖f‖≤t)(hg:‖g‖≤t)(hx:t ≤1): Owns (SunAt X S f g F univ.toList) o P W p b₂ v U_' ξ Bh PV∧ Owns (tilde F S X) o P W p b₂ v U_' ξ Bh PV:=by
         have h₁:0≤t:= (norm_nonneg _).trans hS; have hz0:=hr.nng; have hM:M*t≤M+6*(M+M):=(mul_le_of_le_one_right hz0 hx).trans (le_add_of_nonneg_right (by positivity)); have hB: hullP P.B k*(Real.exp (b₂+μ)*(M *(t*ξ)*2^P.order))≤μ:=by
               apply le_trans _ hv; rw [←mul_assoc M]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hz) (by positivity)) (Real.exp_pos _).le) (by unfold hullP; positivity)
         let b1:= pl P k (Fintype.card I) M a T ξ t v; let b2:= pu P k (Fintype.card I) M a T ξ t v
         let Uh := cleanA P k B M a (t*ξ) t v; let H := (Fintype.card I:ℝ)*(ξ*(T*v^2*P.threshold)); let E':=(Fintype.card I:ℝ)*(ξ*(T*v^2)); have hv0 :M ≤ U_':=le_add_of_nonneg_right (by positivity)
         have ht0:= fame o W S p F X W' f g ht hz hP h0 hY hk T hr h he t (univ.toList) hQ hF h₁ hx hS hg hB
         have hi:Owns (SunAt X S f g F univ.toList) o P W p b₂ v U_' ξ b1 b2:=by unfold b1 b2 pl pu cleanA hkappa loomR; simpa only [Finset.length_toList,card_univ, show Fintype.card (Flavor 6)=6 from by simp[Flavor], Nat.cast_ofNat] using ht0
         have ht1: 0≤Uh:=by
               unfold Uh cleanA hkappa; have hr:0≤ loomR P k M (t*ξ):=by unfold loomR mCash mRent beamFee polyPrice hullP; dsimp only; positivity
               have hp:0≤ cashZ v b₂:=by unfold cashZ veinFare; positivity
               apply add_nonneg; exact mul_nonneg hr (mul_nonneg (earnA ..) (by positivity)); positivity
         let κ:=(Fintype.card I:ℝ); have hrL: κ ≤ (B:ℝ):=by unfold κ; exact_mod_cast hp
         have hz' : cleanA P k (Fintype.card I) M a (t*ξ) t v ≤ Uh:=by
               unfold Uh cleanA; apply add_le_add; exact le_rfl; gcongr; · unfold cashZ veinFare; positivity
         have hF:H ≤ B*(ξ*(T*v^2*P.threshold)):= mul_le_mul_of_nonneg_right hrL (by positivity[P.threshold_pos])
         have hV:E'≤ B*(ξ*(T*v^2)):=mul_le_mul_of_nonneg_right hrL (by positivity)
         refine ⟨swings _ _ _ _ hi le_rfl (add_le_add hF (mul_le_mul_of_nonneg_left hz' (by norm_num : (0:ℝ) ≤6))) (add_le_add hV (mul_le_mul_of_nonneg_left hz' (by norm_num:(0:ℝ) ≤ 6))), swings _ _ _ _ (κp o W S p F X W' hP ht (fun i=> (hr.b P le_rfl le_rfl c _ X F).2.2) hk h he) hv0 (hF.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num: (0:ℝ) ≤ 6) ht1))) (hV.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num:(0:ℝ)≤6) ht1)))⟩
end Basal.Surge
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.Surge.Éclore
#print axioms YM.MassiveQCD.Sample.Basal.Surge.sprats

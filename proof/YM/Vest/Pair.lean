import YM.Vest.Flail
import YM.Vest.Corn
import YM.Rebus.Shocks
import YM.Vest.Inca
import YM.Vest.Loom
import YM.Hypnos.Tenuous
/-! # Paid one-step primary. COREVS.reducing to payouts
 Geometry over thermal counting stencils includes deterministic Wick-support. Propagating grade.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.TimesV
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
open Rebus Matrix Vest
variable (P:Flight j k)(h:f.val=c.val*P.L.val)(K:KernelChoices)
variable (H₀ H₁ :Bed)(A:Towers P.patch.L) -- P.patch namespace?
set_option quotPrecheck false
local notation "ϕ"=> P.visit K h
variable (hu:(curtain su (Flight.visit P K h) H₀ H₁ A).IsSymm)
-- exact ambulatory.
-- standard tagged truncation certificate.S.Final Burch cost.LINEVS.
variable {P S:Tone (Kh f) (Dh f N I) (Kh c) (Dh c N I)}
variable (w:I→ℝ)(z: Finset I) (gT:Hypnos.State su)
variable (fP:Quince f N I) (o:I→ Site f) {Vt:Finset (Finset I)} {x y s ε e ξ φ R0 d v:ℝ}
local notation "Dv"=> Dh c N I
local notation "Lo" T:arg => Play.Chamber.switch fP (T).P (T).Q (T).M (T).V
variable (hp : Tone.Rich S x)(hs:P.Rich x)(hv: P.Gale S s)
variable (he:SetL o Vt B l k m fP)
variable (ht: ∀ i∈ Vt,i.Nonempty→cents (fP i)≤ y^i.card)
variable (hu:z∈Vt) (h':∀ i:Finset I,i⊆ z →i∈Vt) (hz:z.Nonempty)(hy:1 ≤ y)(hl:z.card ≤ l)
open Vest.Tuck FlareV
noncomputable abbrev linearV {σ:Side}(β:ℝ) (U:Directions su σ): Kh σ →ℝ:= fun z=> β⁻¹*Fruit.jet U z
lemma tender0 (ht:|ξ⁻¹| ≤ s)(U:Directions su c)(r:ℝ)(hp:‖U‖≤r)(hv:r ≤gT.web.radius)(j:Kh c): ‖karm ξ (increment 1 U) j-linearV ξ U j‖ ≤ s*gT.web.scale*r^2 :=by
     change ‖ξ⁻¹*Hypnos.marrow (increment 1 U) (bleep j) j.2.2 - ξ⁻¹ * Fruit.jet U j‖ ≤ _; rw [← mul_sub,norm_mul, mul_assoc]; exact mul_le_mul ht (MassiveQCD.Rebus.breezeK U j gT.web hp hv) (norm_nonneg _) ((abs_nonneg _).trans ht)
local notation "Q0"=> cpalm x y l k m
local notation "A0"=> caulk x s y l k m
local notation "Gz"=> MassiveQCD.FlareV.give w z
include hp hs hv he ht h' hz hy hl
lemma payL (U: Directions su c)(hs':0 ≤ s)(hG:1 ≤ R0)(hq:‖give w z‖≤ R0) (hW:|ξ⁻¹| ≤ d) (hV:‖U‖≤v)(hH:v≤gT.web.radius)(hy0:1 ≤ e)(hC:d*(gT.web.scale*v+gT.web.scale*v^2)≤e): ‖(Gz • Oce.rose Dv (karm ξ (increment 1 U)) ((Lo S) z)) - Gz • Oce.rose Dv (linearV ξ U) ((Lo P) z)‖ ≤ R0*((l*k:ℕ)* e^(l*k)*(d*gT.web.scale*v^2)*Q0^l+ e^(l*k)*A0) :=by
     let a:=karm ξ (increment 1 U); let b:=linearV ξ U; have hd:0≤d:= (abs_nonneg _).trans hW
     let F:=gT.web.scale; have hf:1 ≤ F:=gT.web.cost; have ht':0 ≤v:= (norm_nonneg _).trans hV
     have hg: Oce.bill a univ e:=fun i _=> ((MassiveQCD.Rebus.gust U i gT.web ξ hV hH).trans (mul_le_mul_of_nonneg_right hW (show 0 ≤ F*v+F*v^2 from by positivity))).trans hC
     have hk: Oce.bill b univ e:=fun i _=> by
         refine le_trans ?_ hC; unfold b linearV; rw [norm_mul]; exact mul_le_mul hW ((MassiveQCD.Rebus.linearK U i gT.web hV).trans (le_add_of_nonneg_right (show 0≤ F*v^2 from by positivity))) (norm_nonneg _) hd
     let b₁:= d*F*v^2; have hK:0≤b₁:=by unfold b₁; positivity
     let q:= Lo S; let Q:=Lo P
     -- Need biUnion deq explicit inst.L
     have h p (hξ:p ⊆ z)(hz:p.Nonempty) :=he.scope p (h' p hξ) hz; have hx p (hv:p⊆ z):=ht p (h' p hv); have hG0:Tuck.cpalm x y l k m≥1:=one_le_mul_of_one_le_of_one_le hy (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (Tuck.em_pos hp.craze) (one_le_pow₀ (by norm_num))) (MassiveQCD.Rebus.sageMoney l))
     have hv0 (T:Tone (Kh f) (Dh f N I) (Kh c) (Dh c N I)): (Lo T) z∈ Bera.Camp univ (l*k):= (leaguer (Play.Chamber.move fP _ _ T.P T.Q T.M T.V h (fun _=>univ) (fun _=>univ) (fun _ _ _ _ p _=>mem_univ p) (fun _ _ _ _ p _=>mem_univ p)) (subset_univ _) (subset_univ _) (Nat.mul_le_mul_right k hl) (Nat.mul_le_mul_right m hl)).2
     have hy1: ‖Oce.rose Dv a (q z)- Oce.rose Dv b (q z)‖≤ (l*k:ℕ)* e^(l*k)*b₁*Q0^l :=by
        apply (Oce.tang a b _ (hv0 S) hg hk hy0 (fun i _=> tender0 gT hW U v hV hH i) hK).trans; let U:=(l*k:ℕ); rw [show ↑U*(d*gT.web.scale*v^2)*e^U = (U:ℝ)*e^U*b₁ from by unfold b₁ F; ring]; exact mul_le_mul_of_nonneg_left ((Tuck.veks S fP h hp hl hy hx z (Subset.refl _)).trans (pow_le_pow_right₀ hG0 hl)) (by positivity)
     have hu1: ‖Oce.rose Dv b (Q z)-Oce.rose Dv b (q z)‖≤ e^(l*k)*A0 :=by
          rw [← map_sub]; exact (Oce.cares (Submodule.sub_mem _ (hv0 P) (hv0 S)) hk hy0).trans (mul_le_mul_of_nonneg_left (columnP P S fP h hs hp hv hl hy hx hs' z (Subset.refl _)) (pow_nonneg (zero_le_one.trans hy0) _))
     rw [← smul_sub,norm_smul]
     exact mul_le_mul hq ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hy1 ((norm_sub_rev ..).le.trans hu1))) (norm_nonneg _) (zero_le_one.trans hG)
end YM.MassiveQCD.TimesV
#print axioms YM.MassiveQCD.TimesV.payL

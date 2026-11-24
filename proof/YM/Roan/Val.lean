import YM.Roan.Mime
import YM.Roan.Rule
import YM.Roan.Royal
import YM.Clink.Brass
import YM.Kwick.Vale
import YM.Roan.Ode
import YM.Lapin.Spark
/-! End read at reference upper Hop boot.Several charts transfer.X near arbitrary.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Pane Tawny.BendR
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
/- Need Shelf.Guru.Bind at references. Keep full Tally + price lower.S
-/
variable {S:Scheme}{R:Side} (A:Run S N R 6) (q:ℕ)(T:TaperHol)
-- for any authentic entries.P1 vector extracted unique and provides growth comparisons.Progress.Act emission estimate.S.
set_option maxHeartbeats 700000
open Next.Free QCD.Entr QCD.Entr.Meridian QCD.Flume
variable (a:Flavor 6)(hA:A.Actual)(h:q ≤ N) (P:QCD.Flume.Plan d)(H:Train d)(z:ℝ)
variable (n:ℕ)(hp:n ≤ q)
open Tawny Tawny.Cast.Rays Tawny.Pane Tawny.BendR QCD.Entr.Goals Seals
variable (D D1:ℝ)(Z1 Z2 Z3:RawVec 10)(P': BudgetPoint)(u:Averaging)
local notation "Zφ"=> report (Aim)
local notation "φ"=> A.density n
local notation "Qp" X:arg=> report A X u n 0
local notation "Fo" X:arg=> Canvas.foil φ (Qp X)
local notation "Y"=> corm (i:=q) A d P H z a 0
local notation "V"=> marque (i:=q) A true a 0
local notation "G"=> sprigs (i:=q) A a 0
local notation "g"=> Gpick
local notation "K"=> S.side R n
open TorusPCAC.Geometry
-- growth lead.R0.C Mat. 
local notation "pm"=> prismB
local notation "MΩ"=> (Zinc.whirl Gpick (gamma 1)) aux1 aux2
local notation "Pκ"=> (-(2:ℂ)*wave (gamma (0:Axis)*gamma 1) ax1 ax2)
-- at either k,t forecast upper.Trans.
noncomputable def billR (C:ℝ)(L:Side)(D:ℝ):ℝ:= ‖MΩ⁻¹‖* ((L.val:ℝ)⁻¹*C*D)
noncomputable def taxP (L:Side)(D:ℝ):ℝ:= ‖Pκ⁻¹‖*(costQ 2*tick L *D)
variable (Cζ C2:ℝ) (hC: WealthR T P' Cζ C2) (p:ℕ)
local notation "b₁"=> taxP K
local notation "b₂"=> billR C2 K
noncomputable def toll_b (F:Density c 6): Flavor 6→ℂ:= fun p=> Pκ⁻¹ *river1 1 p ax1 ax2 F
noncomputable def toll_q (F:Density c 6): Flavor 6→ℂ:= fun p=> MΩ⁻¹* river2 0 1 p aux1 aux2 Gpick F
include hA h hC hp a
lemma ticketsP (F:Density K 6)(Z:RawVec 10)(hF:Tally T 0 (Z.val 0) φ F)(hv:SungP F)(ht:Allow P' g (Canvas.foil φ F) p D)(hm:10≤ p): ‖prismA Z-toll_b (Canvas.foil φ F)‖≤ taxP K D ∧ ‖prismB Z-toll_q (Canvas.foil φ F)‖≤ billR C2 K D:=by
      let Q:=Canvas.foil φ F; have hd:0 ≤ D:= (peaks_g ..).trans (ht.heatL a ax1 ax2)
      constructor
      · apply (pi_norm_le_iff_of_nonneg ?_).mpr; · intro p; change ‖Pκ⁻¹*_ - Pκ⁻¹* _‖ ≤ _; rw[norm_sub_rev,← mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (bracken P' g 1 T ax1 ax2 p φ F (Z.val 0) hF ht) (norm_nonneg _)
        unfold taxP; exact mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (costQ_p _ (by norm_num)) (tick_g _).le) hd)
      apply (pi_norm_le_iff_of_nonneg ?_).mpr; · intro i; change ‖MΩ⁻¹*_ - MΩ⁻¹*_‖ ≤_; rw [norm_sub_rev,← mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (hC.spirit _ F φ p D (Z.val 0) ht (treated _ _ (dSung A hA (hp.trans h)) hv) hF hm i aux1 aux2) (norm_nonneg _)
      unfold billR; positivity[hC.q_nn]
-- post
variable (X:Sail) (hu:u= Option.some X)
include hu
lemma ducks (hD:Allow P' g (Fo Y) p D)(he:Allow P' g (Fo V) p D1)(hz:Tally T 0 (Z1.val 0) φ (Qp Y))(hP:Tally T 0 (Z2.val 0) φ (Qp V))(ho:10 ≤ p) : ‖prismA Z1- prismA Z2‖ ≤ taxP K D + taxP K D1 ∧ ‖prismB Z1-prismB Z2‖ ≤ billR C2 K D+ billR C2 K D1:=by
       have hv:= wool A a 0 u P H z hp X hu
       have hF:= stampC (axle true a 0) A hA h u
       have heY:TideT A u q (report A Y u):=blendT _ _ _ _ hF (b_stem A hA h d P H z a 0 u)
       have hT(p':Flavor 6)(i j:Fiber):= ζblink A hA h p' 0 1 Gpick u i j X hu hp hz.unit Y V hv hD.alive he.alive heY hF (show 1≤p from by omega)
       let Z0:= Fo Y; let V0:=Fo V; have hZ₁:toll_b Z0= toll_b V0:=funext fun s=> congr_arg (fun e:ℂ=>Pκ⁻¹*e) (hT s ax1 ax2).1; have hZ₂:toll_q Z0=toll_q V0:=funext fun s=> congr_arg (fun e:ℂ=>MΩ⁻¹*e) (hT s aux1 aux2).2
       have he1:SungP (⇑(Qp V)):= entireS _ _ _ _ (fun o=>inkS A hA (axle true a 0) _ h) hp
       have he2:SungP (⇑(Qp Y)):= by
              apply entireS _ _ _ _ _ hp
              intro o t v; change slots 6 t ((_)+_)=_+_; rw [map_add]; exact congr_arg₂ (·+·) (inkS A hA (axle true a 0) o h t v) (smolt A hA h d P H z a 0 o t v) -- note arg. 
       have hY:= ticketsP A q T a hA h n hp D P' Cζ C2 hC p (Qp Y) Z1 hz he2 hD ho; have hY':=ticketsP A q T a hA h n hp D1 P' Cζ C2 hC p (Qp V) Z2 hP he1 he ho; rw[show toll_b (Fo V)=_ from hZ₁.symm,show toll_q (Fo V)=_ from hZ₂.symm,norm_sub_rev (prismA Z2), norm_sub_rev (prismB Z2)] at hY'; exact ⟨(norm_sub_le_norm_sub_add_norm_sub _ (toll_b Z0) _).trans (add_le_add hY.1 hY'.1),(norm_sub_le_norm_sub_add_norm_sub _ (toll_q Z0) _).trans (add_le_add hY.2 hY'.2)⟩
lemma shirtP (hD:Allow P' g (Fo G) p D)(hz:Tally T 0 (Z1.val 0) φ (Qp G))(ho:10 ≤ p): ‖prismA Z1‖≤ taxP K D ∧ ‖prismB Z1‖ ≤ billR C2 K D:=by
       have hh(p': Flavor 6)(i j:Fiber) := ξblink A hA h p' 0 1 Gpick u i j X hu hp hz.unit G (ZW A a 0 u hp X hu) hD.alive (nour A hA h _ _ _) (show 1 ≤ p from by omega)
       let Z0:= Fo G; have hb: toll_b Z0=0:=by funext p; change _*(river1 _ _ _ _ _)=0; rw [(hh p ax1 ax2).1,mul_zero]
       have ht:toll_q Z0=0:=by funext p; change _*(river2 _ _ _ _ _ _ _)=0; rw [(hh p aux1 aux2).2,mul_zero]; -- elaborate
       have hZ:= ticketsP A q T a hA h n hp D P' Cζ C2 hC p _ Z1 hz (entireS _ _ _ _ (fun o=>sym_Q A hA h _ _ o) hp) hD ho; rw [show toll_b (Fo G)=0 from hb,show toll_q (Fo G)=0 from ht,sub_zero,sub_zero] at hZ; exact hZ
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.ducks
#print axioms YM.Massive.Patria.Gall.Cahoots.shirtP

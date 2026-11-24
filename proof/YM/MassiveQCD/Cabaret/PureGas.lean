import Mathlib.Analysis.SpecialFunctions.Exponential
import YM.MassiveQCD.Cabaret.Pier
import Mathlib.Analysis.Complex.LocallyUniformLimit
/-! # Turning analytic K families. At ANY strength without τ interpolation of layouts; every mask, real, complex. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut Patron
variable (dep : ι→ℕ)(ζ ζ₀ : ℂ)
variable (M:ℂ→ι→Grid f→Grid c→EvenA c N)(s:Y.Wort)(V:Grid c)(χ:Chi)
local notation "A"=>fun z=>Y.tintF (M z)
variable (h:∀ z:ℂ, ‖z‖≤1→∀ i U V, M z i U V=z^dep i • Y.works i U V) (hp:Summable (honest Y χ V))(hY:∀ z:ℂ, ‖z‖<1→(Y.tintF (M z)).Famous)
local notation "P!"=>Metric.ball (0:ℂ) 1
include h
lemma dawnS (D:Y.Dark): DifferentiableOn ℂ (fun z=>(((A) z).duskV χ V D)) P!:=by
     refine (show DifferentiableOn ℂ (fun z:ℂ=> z^depthF dep D.val • vF Y D.val χ V) P! from by fun_prop).congr ?_
     exact fun z hz=> Y.speedS dep z (M z) χ (h z ((mem_ball_zero_iff.mp hz).le)) D.val V
include hp hY
lemma swivel (i:Y.Faber): DifferentiableOn ℂ (fun z=> mission (Y.tintF (M z)) χ V i.val) P!:=by
    let K (z:ℂ):= (A) z; let f z:= (K z).dawnV χ V; let g z:= (K z).duskV χ V; let U:= RG.flags (Pressure.temp τ) V
    have hg j:= dawnS Y dep M V χ h j; let v:=i.val
    change DifferentiableOn ℂ (fun z=> motto Y.broad Y.invD Y.lightF U (g z) (f z) v) P!
    unfold motto; split; swap; · exact (differentiableOn_const _)
    apply DifferentiableOn.fun_finsetProd; intro i hi; cases i with
    | inl d=> exact hg d
    | inr W=>
       let y:=fun z=> -(portion Y.lightF (f z) W); have hh (z:ℂ) (hx:z∈P!) (s:Clusters Y.Bright): termP (blocked Y.lightF) (f z) s=z^(Y.depthT dep s) • honest Y χ V s:= (phoenix (K z) χ V (hY z (mem_ball_zero_iff.mp hx)) s).symm.trans (Y.paysS dep z (M z) χ (h z ((mem_ball_zero_iff.mp hx).le)) s V)
       let L(s:Clusters Y.Bright)(z:ℂ):= if seatP Y.lightF s=W then termP (blocked Y.lightF) (f z) s else 0
       have hf:DifferentiableOn ℂ y P!:= by
           apply DifferentiableOn.neg (E:=_) ?_; change DifferentiableOn ℂ (fun z:ℂ=> ∑' i,L i z) P!
           refine Complex.differentiableOn_tsum_of_summable_norm hp.norm ?_ Metric.isOpen_ball ?_
           · intro i; unfold L; split; swap; · exact (differentiableOn_const _)
             apply DifferentiableOn.congr _ (fun z h=>hh z h i); fun_prop
           intro i z hz; unfold L; split; next _=> rw [hh z hz i,norm_smul]; apply mul_le_of_le_one_left (norm_nonneg _); rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz).le
           next _=> rw [norm_zero]; exact norm_nonneg _
       refine (?_ : DifferentiableOn ℂ (fun z=> NormedSpace.exp (y z)-(1:EvenA c N)) P!)
       exact DifferentiableOn.sub (fun z hz=>(_root_.hasFDerivAt_exp (𝕂:=ℂ)).differentiableAt.comp_differentiableWithinAt z (hf z hz)) (differentiableOn_const _)
lemma fundsRead (i:Y.Faber): AnalyticOnNhd ℂ (fun z=>(claim (Y.tintF (M z)) χ).warp i V) P! :=(swivel Y dep M V χ h hp hY i).analyticOnNhd Metric.isOpen_ball
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.fundsRead

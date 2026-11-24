import YM.MassiveQCD.Mayer.Sen
import YM.QCD.High.Stroll
/-! # Criterion for the Mayer-log step of a priced support
 Includes ALL calibrated powers. Logs used at value-only without smoothness on bad flags.
 Direct ties to mass meters reference of true QCD. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {c:Side}{N:ℕ}{o:Site c}{B:Support c}{t q a r:ℝ}{k n:ℕ}
local notation "Z"=>EvenA c N
local notation "Q"=>Sen (N:=N) o t
open MassiveQCD.Analysis.Many
variable {V:Config su c}{f g:Grid c→EvenA c N}{p:BudgetPoint}{D:Directions su c→Prop}
lemma log_gate {x:Z}(h:Gated B x): Gated B (logM x):= by
    unfold logM; apply Territory.spearm; intro i; apply Territory.club; unfold Gated; rw [map_pow]; exact Subalgebra.pow_mem _ h _
lemma log_borel (f:Grid c→Z) (h:Measurable f): Measurable (logM ∘ f):=Measurable.tsum (fun (i:ℕ)=> measurable_const.smul (h.pow_const i)) -- syntax
lemma log_budget (ht: 1 ≤ t)(h:Woven o B p t f a)(hx:a≤1/2): Woven o B p t (logM ∘ f) (logFee p.order*a):=by
    refine ⟨fun _ _ hv=> congr_arg logM (h.room _ _ hv),fun V=>log_gate (h.gated V),fun V hi=> ?_,fun V hi=> stampLog ht (h.use V hi) (h.pole V hi) hx, log_borel f h.Borel, mul_nonneg ((by norm_num : (0:ℝ)≤ 2).trans (logFee_post _)) h.travel⟩
    exact (shallow (h.use V hi) ((((pass_high (f V) ht (o:=o)).trans (h.sizeU V hi)).trans hx).trans_lt (by norm_num))).1
lemma log_honors (M:Z →+* Z)(hp:Continuous M)(he: Bijective M)(v:Z): M (logM v) = logM (M v):=by
    let X:= M.toAddMonoidHom.toRealLinearMap hp
    let Y:EvenA c N ≃L[ℝ] EvenA c N:= (LinearEquiv.ofBijective X.toLinearMap he).toContinuousLinearEquiv
    unfold logM; change Y _= _; rw [Y.map_tsum]; refine tsum_congr (fun i=>?_); change M _ = _; rw [eSM M hp,map_pow]
open High.PrismT
lemma unmaskA (x:Z)(h:‖x‖<1)(he:Reggae.mud x=0): mud (logM x)=0 ∧ ∀ b:Flavor N,meter b (logM x)=meter b x:=by
    let f i:= coeffM i • x^i
    have hK : HasSum f (logM x):= (logs h).of_norm.hasSum -- prefix mismatch abbrev
    have he₁ : mud (logM x)=0:=by
      let p:= (clay c N).restrictScalars ℝ; rw [show mud (logM x)=∑' i,p (f i) from (p.hasSum hK).tsum_eq.symm]; conv_rhs => rw [← (show (∑' _:ℕ,(0:ℂ))=0 from tsum_zero)]
      apply tsum_congr; intro i; unfold f; rw [map_smul]; by_cases h:i=0; · subst i; simp [coeffM]
      rw [show p (x^i)=0 from ?_,smul_zero]; exact High.PrismT.held x i he (by omega)
    refine ⟨he₁,fun b=>?_⟩; rw [← proud b (logM x) he₁,soothe x h,map_add,begins,zero_add]
    -- need previous. bind ↑
    -- edit combine hYoga
lemma turns_log (h:shadeG f): shadeG (logM ∘ f):=by
    intro i k; exact congr_arg Subtype.val (Eq.trans (log_honors _ (phare _) (surfeit (copies_unitary _ _ (siteRot_u k))) _) (congr_arg logM (Subtype.ext (h i k))))
end YM.QCD.Stew.Phased

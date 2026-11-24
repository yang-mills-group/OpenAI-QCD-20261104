import YM.QCD.Rain.Vows
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
open Acre Rails PhysicalNext.Repeat Raft ParcelR Sq
variable {f:Side}{k: ℕ}{K:KernelChoices}
-- namespaces.Tuning uses j
noncomputable def peakW (L:Side)(N:ℕ): EvenA L N→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap ((ber (Modes L N)).comp (Cove.light _).toLinearMap)
noncomputable abbrev cBer (x:Pixel c N)(U:Grid c):ℂ:= peakW c N (x U)
def realP {n:Side}(x:Pixel n N):Prop:= ∀ V, cBer x V = ((cBer x V).re:ℂ) ∧0 ≤ (cBer x V).re
noncomputable abbrev Cvol (x:Pixel c N):ℂ:= ∫ U,cBer x U ∂prior su c
noncomputable def gain (q:ℝ)(c:Side)(N:ℕ):ℝ:=q^(Fintype.card (Keys c N))
lemma crestP (V:EvenA c N)(t:ℝ): (ber _ (Cove.light _ (wearK c N t V)))=(gain t c N:ℂ)*peakW c N V:=by
    let n:= Keys c N
    change (ber _ (engine t n (Cove.light n V)))=(gain t c N:ℂ)*ber _ (Cove.light n V); unfold ber gain; unfold n; rw [show Fintype.card (Keys c N) = Fintype.card (Pairs (Modes c N)) from rfl]; simp only [LinearMap.smul_apply,fundW,smul_eq_mul, Complex.ofReal_pow,card_univ]; ring
section sol
variable (S:YM.Next.Free.Flight j j)(h: f.val=c.val*S.L.val)(X:Pixel f N)(T:KernelChoices)
lemma tenderL (he:Continuous X):Continuous (can S h N X):=by
      have hf : Continuous (fun i:Grid f=> (ater S h i (F:=N),Cove.light (Keys f N) (X i))) := (signsR (S:=S) (h:=h) (N:=N)).prodMk ((lightC (Keys f N)).comp he)
      have hp := (Kit.sheath_cont (A:=Modes f N) (B:=Modes c N) (b:=1)).comp hf
      exact hp
variable (hK:S.patch.Branches T su) (hx: Continuous X)
include hx hK
set_option maxHeartbeats 700000 in
lemma living (p:ℝ): Continuous (advance S T h X p):=by
     rw [continuous_iff_continuousAt]; intro i; rw [← continuousWithinAt_univ]; have he:Integrable (can S h N X) (prior su f):=(tenderL S h X hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..); exact (Push.BetaTransport.push_continuousWithinAt (S.visit T h) hK (b:=fun _=>p) (y:=i) continuousWithinAt_const continuousWithinAt_id (V:=id) (F:=fun _=>can S h N X) he (Eventually.of_forall fun _=> he.1) (ae_of_all _ fun _=> continuousWithinAt_const) he.norm (Eventually.of_forall fun _=> ae_of_all _ fun _=> le_rfl)).2
lemma assets (w:ℝ)(V:Grid c)(hV: realP X) : let u:= ber _ (advance S T h X w V); u=(u.re:ℂ)∧ 0 ≤ u.re:=by
   intro z; let Y:= S.visit T h; have hh:Y.IsKernel w su:=Y.isKernel hK _
   have he:=Y.push_slice hh V _ ((tenderL S h X hx).integrable_of_hasCompactSupport (μ:=prior su f) (HasCompactSupport.of_compactSpace (f:=can S h N X) ..)) -- signature
   let l (i:Grid f):= Y.density w i V; let H:=LinearMap.toContinuousLinearMap (ber (Modes c N)); let g (i:Grid f):= l i*(cBer X i).re
   have hz(i:Grid f):H (l i • can S h N X i)=(g i:ℂ):=by
       rw [show l i • can S h N X i= ((l i):ℂ) • _ from rfl,map_smul]; change ((l i):ℂ)*ber _ (sheath 1 (ater S h i) _)=_; rw [insulate (by norm_num : (1:ℝ)≠ 0)]; change ↑(l i)*cBer X i =_; rw [(hV i).1]; unfold g; norm_cast -- bad rewriting re
   have hm:z= ((∫ i,g i ∂prior su _) :ℝ):=by
        change H (∫ i, l i • can S h N X i ∂prior su f) =_; rw [← H.integral_comp_comm he]; rw [← integral_complex_ofReal]; apply integral_congr_ae (ae_of_all _ hz)
   rw [hm]; exact ⟨rfl,integral_nonneg (fun i=> mul_nonneg (hh.positive _ _) (hV i).2)⟩
lemma marching (w:ℝ) (Y:Pixel c N)(hp:0<t)(he:∀ i,advance S T h X w i=gBody _ t (Y i)) : Continuous Y ∧ Cvol X=gain t⁻¹ c N • Cvol Y:=by
    have hv i:Y i=(songT t) (fort S T h N w X i):=by rw [fort, Function.comp_apply,he, gBody,callH]; exact (wit _ _ _ (mul_inv_cancel₀ hp.ne')).symm
    let R:=can S h N X; let F:=S.visit T h; have hI:F.IsKernel w su:=F.isKernel hK _; have he' :Integrable R (prior su f):=(tenderL S h X hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..); have hp' := F.push_integrable hI _ he'; let G:=LinearMap.toContinuousLinearMap (ber (Modes c N))
    constructor
    · rw [funext hv]; exact Continuous.comp (songT t|>.continuous) ((levit c N).continuous.comp (living _ _ _ _ hK hx _))
    have hJ:Cvol X = ∫ V:Grid c, G (advance S T h X w V) ∂prior su c:=by
          unfold advance; rw [G.integral_comp_comm hp', F.push_integral hI R he', ← G.integral_comp_comm he']; unfold Cvol; apply integral_congr_ae (ae_of_all _ fun _=>?_); exact (insulate (by norm_num : (1:ℝ)≠ 0) _ _).symm
    rw [hJ,←integral_smul]; refine integral_congr_ae (ae_of_all _ fun i=>?_); dsimp only; rw [he]; exact crestP ..
end sol
end YM.QCD.Rain

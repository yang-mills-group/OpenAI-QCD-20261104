import YM.QCD.Stew.Stitch
/-! # after gauge money. Fixed Craft pre-renewal. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port Jets Jets.Sun
variable {B: Support c}{C : ℝ}
def tunnel (N:ℕ)(C:ℝ):=9*fingers N^2 * ‖goldW‖+foamer C N
lemma firm (N:ℕ)(he:0≤C):0≤tunnel N C:=by unfold tunnel foamer; positivity
variable (hp:stratum C n o p) (ht:0<a)(he:0≤C)
lemma boardFee (ht:0<a) (M:Spike) (N:ℕ) : Sen o a (paleF N (localX o M)) ≤ 9*fingers N^2 * ‖goldW‖*(a^2*‖M‖):=by
    have hi:o∈ stand o:= halo_subset 2 _ (Finset.mem_singleton_self _)
    rw [siteBl]; apply (budgetBl _ _ _ hi hi ht N).trans; exact (mul_le_mul_of_nonneg_left (goldW.le_opNorm M) (by positivity : 0 ≤ 9*a^2*fingers N^2)).trans_eq (by ring)
-- stencil norm SUP even on unhealthy V
lemma roadA (o : Site c)(M: Spike)(j:Axis)(U:Grid c): entry o M (some (j,true)) U=(2:ℂ)⁻¹ • (localX o M* leg 0 U (posDir j))+ (-(2:ℂ)⁻¹) • (localX o M*leg 0 U (negDir j)):=by
    change localX o M*delta U j= _; unfold delta; rw [Matrix.mul_smul,mul_sub,smul_sub,sub_eq_add_neg,neg_smul]; rfl
lemma roadR (x y:Grid c→Sheet c)(hv:Woven o B p a (paleF N ∘ x) u)(hp:Woven o B p a (paleF N ∘ y) u): Woven o B p a (fun i=> paleF N (((2:ℂ)⁻¹) • x i+ (-(2:ℂ)⁻¹) • y i)) u:=by
    let t:ℝ:=(2:ℝ)⁻¹; have hr : ‖t‖*u+‖-t‖*u=u:=by unfold t; rw [norm_neg,norm_inv]; norm_num; ring
    have he : ∀ s:Sheet c,((2:ℂ)⁻¹) • s=t • s:=by intro i; rw [show (2:ℂ)⁻¹=(t:ℂ) by simp [t],Complex.coe_smul]
    let Z:= (t • (paleF N ∘ x))+ (-t) • (paleF N ∘ y); have hQ: ∀ A:ℝ,∀ i:Sheet c,paleF N (A • i)= A • (paleF N i):=fun v x=> map_smul (ContinuousLinearMap.restrictScalars ℝ (nozzle c N)) v x
    rw [show (fun _=> _)= Z from ?_]; · exact hr ▸ ((hv.byScalar t).addition (hp.byScalar (-t)))
    funext i; rw [oneC,he, neg_smul,he, ← neg_smul,hQ,hQ]; rfl
include he ht hp
lemma headwind (N:ℕ)(M:Spike)(s:SampleX) : Woven o (stand o) p a (fun U=> paleF N (entry o M s U)) (tunnel N C*(a^2*‖M‖)):=by
    let q:=tunnel N C; let y:=foamer C N; have hk: y*(a^2*‖M‖) ≤ q*(a^2*‖M‖):= mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity); have hj(o:Site c): o∈ stand o:= halo_subset 2 _ (Finset.mem_singleton_self _)
    rcases s with _|⟨j,_|_⟩
    · let v:=paleF N (localX o M); change Woven o _ _ _ (fun U=>v) _; have hG:Gated (stand o) v:=by unfold v; rw [siteBl]; exact padBl _ _ _ (hj _) (hj _)
      refine ⟨fun _ _ _=> rfl,fun _=>hG,fun i _=>contDiffAt_const,fun i hi l ha hz=> ?_, (show Measurable (fun _:Grid c=> v) from measurable_const),by exact mul_nonneg (firm _ he) (by positivity)⟩
      cases l with
      | nil=> exact (boardFee ht M N).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by unfold foamer; positivity)) (by positivity))
      | cons i l=> rw [show leftDerivs _ _ _=(0:EvenA c N) from (Work.G07.left_const v (i::l) _),← measures,map_zero,norm_zero]; exact mul_nonneg (firm _ he) (by positivity)
    · apply Woven.stretches (c:=c) ?_ (Subset.refl _) hk; simp_rw [hero _ o M j, roadA, star_add, star_smul]; rw [star_neg,star_inv₀,star_ofNat,show y*(a^2*‖M‖)=y*(a^2*‖star M‖) by rw [norm_star]]; exact roadR _ _ (hale hp ht he (star M) _ N).2 (hale hp ht he (star M) _ N).2
    simp_rw [roadA]; apply Woven.stretches _ (Subset.refl _) hk; exact roadR _ _ (hale hp ht he M _ N).1 (hale hp ht he M _ N).1
-- all fields no healthy. for Soft remainder. deriv may specialized hw any because charts global. Woven bound enough? needs all-field for Loc, prove substitute B.lemma
end YM.QCD.Stew

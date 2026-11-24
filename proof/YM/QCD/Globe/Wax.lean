import YM.QCD.Globe.Pam
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Trees Brick Nola
variable {a T C D V r δ A v d:ℝ} {L:Side}
lemma choose₀ : ∃ δ:ℝ,0 < δ ∧ δ ≤ 1∧degreePriceCard (Real.exp δ-1) 1 ≤1/2:=by
   let f(x:ℝ):=degreePriceCard (Real.exp x-1) 1; have hf : Continuous f:=by unfold f degreePriceCard stretchCard; fun_prop
   have hz:f 0=0:=by simp [f,degreePriceCard,stretchCard]
   have he: ∀ᶠ x in 𝓝[>] (0:ℝ), x ≤ 1 ∧ f x ≤1/2:=mem_nhdsWithin_of_mem_nhds ((eventually_le_nhds zero_lt_one).and ((hf.tendsto _).eventually_le_const (show f 0<1/2 by rw [hz]; norm_num)))
   obtain ⟨x,⟨h1,h2⟩,hx⟩:=(he.and self_mem_nhdsWithin).exists; exact ⟨x,hx,h1,h2⟩
lemma fern_goal : Tendsto (fun L:Side=>(L.val:ℝ)) atTop atTop:= by
    refine tendsto_natCast_atTop_atTop.comp (show Tendsto (fun L:Side=>L.val) atTop atTop from ?_)
    apply tendsto_atTop.2; intro b; filter_upwards [eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with i hi; exact le_trans (Nat.le_succ _) hi
lemma ask (C A:ℝ)(h:0 ≤ C) (he:0≤A) :∃ L₀:ℕ,∀ L:Side, L₀≤ L.val→ A*cape L 0 ≤ 1 ∧ (L.val:ℝ)^4*C*(A*cape L 0)^4 ≤ 1:=by
    have hu:Tendsto fern atTop (𝓝 0):=tendsto_inv_atTop_zero.comp fern_goal
    have hx : (∀ᶠ L:Side in atTop,A^2*(fern L)^3≤ 1) := (show Tendsto (fun L=> A^2*(fern L)^3) atTop (𝓝 0) from (by simpa using ((hu.pow 3).const_mul (A^2)))).eventually_le_const zero_lt_one
    have hh: ∀ᶠ L:Side in atTop,C*A^4*fern L^2 ≤1:=(show Tendsto (fun L=> C*A^4*fern L^2) atTop (𝓝 0) from by simpa using ((hu.pow 2).const_mul _)).eventually_le_const zero_lt_one
    obtain ⟨L,H⟩:= Filter.eventually_atTop.mp (hx.and hh); refine ⟨L.val,fun E h=> ⟨?_,?_⟩⟩
    · have hp:= (H E h).1; rw [← capeQ E,← mul_pow] at hp; nlinarith
    refine le_trans ?_ (H E h).2; rw [mul_pow]; rw [show cape E 0^4=fern E^6 from (by rw [show 4=2*2 from rfl,pow_mul,capeQ,← pow_mul] : _)]; exact le_of_eq (by unfold fern; field_simp) -- maybe syntax
noncomputable def spoolM (δ a:ℝ):= (2*a/δ)
noncomputable def coastW (L:Side)(δ:ℝ)(a:ℝ):=(L.val:ℝ)^4 * 2^6 * (spoolM δ a*(Real.exp δ-1)*2)
noncomputable def titanic (C:ℝ)(L:Side):=2*(C*cape L 0)
noncomputable def riderW (C:ℝ)(L:Side)(N:ℕ):=stemF N*titanic C L*(4*(Real.exp 2))
lemma tackle (ht:0 < δ)(h:0 < C)(N:ℕ):∃ L₀:ℕ,∀ L:Side,L₀ ≤ L.val→ ∀ a:ℝ,0<a→ riderW C L N ≤ 1∧ coastW L δ a*(riderW C L N)^4≤ a:=by
    let A:=2^6*((2/δ)*(Real.exp δ-1)*2); let B:= stemF N*(2*C)*(4*Real.exp 2); have hA:0 ≤ A:=by unfold A; have he:0 ≤ Real.exp δ-1:=sub_nonneg.mpr (Real.one_le_exp ht.le); positivity
    obtain ⟨L,H⟩:=ask A B hA (by unfold B stemF Jets.Sun.fingers; positivity)
    refine ⟨L,fun S hp a he=>?_⟩; rw [show riderW C S N=B*cape S 0 from ?_,show coastW S δ a=(S.val:ℝ)^4*A*a from ?_]; exact ⟨(H S hp).1,(by linarith only [mul_le_mul_of_nonneg_right (H S hp).2 he.le])⟩
    · unfold A coastW spoolM; ring
    unfold B riderW titanic; ring
-- financial picks ordered. choose epsilon sharp after S.L. before.C.M numeric polynomial.
lemma asks (ha:0<a) (h:0 < C)(hg:0 < d)(hv:0 < v) (T V:ℝ)(ht:0 < T)(hy:0≤ V): ∀ᶠ r:ℝ in 𝓝[>] (0:ℝ), C*(2*r)≤1/2 ∧ 2^6*(2*C^2*(2*r)) ≤ a ∧2^6*(2*C^3*(2*r)^2) ≤ T*r ∧ 4*T*r ≤1/4∧ dimeZ V (4*T*r)≤d ∧ r≤v:=by
    let g(r:ℝ):= ((2:ℝ)^6*(2*C^3*2^2*r)); have he:Continuous g:=by unfold g; fun_prop
    have hP(k:ℝ)(w:ℝ)(hz:0<w): ∀ᶠ r in 𝓝 (0:ℝ), k*r ≤ w:=((show Continuous (fun r:ℝ=> k*r) from by fun_prop).tendsto _).eventually_le_const (by simpa)
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (hP (C*2) (1/2) (by norm_num)), mem_nhdsWithin_of_mem_nhds (hP (2^6*(2*C^2*2)) _ ha), mem_nhdsWithin_of_mem_nhds ((he.tendsto (0:ℝ)).eventually_le_const (show g 0<T by simpa[g] using ht)), mem_nhdsWithin_of_mem_nhds (hP (4*T) (1/4) (by norm_num)), mem_nhdsWithin_of_mem_nhds (hP ((4*V+2)*4*T) d hg), mem_nhdsWithin_of_mem_nhds (eventually_le_nhds hv)] with r hr ht' h1 h2 h3 h4 h5
    refine ⟨by linarith only [ht'],by linarith only [h1], by linarith only [mul_le_mul_of_nonneg_right (show (2:ℝ)^6*(2*C^3*2^2*r) ≤ T from h2) (show 0 ≤ r from (show 0<r from hr).le)],h3,by unfold dimeZ; linarith only [h4],h5⟩
lemma heft (hC:0 ≤ C)(hT:0 < T) :∃ M:ℝ, 1 ≤ M∧∀ x:ℝ,M≤x→x⁻¹^2*C ≤ T:=by
    have hh:Tendsto (fun x:ℝ=>x⁻¹^2*C) atTop (𝓝 0):=by simpa using ((tendsto_inv_atTop_zero (𝕜:=ℝ)).pow 2|>.mul_const C)
    obtain ⟨Q,H⟩:= (eventually_atTop.mp ((hh.eventually_le_const hT).and (eventually_ge_atTop (1:ℝ)))); exact ⟨Q,(H Q le_rfl).2,fun x hx=>(H _ hx).1⟩
end YM.QCD.Globe

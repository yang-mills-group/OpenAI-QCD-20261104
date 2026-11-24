import YM.Gall.IvyT
import YM.Gall.Cone
/-! S stencil Tally shift active.S/H. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas
variable (g:su.Color)(x: Cover)(P F:Density c 6)
local notation "R"=> foil P F
-- restore exact even when singular_W. Gauge transformation inverse only needed for density unit
abbrev SungP (F:Density c 6):Prop:=∀ k U,slots 6 k (F (Lattice.gauge k U)) = F U
lemma treated (H:SungP P)(hf:SungP F): SungP R:=by
    intro k U; let V:= Lattice.gauge k U; by_cases hp:IsUnit (P V)
    · have hm : IsUnit (P U):= H k U ▸ hp.map (slots 6 k)
      refine Eq.symm ((Ring.inverse_mul_eq_iff_eq_mul _ _ _ hm).mpr ?_); rw [←hf k U,←H k U, ←map_mul]; apply congr_arg -- cyclic? gauge U replaced inside? tactic rewrites U all F U & P U only
      exact Eq.symm (Ring.mul_inverse_cancel_left _ _ hp)
    have hx: ¬ IsUnit (P U):=by
        intro h₀; have he:Lattice.gauge k⁻¹ V=U:=funext fun i=>by simp[Lattice.gauge,V,mul_assoc]
        apply hp; have h:Lattice.gauge k⁻¹ (Lattice.gauge k U)=U := he; rw [←he] at h₀; exact H k⁻¹ V ▸ h₀.map (slots 6 _)
    unfold foil; rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ hp,zero_mul,zero_mul,map_zero]
lemma course (he:∀ᶠ V in 𝓝 (1:Grid c),IsUnit (P V))(ht: march x P=P): foil P (march x F)=ᶠ[𝓝 1] march x (foil P F):=by
    let V(U:Grid c):= pull 1 (wrap c x) U; let X:= foil P F; let U' := foil P (march x F); let K:= crank 1 1 (wrap c x) (heat x) (N:=6)
    have hf:Tendsto V (𝓝 1) (𝓝 1):=by
          have hQ : V 1=1:=by unfold V; rw [pull_one]; rfl
          exact hQ ▸ (continuous_pull ..|>.tendsto 1)
    filter_upwards [hf.eventually he,he] with p hp hu; have hq:= Ring.inverse_mul_eq_iff_eq_mul (P p) ((march x F) p) ((march x X) p) hu; refine hq.mpr ?_; let x':=V p; change K (F x')=P p*K (X x'); rw [show P p= _ from (congr_fun ht p).symm]; change K (F x')= K (P x')* K (X x'); rw [← map_mul]; exact congr_arg K (Ring.mul_inverse_cancel_left (P x') (F x') hp).symm
lemma soonK : Tendsto (kiln (c:=c) g) (𝓝 0) (𝓝 1):=by
    have hc:Continuous (kiln (c:=c) g):=by unfold kiln Rudder.bird; fun_prop
    simpa using hc.tendsto 0
lemma frugal (f q:Density c 6)(h:f=ᶠ[𝓝 1] q)(he: Chart k q 1): Chart k f 1:=by
    have he': Tendsto (increment (1:Grid c)) (𝓝 0) (𝓝 1):=by simpa [increment] using (Further.LogJets.increment_cont (1:Grid c)).tendsto 0
    exact he.congr_of_eventuallyEq (h.comp_tendsto he')
lemma marchC(h:Chart k F 1):Chart k (march x F) 1:=by
    let Q:= wrap c x; let S:Directions su c→L[ℝ]Directions su c:= LinearMap.toContinuousLinearMap { toFun:=fun a i=>a (i.1+Q,i.2), map_add':=fun A B=>rfl,map_smul':=fun t X=>rfl }
    let L: G★→L[ℝ]G★:= (crank 1 1 (wrap c x) (heat x) (N:=6)).toLinearMap.toContinuousLinearMap.restrictScalars ℝ
    have ht: march x F ∘ increment 1= L ∘ (F ∘ increment 1) ∘ S:=funext fun i=>by change L (F (pull 1 Q _))=_; rw [pull_one]; apply congr_arg; apply congr_arg; rfl
    unfold Chart; rw [ht]; exact L.contDiff.contDiffAt.comp _ ((show ContDiffAt ℝ _ _ (S 0) from (by rw [map_zero]; exact h)).comp _ S.contDiff.contDiffAt)
lemma voiceP(u v:Cray c)(h:Chart k F 1)(hk:2≤k) : trade (march x F) g u v = trade F g (floats x u) (floats x v):=by
     let Q:= wrap c x; let L:=crank 1 1 Q (heat x) (N:=6); let f:=shrub F ∘ kiln g; let S:Cray c→L[ℝ]Cray c:=floats x; have hm: shrub (march x F) ∘ kiln g=f ∘ S:= by
          funext i; change oneT (L (F (pull 1 Q _)))=_; rw[pull_one]; exact flat0 (copies 6 _) _ _ -- edit
     have hp:=collinear g 0 _ (show Chart k (shrub F) _ from (by rw [kiln0]; exact shrub_p _ h))
     unfold trade; rw[hm]; unfold crown; let T:= fderiv ℝ f
     let M:(Cray c→L[ℝ]ℂ)→L[ℝ](Cray c→L[ℝ]ℂ):= ContinuousLinearMap.precomp ℂ S -- type
     have hf:ContDiffAt ℝ (2:ℕ∞ω) f 0:= hp.of_le (by exact_mod_cast hk)
     have he:fderiv ℝ (f ∘ S)=ᶠ[𝓝 0] M ∘ T ∘ S:=by
          have hv:Tendsto S (𝓝 0) (𝓝 0):=by simpa using S.continuous.tendsto 0
          filter_upwards [hv.eventually (hf.eventually (by simp))] with i ht; rw[fderiv_comp i (ht.differentiableAt (by simp)) S.differentiableAt, S.fderiv]; rfl
     have hd: DifferentiableAt ℝ T (S 0):=by rw [map_zero]; exact (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by decide)
     change _= fderiv ℝ T 0 _ _; rw[he.fderiv_eq,fderiv_comp 0 M.differentiableAt (hd.comp _ S.differentiableAt),fderiv_comp 0 hd S.differentiableAt,S.fderiv,M.fderiv,map_zero]; rfl
lemma cosmos (h:∀ᶠ V in 𝓝 (1:Grid c),IsUnit (P V))(ht:march x P=P)(hG:Chart k R 1)(hk: 2 ≤ k)(u v:Cray c) : trade (foil P (march x F)) g u v= trade R g (floats x u) (floats x v):=by
     let X:= march x R; let Z:= foil P (march x F); have hp: shrub Z ∘ kiln g=ᶠ[𝓝 0] shrub X ∘ kiln g:= ((course x P F h ht).comp_tendsto (soonK g)).fun_comp oneT
     rw [← voiceP g x R u v hG hk]; change crown _ u v=crown _ u v; unfold crown; rw [hp.fderiv.fderiv_eq] -- hp.fderiv? needs explicit
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.cosmos
#print axioms YM.Massive.Patria.Gall.treated

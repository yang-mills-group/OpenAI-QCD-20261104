import YM.Elms.Pinned
/-! # Equation cylinders and skirts at all sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker InnerProductSpace
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
local notation "M" => Mat
local notation "N" => Lat.Fields n 6
local notation "K" g:arg=>landsE n o g
local notation "T" g:arg=>stripe n o g U
local notation "Tr" g:arg=> haloW n o g U
noncomputable abbrev thunk (P:Regulator n 6)(e: Point)(o:Cover):Edge (Site n):=(landsE n o e.w,e.e.2)
lemma thunkC : thunk P e o= placeEdge (wrap n o) e.e:=by unfold thunk landsE placeEdge capEdge; rw [e.lands,map_add]
-- analytic compare exact derivative.Cannon.Palette wealth.
noncomputable def quest (n:Side)(o:Cover)(e:Point) (A:su.Color): Insertion n 6:=⟨fun V=> dualSp o e.w e.e.2 A V,by
    have hf (f g:Walk)(M₀:ΔM) : Continuous (fun V:Grid n=> bill o f g M₀ V):=by
       unfold bill; refine continuous_finsetSum _ (fun i _=> continuous_finsetSum _ (fun j _=>?_)); exact Continuous.const_smul ((cane n false o g j).continuous.mul (cane n true o f i).continuous) (M₀ i j)
    exact (hf _ _ _).neg.sub (hf _ _ _)⟩
noncomputable def purely (n: Side) (o:Cover)(e:Point)(A:su.Color):Insertion n 6:=⟨fun V:Grid n=> (inner ℝ A (force (expandAt (wrap n o) V) e.w e.e):ℂ) • (1: Lat.Fields n 6),by
    exact Continuous.smul (Complex.continuous_ofReal.comp (Continuous.inner (continuous_const (y:=A)) (Push.Mark.onStencil (wrap n o) (Push.Mark.continuous_force (G:=su) e.w e.e)))) (continuous_const (y:=(1:Lat.Fields n 6)))⟩
noncomputable def button (e:Point)(A:su.Color): Insertion n 6:=purely n o e A - ((P.β:ℂ)⁻¹) • quest n o e A
variable (A:su.Color)
lemma coupling : purely n o e A U=(↑(inner ℝ (su.adjoint (haloW n o e.w U)⁻¹ A) (Push.Mark.field U (thunk P e o))):ℂ) • (1:N):=by
    rw [thunkC]; change (inner ℝ A (su.adjoint _ _) :ℂ) • (1:N)=_; rw [Push.Mark.field_place,Push.Mark.twist_inner]; rfl -- haloW
lemma quake (h:P.t=0): quest n o e A U= ΔZ U P (thunk P e o) (su.adjoint (haloW n o e.w U)⁻¹ A):=Δ_reads U P o e.w e.e.2 A h
noncomputable def fingerprint (A:su.Color)(e:Edge (Site n)):N:= P.density U * ΔZ U P e A - ((↑(P.β*inner ℝ A (Push.Mark.field U e))):ℂ) • P.density U
lemma phantom (h:P.t=0)(hf:P.β ≠0): P.density U * button P o e A U = -(P.β:ℂ)⁻¹ • fingerprint U P (su.adjoint (haloW n o e.w U)⁻¹ A) (thunk P e o):=by
    unfold button; simp only [ContinuousMap.sub_apply,ContinuousMap.smul_apply]; rw [coupling U P, quake U P o e A h]; simp only [mul_sub,_root_.mul_smul_comm, mul_one,fingerprint]; rw [smul_sub,smul_smul, Complex.ofReal_mul, neg_mul,← mul_assoc (P.β:ℂ)⁻¹, inv_mul_cancel₀ (by exact_mod_cast hf),one_mul,neg_smul,neg_smul]; abel
-- linear gradient even carrier.True exact representation variation. Grants incoming motion.
noncomputable def tstep (e:Edge (Site n)): su.Color→L[ℝ]Mat:= ((LinearMap.mulRight ℝ (thread P.t U e.2 e.1)).comp (show su.Color→ₗ[ℝ] Mat from su.colorMat)).toContinuousLinearMap -- types su Mat coercion issue
lemma footprint (e:Edge (Site n)): ∃ F:su.Color→ₗ[ℝ] Lat.Fields n 6,(⇑F)= (fun A=>fingerprint U P A e):=by
    obtain ⟨L,hL⟩:=spansL e.1 (e.1+step e.2) e.2
    let p:= Push.Mark.field U e; let x:= P.density U; let S:su.Color→L[ℝ]Mat:= tstep U P e; let Q:= (LinearMap.mulLeft ℝ x) ∘ₗ (L.comp S).toLinearMap
    let f:=innerSL ℝ p; let W:su.Color→L[ℝ]N:= (P.β • f).smulRight x; refine ⟨Q - W.toLinearMap, funext ?_⟩; intro k; change x*L (pathDeriv U P e k) - ((P.β*inner ℝ p k):ℝ) • x=_; rw [hL, real_inner_comm]; rfl
lemma continuityQ (e:Edge (Site n)): Continuous (fun U'=>fingerprint U' P A e):=by
    have h:=Push.Mark.continuous_field su e; have hf:Continuous (fun V:Grid n=> pathDeriv V P e A):=by unfold pathDeriv thread; fun_prop
    unfold fingerprint ΔZ; fun_prop
lemma continuousPhi {X:Type*}[TopologicalSpace X](g:X→su.Color)(i:su.ColorIndex)(h:Continuous g): Continuous (fun x=>(g x) i):= (PiLp.continuous_apply ..).comp h
-- under travel always gauge independent bound predicate conditional.Declare disjoint via geometry earlier.
def Steady (o: Cover)(w:Point)(n:Side) := ∀ U:Grid n,∀ A:su.Color,∀ t:ℝ, haloW n o w.w (turnLink (placeEdge (wrap n o) w.e) A t U)=haloW n o w.w U
def Misses (e:Point)(o:Cover)(x:Insertion n 6) : Prop:= ∀ U:Grid n,∀ A:su.Color,∀ t:ℝ, x (turnLink (placeEdge (wrap n o) e.e) A t U)=x U
lemma compound (f:Edge (Site n))(G:Grid n→su.Color)(Y:Insertion n 6)(hg:Continuous G)(gX:∀ U:Grid n,∀ A t, G (turnLink f A t U)=G U)(hy:∀ U:Grid n,∀ A t, Y (turnLink f A t U)=Y U)(hn:2≤n.val) : (∫ U:Grid n,(ber _) (fingerprint U P (G U) f *Y U) ∂prior su n)=0:=by
    let E:= EuclideanSpace.basisFun su.ColorIndex ℝ
    let Y'(i:su.ColorIndex): Insertion n 6:= ⟨fun U=> (↑(G U i):ℂ) • Y U,by exact Continuous.smul (Complex.continuous_ofReal.comp (continuousPhi G i hg)) Y.continuous⟩
    have hz (U): fingerprint U P (G U) f*Y U=∑ i:su.ColorIndex,fingerprint U P (E i) f*Y' i U:=by
       obtain ⟨L,hL⟩:=footprint U P f; have hs(x):fingerprint U P x f=L x:=(congr_fun hL x).symm;  simp_rw [hs]; conv_lhs=> rw [← (show ∑ i, G U i • E i=G U from E.sum_repr _), map_sum,sum_mul]
       apply sum_congr rfl; intro i _; rw [map_smul,_root_.smul_mul_assoc,show Y' i U=(↑(G U i):ℂ) • Y U from rfl, _root_.mul_smul_comm]; rfl
    have hd(i:su.ColorIndex): Continuous (fun U=> ber _ (fingerprint U P (E i) f * Y' i U)):= continuous_ber.comp ((continuityQ P _ _).mul (Y' i).continuous)
    simp_rw [hz,map_sum]; rw [integral_finsetSum _ (fun i _=> (hd i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),sum_eq_zero]
    intro i _; refine exactZ P f (E i) (Y' i) ?_ hn; intro U t
    change (↑(G (turnLink _ _ _ U) i):ℂ) • Y _= (↑(G U i):ℂ) • Y _; rw [hy,gX] -- apply args
lemma led (f:Edge (Site n))(G:Grid n→su.Color)(Y X:Insertion n 6)(hg:Continuous G)(gX:∀ U:Grid n,∀ A t, G (turnLink f A t U)=G U)(hy:∀ U:Grid n,∀ A t,Y (turnLink f A t U)=Y U)(hn:2≤n.val)(c:ℂ)(hc:∀ U,P.density U*X U=c • fingerprint U P (G U) f): P.average (X*Y)=0:=by
   suffices hv:P.raw (X*Y)=0 by simp [Regulator.average,hv]
   change (∫ U:Grid n,(ber (Modes n 6)) (P.density U*(X U*Y U)) ∂prior su n)=0
   simp_rw [← mul_assoc,hc,_root_.smul_mul_assoc,map_smul]; rw [integral_smul,compound P f G Y hg gX hy hn,smul_zero]
private lemma streetsG (A:su.Color): Continuous (fun U:Grid n=>su.adjoint (haloW n o e.w U)⁻¹ A):=by
     let g:=fun U:Grid n=> ((haloW n o e.w U)⁻¹,A); have hg:Continuous g:= (halo_cont n o e.w).inv.prodMk continuous_const; have h:= Continuous.comp (Push.Mark.continuous_ad su) hg; apply h
lemma exact_silent (h:P.t=0)(hf:P.β≠0)(Y:Insertion n 6)(hV:Steady o e n)(hy:Misses e o Y)(hn:2≤ n.val): P.average (button P o e A*Y)=0:=by
   have hg(U:Grid n)(A':su.Color)(t:ℝ):(su.adjoint (haloW n o e.w (turnLink (thunk P e o) A' t U))⁻¹ A)=su.adjoint (haloW n o e.w U)⁻¹ A:=by rw [thunkC,hV U A' t]
   have hx:∀ U:Grid n,∀ A t, Y (turnLink (thunk P e o) A t U)=Y U:=by rw [thunkC]; exact hy
   exact led P (thunk P e o) _ Y _ (streetsG o e A) hg hx hn _ (fun U=>phantom U P o e A h hf)
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.exact_silent

import YM.QCD.Fount.Read
/-! # local fiscal from atmosphere. sign of pressure -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR
variable {i b j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a A B w ν α s L y u' :ℝ} {M:ParcelR}
variable (P:Plan j) (V : Back E K j j p u v) {X Y: SunR M} (Q:Avenue V η Ω Θ)
-- permit price read at healthy. station graph μ. scalar constant explicitly carried, important for funds liquid.
set_option quotPrecheck false
local notation "ds" =>divides0 V.fly V.chain i
local notation "K₀"=>park V.fly (divides0 V.fly V.chain i) P X.X X.Y t 0
local notation "Γ"=>fun z:Cnr (V.chain.n i)=> (encamp (V.port.forest i) (V.port.u i) z).1
variable (hR:Rates M s)(hp:Species V.fly (divides0 V.fly V.chain i) w ν r 0 a b (park V.fly (divides0 V.fly V.chain i) P X.X X.Y t 0))(hr:0<r)(ht:0<t)(hx:t≤1)
lemma tannin {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D]{n:Side}{F G:D→Sheet n}(h:Duet F G)(hp:IsUnit (F 0).det):Duet (presG F) (presG G) :=by
    let Q (i:Sheet n):= i-F 0; let U (x:Sheet n):= F 0+x
    have he: ContDiffAt ℝ ω (presG U) (Q (F 0)):=by
       rw [show Q (F 0)=0 from sub_self _]; exact (Raft.tollsP _ (contDiffAt_const.add contDiffAt_id) (show IsUnit (U 0).det by unfold U; rw [add_zero]; exact hp)).1
    let S:= presG U ∘ Q
    have hz:S=(fun i:Sheet n=> -Real.log ‖i.det‖):=funext fun i=>by simp [S,U,Q,presG]
    have hp':= duchy S h (he.comp (f:=Q) _ (by unfold Q; fun_prop)); rw [hz] at hp'; exact hp'
abbrev kroner (T:On)(f:Side)(U:Grid f):ℝ:=Real.log ((T f U).det.re)
-- wee panel
local notation "Υ"=> fun y=> -Real.log ((K₀ ((Γ) y)).det.re)
include hr ht hp hR hx Q
lemma dims : Duet (Υ) (purchaseG V P X.powerG i):=by
    obtain ⟨W,hW,hH,hV,hx'⟩:=Raft.lecture V i Q
    have hz:= duct W (hardened P V hR hp hr ht hx) hH hW
    have hh:= tannin hz (show IsUnit (K₀ _).det from hp.sole _)
    refine ((Duet.together hh.leftF (Q:=Υ) ?_).flip.chain hh).chain (Duet.together hh.rightF ?_)
    · filter_upwards [hV] with y hy; change -Real.log ‖(K₀ _).det‖= -Real.log _; rw [hy]; congr 2 -- risk
      let D:= K₀ ((Stationary.input su _ ∘ W) y)
      change ‖D.det‖= D.det.re
      conv_lhs=> rw [← Cost.determinant_real chi_sq (hp.crease _),Complex.norm_real,Real.norm_of_nonneg (hp.full _).le]
    exact hV.symm.mono fun z hz=> congr_arg (fun q=>-Real.log ‖(shiftH V.fly ds P (X.powerG _) q).det‖) hz
-- subtract scalar. transfer avoids Euclid Op issue. Hart
local notation "Ζ" => (Υ)+litG V X.Z.page i
lemma franc {d' e':ℝ}(he:BirthR M P V Q X Y α)(R:PathData su)(h:R.Bounds p u v u')(hd:Attached Q.D' R)(hy:Precision.Floor Q.D' p (V.chain.n i) d' e') :
   let E:=(Ζ) - (α • inputSeries p R + Voyage.barG Y.Z.page (V.chain.n i))
   ContDiffAt ℝ ω E 0 ∧ fderiv ℝ E 0=0 ∧ ∀ x, ‖iteratedFDeriv ℝ 2 E 0 ![x,x]‖ ≤ (Fintype.card (Site (V.chain.n i)):ℝ)*(M.l*Real.exp (-M.w*(localG V i).val))*‖x‖^2 :=by
    intro S; have ht :=dims P V Q hR hp hr ht hx; let E:= litG V X.Z.page i; have hf:=(he.price i); dsimp only at hf
    have he:ContDiffAt ℝ ω E 0:=by rw [show E=purchaseG V P X.powerG i+ E-purchaseG V P X.powerG i from (add_sub_cancel_left ..).symm]; exact hf.1.sub ht.rightF
    have hp':= ht.add (Duet.together he EventuallyEq.rfl)
    let R':=inputSeries p R (m:=V.chain.n i); have hh := low_columns h hd hy (Q.Sw i); have hi := zen (Y.Z.cost hR.ht) hR.ht (V.chain.n i)
    have hz:ContDiffAt ℝ ω (α • R') 0:= (stain_knit (m:=V.chain.n i) R p h).analytic.contDiffAt.const_smul α
    have ht:= zen (X.Z.cost hR.ht) hR.ht (V.chain.n i)
    refine ⟨hp'.leftF.sub (hz.add hi),?_,fun x=>?_⟩
    · have hP : fderiv ℝ (Υ+E) 0=0:= ContinuousLinearMap.ext fun i=> (hp'.paint i).trans (hf.2.1 i)
      let F:=barG Y.Z.page (V.chain.n i); have hF : fderiv ℝ F 0=0:= ContinuousLinearMap.ext fun i=> (crust Y.Z hR.ht i).1
      let L:=α • R'; have hv:S=(Υ+E)-(L+F):=rfl
      have hZ: HasFDerivAt (𝕜:=ℝ) L 0 0:=by
        have hf := ((stain_knit R p h (m:=V.chain.n i)).analytic.contDiffAt (n:=ω) |>.differentiableAt (by simp)).hasFDerivAt.const_smul α; rw [hh.2.1,smul_zero] at hf; exact hf
      have hf:HasFDerivAt (𝕜:=ℝ) F 0 0:= by rw [← hF]; exact (hi.differentiableAt (by simp)).hasFDerivAt
      have hg:=((hp'.leftF.differentiableAt (by simp)).hasFDerivAt.sub (hZ.add hf))
      rw [hP,zero_add,sub_zero] at hg; rw [hv]; exact hg.fderiv
    rw [show iteratedFDeriv ℝ 2 S 0=_ from iteratedFDeriv_sub_apply (hp'.leftF.of_le le_top) ((hz.add hi).of_le le_top),_root_.sub_apply, ← iter _ _ hp'.leftF,hp'.rep, show iteratedFDeriv ℝ 2 (α • R'+barG _ _) 0= _ from iteratedFDeriv_add_apply (hz.of_le le_top) (hi.of_le le_top), _root_.add_apply, ← iter _ _ hi]
    let L:=α • ContinuousLinearMap.id ℝ ℝ; have h:(α • R')=L ∘ R':=rfl
    have hl: ContDiffAt ℝ ω R' 0:= (stain_knit R p ‹R.Bounds p u v u'›).analytic.contDiffAt
    rw [← iter _ _ hz,h,retold _ _ L hl,iter _ _ hl, show iteratedFDeriv ℝ 2 R' 0 _ = _ from hh.2.2 x x]; exact hf.2.2 x
end YM.QCD.Fount

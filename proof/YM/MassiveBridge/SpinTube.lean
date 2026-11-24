import YM.MassiveBridge.Algebraic
import YM.Next.MAXWELL.ComplexInk
import YM.MassiveTwoEstimates.SpinGeometry

/-!
# Filling paths on spin tuples for spatial symmetries and boosts

Use actual gamma conventions and explicit rapidity lifts. Use entire
identity with holomorphic matrices, along complex paths of each generator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Spinor
open QCD QCD.Lat
open Set Function Filter Mink Complex
open MassiveTwoEstimates (SpinGeometry.geometry)
open MassiveTwoEstimates.BoostMotion (point)
open MassiveTwoEstimates
open Maxwell.Free (stencil stencil_cont stencil_mul follows paints lamp stroll night writes_axes photos)
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

lemma from_real_parameter {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {F G : ℂ → V} (h : Differentiable ℂ F) (g : Differentiable ℂ G)
    (hg : ∀ x : ℝ, F x=G x) : F=G := by
  apply ((h.differentiableOn (s:=univ)).analyticOnNhd isOpen_univ).eq_of_frequently_eq ((g.differentiableOn (s:=univ)).analyticOnNhd isOpen_univ) (z₀:=0)
  have H : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x:=0)).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
    filter_upwards [self_mem_nhdsWithin] with y hy; exact fun ht : (y:ℂ) = 0 => hy (by exact_mod_cast ht)
  by_contra! w
  obtain ⟨i,hi⟩ := (H.eventually w).exists; exact hi (hg _)

lemma from_imag_parameter {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {F G : ℂ → V} (h : Differentiable ℂ F) (g : Differentiable ℂ G)
    (hg : ∀ x : ℝ, F ((x:ℂ)*I) = G ((x:ℂ)*I)) : F=G := by
  let p : ℂ → ℂ := fun z => z*I
  have hp : Differentiable ℂ p := differentiable_id.mul_const _
  have he := from_real_parameter (h.comp hp) (g.comp hp) hg
  funext z
  have hh : p (z*(-I)) = z := by simp [p, mul_assoc]
  simpa only [Function.comp_apply,hh] using congr_fun he (z*(-I))

local notation "timev" => timeAxis
def wire (p : RealSpin) : ArrayS := (stencil p.coord, p.matrix.val,p.matrix⁻¹.val)
def track (X Y : ArrayS) : ArrayS := (Maxwell.Free.follow X.1 Y.1,X.2.1*Y.2.1,Y.2.2*X.2.2)
lemma links (p q : EuPin) : track (printS p) (printS q)=printS (p*q) := by
   apply Prod.ext (follows p.coord q.coord)
   change (_,q.matrix⁻¹.val*p.matrix⁻¹.val)=(p.matrix.val*q.matrix.val,(p.matrix*q.matrix)⁻¹.val); rw [mul_inv_rev]; rfl
lemma wires (p q : RealSpin) : track (wire p) (wire q)=wire (p*q) := by
   apply Prod.ext (stencil_mul p.coord q.coord).symm
   change (_,q.matrix⁻¹.val*p.matrix⁻¹.val)=(p.matrix.val*q.matrix.val,(p.matrix*q.matrix)⁻¹.val); rw [mul_inv_rev]; rfl
lemma wire_c : Continuous wire := by
   have h : Continuous (fun p:RealSpin=> p.matrix) := continuous_snd.comp continuous_subtype_val
   exact (stencil_cont.comp (continuous_fst.comp continuous_subtype_val)).prodMk
     ((Units.continuous_val.comp h).prodMk (Units.continuous_val.comp (continuous_inv.comp h)))
lemma track_left (A:ArrayS) : Differentiable ℂ (fun B:ArrayS=> track A B) := by
   have he := (Maxwell.Free.follow_left A.1).differentiable (by simp); unfold track; fun_prop (disch:=assumption)
lemma track_right (B:ArrayS) : Differentiable ℂ (fun A:ArrayS=> track A B) := by
   have he := (Maxwell.Free.follow_right B.1).differentiable (by simp); unfold track; fun_prop (disch:=assumption)

namespace Lift
open MassiveTwoEstimates.BoostRotor
variable (e : Ray)
def spinPart (z : ℂ) := binomial e (Complex.cosh (z/2)) (Complex.sinh (z/2))
lemma spin_real (r : ℝ) : spinPart e r=(point e r).matrix.val := by
   change binomial _ _ _=mat _ _; rw [mat, Complex.ofReal_cosh,Complex.ofReal_sinh]; push_cast; rfl
lemma spin_diff : Differentiable ℂ (spinPart e) := by unfold spinPart binomial; fun_prop
-- arbitrary real boost curve entire (for fullness beyond generators)
def matrixPart (z : ℂ) : Ink := fun a b => lamp a * ((basis b a:ℂ)+Complex.sinh z*(e.crossT (basis b) a:ℂ)+(Complex.cosh z-1)*(e.scalesT (basis b) a:ℂ))*(lamp b)⁻¹
lemma matrix_real (r:ℝ) : matrixPart e r=stencil (e.boost r):=by
   funext a b; unfold matrixPart stencil; rw [Ray.boost_at]; unfold Ray.shift; simp
lemma matrix_diff : Differentiable ℂ (matrixPart e):=by unfold matrixPart; fun_prop

def drum (z:ℂ) : ArrayS := (matrixPart e z, spinPart e z, spinPart e (-z))
lemma drum_real (r:ℝ) : drum e r=wire (point e r):=by
   unfold drum wire; rw [matrix_real,spin_real, ← ofReal_neg, spin_real]; rfl
lemma drum_diff : Differentiable ℂ (drum e) := (matrix_diff e).prodMk ((spin_diff e).prodMk ((spin_diff e).comp differentiable_neg)) -- id neg

variable (i:SpaceAxis)
omit e
local notation "J" => Ray.fromAxis i
local notation "Q" => Ortho.oneParameter (Ortho.plane timev i.castSucc)
lemma matrix_imag (r:ℝ) : matrixPart J ((r:ℂ)*I)= paints (Q r) := by
   let f (z:ℂ) := stroll i (z*(-I))
   have hh := from_real_parameter (matrix_diff J)
     (((Maxwell.Free.stroll_diff i).differentiable (by simp)).comp (show Differentiable ℂ (fun z:ℂ=>z*(-I)) from by fun_prop))
     (show ∀ x:ℝ,matrixPart J x=f (x:ℂ) from fun x=>(matrix_real J x).trans (night i x))
   rw [hh,Function.comp_apply,writes_axes]; congr 1; simp [mul_assoc]

private lemma transpose_diff {A : ℂ → Spike} (h : Differentiable ℂ A) : Differentiable ℂ (fun z=> (A z).transpose) :=
   (show Differentiable ℂ (⇑(LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv Pinor Pinor ℂ ℂ).toLinearMap) ∘ A) from (LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv Pinor Pinor ℂ ℂ).toLinearMap).differentiable.comp h)
lemma spin_inv (e:Ray) (z:ℂ) : spinPart e z * spinPart e (-z)=1 := congr_fun (from_real_parameter
   (show Differentiable ℂ (fun z:ℂ=>spinPart e z * spinPart e (-z)) from (spin_diff _).mul ((spin_diff e).comp differentiable_neg)) (differentiable_const (1:Spike)) (fun r=>by rw [spin_real,← ofReal_neg,spin_real]; exact matInv e r)) z
lemma spin_charge (e:Ray) (z:ℂ): spinPart e z*chargeMatrix*(spinPart e z).transpose=chargeMatrix:=
   congr_fun (from_real_parameter (((spin_diff e).mul_const _).mul (transpose_diff (spin_diff e))) (differentiable_const _)
     (show ∀ r:ℝ,(fun z:ℂ=>spinPart e z*chargeMatrix*(spinPart e z).transpose) (r:ℂ)=chargeMatrix from fun r=>by
       dsimp only; rw [spin_real]; exact preserves e r)) z

-- flatten wick slash into its four columns
lemma wickAxis (x:E4): wickSlash x=∑ a:Axis,(lamp a*(x a:ℂ)) • gamma a:=by
   rw [Fin.sum_univ_castSucc,wickSlash]; congr 1; apply Finset.sum_congr rfl; intro a _; simp [lamp]
lemma axis_slash (e:Ray) (r:ℝ)(b:Axis): spinPart e r* gamma b =
    (∑ a:Axis,matrixPart e r a b • gamma a)*spinPart e r:=by
   let C:=lamp b
   have h : C≠0:= Maxwell.Free.lamp_nz b
   apply smul_right_injective Spike h
   dsimp only; rw [matrix_real,spin_real,← Matrix.mul_smul]
   rw [show C • ((∑ a:Axis, stencil (e.boost r) a b • gamma a)*(point e r).matrix.val)=(C • ∑ a:Axis,stencil (e.boost r) a b • gamma a)*(point e r).matrix.val from (Matrix.smul_mul ..).symm]
   let p:=point e r
   have hp:= ((realSpin_iff p.val).1 p.property).2 (basis b)
   have hf : wickSlash (basis b) = lamp b • gamma b:=by
     rw [wickAxis,Finset.sum_eq_single b]
     · simp
     · intro i _ h; simp [h]
     simp
   have hg : lamp b • ∑ a:Axis, stencil (e.boost r) a b • gamma a = wickSlash (p.coord.act (basis b)):=by
     rw [wickAxis,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _
     rw [smul_smul,stencil,mul_comm (lamp b),mul_assoc (lamp a * _),inv_mul_cancel₀ h,mul_one]; rfl
   rw [←hf,hg]; exact hp
lemma axis_slash_all (e:Ray) (z:ℂ) (b:Axis): spinPart e z * gamma b =
    (∑ a:Axis,matrixPart e z a b • gamma a)*spinPart e z:= by
   have h : Differentiable ℂ fun z=>∑ a:Axis,matrixPart e z a b • gamma a:=by unfold matrixPart; fun_prop
   exact congr_fun (from_real_parameter ((spin_diff e).mul_const (gamma b)) (h.mul (spin_diff _)) (fun r => axis_slash e r b)) z

lemma spinImag (r:ℝ)(x:E4): spinPart J ((r:ℂ)*I)*slash x=slash ((Q r).move x)*spinPart J ((r:ℂ)*I):=by
   let Z:= (r:ℂ)*I; let g:=Q r; let P:=spinPart J Z
   change P * _=_ * P
   unfold slash; simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,Matrix.smul_mul]
   have h (b): P*gamma b = (∑ a:Axis,(g.val a b:ℂ) • gamma a) * P:=by simpa only [P,Z,matrix_imag,g,paints] using axis_slash_all J Z b
   simp_rw [h, Finset.sum_mul, Matrix.smul_mul, Finset.smul_sum,smul_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
   rw [← Finset.sum_smul]; unfold Ortho.move; rw [M4.at_coord,Complex.ofReal_sum]; apply congrArg (· • _); apply Finset.sum_congr rfl; intro b _; simp [g, mul_comm]

def pspin (r:ℝ) : Spikeˣ := ⟨spinPart J ((r:ℂ)*I), spinPart J (-((r:ℂ)*I)),spin_inv ..,by simpa only [neg_neg] using spin_inv J (-((r:ℂ)*I))⟩
def daylight (r:ℝ) : EuPin:=⟨(Q r,pspin i r),(euPin_iff _).mpr ⟨spin_charge ..,spinImag i r⟩⟩
lemma drum_day (r:ℝ): drum J ((r:ℂ)*I)=printS (daylight i r):=by unfold drum; rw [matrix_imag]; rfl
lemma way : EuPin.Path (Ortho.plane timev i.castSucc) (daylight i):=by
  have ha : Continuous (fun r:ℝ=> spinPart J ((r:ℂ)*I)) := (spin_diff J).continuous.comp (continuous_ofReal.mul continuous_const)
  have hb : Continuous (pspin i) := Units.continuous_iff.mpr ⟨ha,(spin_diff J).continuous.comp ((continuous_ofReal.mul continuous_const).neg)⟩
  have hc : Continuous Q := by unfold Ortho.oneParameter; fun_prop
  refine ⟨Subtype.ext ?_,(hc.prodMk hb).subtype_mk _,fun _=>rfl⟩
  apply Prod.ext
  · apply Subtype.ext; simp [daylight,Ortho.oneParameter]
  apply Units.ext; change spinPart _ _=1; simp [spinPart,binomial]

lemma over_spin (r:ℝ): (daylight i r).IsRotation:=by
  -- determinant of every orthogonal path from 1 is +1
  let A : Ortho.Skew:= Ortho.plane timev i.castSucc
  let f:=fun r:ℝ=> Q r
  change LinearMap.det (Matrix.toEuclideanLin (f r).val)=1
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]
  have hp:f r=f (r/2)*f (r/2):= by
     rw [show f (r/2)*f (r/2)=f (r/2+r/2) from (SpinPlane.addParameter ..).symm,add_halves]
  rw [hp]
  let g := f (r/2)
  change (g.val*g.val).det=1
  rw [Matrix.det_mul]; nth_rw 1 [← Matrix.det_transpose]; rw [← Matrix.det_mul,g.transp,Matrix.det_one]
lemma begins (e : Ray) : point e 0=1:=by
   apply Subtype.ext; apply Prod.ext
   · exact e.boost_start
   apply Units.ext; change mat e 0=1; simp [mat,binomial]
lemma path : RealSpin.Path i (point J):= ⟨begins _,BoostMotion.continuousPoint _,fun _=>rfl⟩
lemma kernelFinite : (LorentzTopology.projection.ker : Set RealSpin).Finite := by
  obtain ⟨q,hq,hqspin⟩ := SpinGeometry.geometry.minkBoth (1:RealSpin)
  refine (Set.finite_singleton q).insert (1:RealSpin) |>.subset ?_
  intro p hp
  have coord : p.coord=(1:RealSpin).coord := hp
  rcases SpinGeometry.geometry.minkFiber p 1 coord with rfl|hminus
  · exact Set.mem_insert _ _
  have eq : p=q:=Subtype.ext (Prod.ext (coord.trans hq) (hminus.trans hqspin.symm)); exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr eq)
lemma covering : IsCoveringMap RealSpin.coord :=by
  have hc : Continuous LorentzTopology.projection := continuous_fst.comp continuous_subtype_val
  have hg : Topology.IsQuotientMap LorentzTopology.projection := SpinGeometry.geometry.realOpen.isQuotientMap hc SpinGeometry.geometry.realTime
  exact (hg.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom kernelFinite.isDiscrete).isCoveringMap
lemma point_mul (e:Ray) (a b:ℝ) : point e a * point e b = point e (a+b) :=by
   have he : (fun b:ℝ=>point e a * point e b)=fun b=>point e (a+b) :=
     covering.eq_of_comp_eq (continuous_const.mul (BoostMotion.continuousPoint _)) ((BoostMotion.continuousPoint e).comp (continuous_const.add continuous_id))
       (funext (fun r=> (e.boost_add a r).symm)) (0:ℝ) (by simp [begins])
   exact congr_fun he b
lemma point_neg (e:Ray)(a:ℝ) : (point e a)⁻¹=point e (-a) := inv_eq_of_mul_eq_one_right (by rw [point_mul,add_neg_cancel,begins])
lemma prescribed (p:ℝ→RealSpin) (hp:RealSpin.Path i p): p=point J := covering.eq_of_comp_eq hp.2.1 (path i).2.1 (funext (hp.2.2)) 0 (hp.1.trans (begins _).symm)
end Lift

-- don't quotient out the second lift!
def spatialP (p : RealSpin) := ∃ (U : EuPin) (h:Lorentz.spatialTurn U.coord), Lorentz.room U.coord h=p.coord ∧ U.matrix=p.matrix
lemma hold_of_fixed (p:RealSpin)(h:p.coord.act (basis timev)=basis timev): spatialP p := by
   obtain ⟨s,hs,H⟩:=Work.A16.exists_room_of_fix _ h
   obtain ⟨q,hq⟩:= SpinGeometry.geometry.euclidean s; subst s
   obtain ⟨u,hu,hV⟩:= SpinGeometry.geometry.spatial q hs
   rcases SpinGeometry.geometry.minkFiber p u (H.symm.trans hu.symm) with he|hv
   · subst p; exact ⟨q,hs,H,hV.symm⟩
   obtain ⟨q',hq',ht⟩:= SpinGeometry.geometry.euBoth q; refine ⟨q',hq' ▸ hs,?_,ht.trans (by rw [hv,hV])⟩
   -- dependent K
   exact Eq.trans (by congr 1; exact hq'.symm : Lorentz.room _ _ = Lorentz.room q.coord hs) H
lemma spatialP_fixed {p:RealSpin}(h:spatialP p): p.coord.act (basis timev) = basis timev:=by
   obtain ⟨q,h,H,_⟩:=h; rw [← H]; exact Maxwell.Free.spatial_axis _ h
lemma spatialP_print {q:RealSpin} {p:EuPin} {h:Lorentz.spatialTurn p.coord} (hp:Lorentz.room p.coord h=q.coord)(he:p.matrix=q.matrix): wire q=printS p :=by
   unfold wire; rw [←hp,←he,photos]; rfl
abbrev groupR := Subgroup.closure ({p:RealSpin|spatialP p} ∪ {p|∃ i:SpaceAxis,∃ r, p=point (Ray.fromAxis i) r})
lemma reaches (q:RealSpin) : q∈groupR:=by
   let f:= LorentzTopology.projection
   have hg : Bid.beamGens ≤ groupR.map f:=by
      apply (Subgroup.closure_le _).mpr; rintro p (hp|hp)
      · rcases hp with ⟨r,hr,rfl⟩; obtain ⟨q,hq⟩:=SpinGeometry.geometry.realTime (Lorentz.room r hr); refine ⟨q,Subgroup.subset_closure (Or.inl (hold_of_fixed q ?_)),hq⟩
        rw [hq]; exact Maxwell.Free.spatial_axis r hr
      rcases hp with ⟨i,t,rfl⟩; exact ⟨point (Ray.fromAxis i) t,Subgroup.subset_closure (Or.inr ⟨i,t,rfl⟩),rfl⟩
   obtain ⟨p,hp,h⟩:= hg (show f q∈Bid.beamGens by rw [show Bid.beamGens=⊤ from Work.A16.answer]; trivial)
   have he : spatialP (p⁻¹*q):= hold_of_fixed (p⁻¹*q) (by
     have hr : RealSpin.coord (p⁻¹*q)=1:= show f (p⁻¹*q)=1 by rw [map_mul,map_inv,h,inv_mul_cancel]
     simp only [hr,Lorentz.act_one])
   rw [← mul_inv_cancel_left p q]; exact Subgroup.mul_mem groupR hp (Subgroup.subset_closure (Or.inl he))

-- entire identities (following `Casting` in Next/MAXWELL)
section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
def lands (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] (x:ArrayS) := ∀ f g:ArrayS→V, Differentiable ℂ f → Differentiable ℂ g → (∀ p:EuPin,f (printS p)=g (printS p)) → f x = g x
omit [CompleteSpace V] in
lemma lands_mul {a b : ArrayS}(ha:lands V a)(hb:lands V b): lands V (track a b):=by
   intro p q hp hq h
   have he (s : EuPin) : p (track a (printS s))= q (track a (printS s)):=
     ha (fun a=> p (track a (printS s))) (fun a=> q (track a (printS s))) (hp.comp (track_right _)) (hq.comp (track_right _)) (fun t => by rw [links,h _])
   exact hb _ _ (hp.comp (track_left a)) (hq.comp (track_left a)) he
lemma boost_auth (a:SpaceAxis) (t:ℝ): lands V (wire (point (Ray.fromAxis a) t)):=by
   intro p q hp hq h; rw [← Lift.drum_real]
   have hd:= Lift.drum_diff (Ray.fromAxis a); exact congr_fun (from_imag_parameter (hp.comp hd) (hq.comp hd) (fun x=>by simp only [Function.comp_apply,Lift.drum_day,h _])) (t:ℂ)
lemma genuine (p : RealSpin) : lands V (wire p) := by
   have hp := reaches p
   have hs {p:RealSpin}(h:spatialP p) : lands V (wire p):=by
       obtain ⟨q,h,H,hq⟩:= h; rw [spatialP_print H hq]; exact fun _ _ _ _ he=>he q
   suffices h : lands V (wire p) ∧ lands V (wire p⁻¹) from h.1
   induction hp using Subgroup.closure_induction with
   | mem g hg=>
     rcases hg with hg|⟨a,t,rfl⟩
     · refine ⟨hs hg,hs (hold_of_fixed _ ?_)⟩; have hv:= spatialP_fixed hg; change g.coord⁻¹.act _=_; nth_rw 1 [← hv]; exact Lorentz.starts ..
     · rw [Lift.point_neg]; exact ⟨boost_auth _ _,boost_auth _ _⟩
   | one=> rw [inv_one]; have hb:= hs (hold_of_fixed 1 (Lorentz.act_one (basis timev))); exact ⟨hb,hb⟩
   | mul x y hx hy a b=> rw [← wires,mul_inv_rev,← wires]; exact ⟨lands_mul a.1 b.1, lands_mul b.2 a.2⟩
   | inv x h hp=>rw [inv_inv]; exact ⟨hp.2,hp.1⟩
end
end YM.Massive.Bridge.Spinor

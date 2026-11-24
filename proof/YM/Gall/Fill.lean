import YM.Gall.Fellow
import YM.QCD.Rudder.Real
/-! Abelian derivatives agree with left prices WITHOUT periodic assumptions.Ward pure gauge.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole
open Poised Poised.Display Poised.Beacon PCAC Push.Local Rudder
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable {E Y:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y]
abbrev Cray (c:Side):= Edge (Site c)→ℝ
local notation "Y★"=> Cray c
variable (g:su.Color)
noncomputable def ink : Cray c→L[ℝ] Directions su c :=LinearMap.toContinuousLinearMap { toFun:=fun x i=> x i • g,map_add':=fun x y=>funext fun i=> add_smul _ _ _, map_smul':=fun z x=> funext fun i=> mul_smul _ _ _ }
def kiln (x:Cray c):Grid c:= fun i=>Rudder.bird g (x i)
local notation "cv"=> kiln g
local notation "K"=> ink g
@[simp] lemma kiln0 : cv (0:Y★)=1:=funext fun i=> show bird g 0=1 from (by simp[bird])
@[simp] lemma kiln_val (x:Y★) : increment 1 (ink g x)=cv x:=by funext i; unfold increment; rw [Pi.one_apply,mul_one]; rfl
lemma colony (x y:Y★) : cv (x+y)=increment (cv y) (K x):= by
    funext i; change bird g (x i+y i)= bird g (x i)*bird g (y i); rw [bright]
lemma collinear (x:Y★)(F:Grid c→E)(hF:Chart k F (cv x)): ContDiffAt ℝ (k:ℕ∞ω) (F∘cv) x:=by
    let Φ:= (ink (c:=c) g) -- syntax
    let Tp(y:Y★):= Φ (y-x); have hV:Tp x=0:=by simp[Tp]
    have he: F ∘ cv= (F ∘ increment (cv x)) ∘ Tp:= funext fun i=> congr_arg F (show cv i= _ from (by nth_rw 1 [←sub_add_cancel i x]; exact colony g (i-x) x))
    rw [he]; exact (show ContDiffAt ℝ _ _ (Tp x) from hV.symm ▸ hF).comp _ (Φ.contDiff.contDiffAt.comp _ (contDiffAt_id.sub contDiffAt_const)) -- contDiffAt
lemma gently (x y:Y★)(F:Grid c→E)(hF:Chart k F (cv x))(hk:1 ≤ k): fderiv ℝ (F ∘ cv) x y= leftDerivs F [K y] (cv x):=by
    have hg:= collinear g x F hF; let A:= F ∘ cv
    have hv : HasDerivAt (fun t:ℝ=> t • y+x) y 0:=by simpa using ((hasDerivAt_id' (0:ℝ)).smul_const y).add_const x
    have he:= (show HasFDerivAt A (fderiv ℝ A x) ((0:ℝ) • y+x) from (by rw [zero_smul,zero_add]; exact (hg.differentiableAt (by exact_mod_cast (Nat.zero_lt_of_ne_zero (Nat.ne_of_gt hk)).ne')).hasFDerivAt)).comp_hasDerivAt (0:ℝ) hv
    rw [show leftDerivs F [K y] (cv x)=deriv (A∘(fun t:ℝ=>t • y+x)) 0 from (by unfold leftDerivs; rw [show A∘(fun t:ℝ=> t • y+x)=(fun t:ℝ=> F (increment (cv x) (t • K y))) from funext fun t=> congr_arg F (by rw [colony,map_smul])]; rfl)]; exact he.deriv.symm
lemma trailV(x y:Y★)(F:Grid c→E)(hF:Chart k F 1)(hk:2 ≤ k): crown (F ∘ cv) x y=leftDerivs F [K x,K y] 1:=by
    let A:= F∘cv; let L:= ContinuousLinearMap.apply ℝ E y; let T:= leftDerivs F [K y]; have hm:= collinear g 0 F (show Chart k F _ from by rw [kiln0]; exact hF)
    have hd: DifferentiableAt ℝ (fderiv ℝ A) 0:= (hm.fderiv_right (m:=1) (by exact_mod_cast hk)).differentiableAt one_ne_zero
    have he: L ∘ fderiv ℝ A=ᶠ[𝓝 0] T ∘ cv:=by
        have hF:∀ᶠ X in 𝓝 (0:Y★), Chart k F (cv X):=by
            apply chart_eventually (by rw [kiln0]; exact hF); intro i; unfold kiln Rudder.bird; exact (su.exp_jet.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)).contDiffAt
        filter_upwards [hF] with i hi; exact gently g i y F hi (by omega)
    have ht : Chart 1 T (cv (0:Y★)):=by rw [kiln0]; exact Next.Foundations.leftDerivs_chart _ 1 (hF.of_le (by simp only[List.length_cons,List.length_nil]; exact_mod_cast hk))
        -- pay
    change crown A x y=_
    calc crown A x y=fderiv ℝ (L ∘ fderiv ℝ A) 0 x:=by rw [fderiv_comp 0 L.differentiableAt hd,L.fderiv]; rfl
         _= leftDerivs F [K x,K y] 1:= by rw [he.fderiv_eq,gently g 0 x T ht (Nat.le_refl 1),kiln0]; rfl
def glaze (u:Site c→ℝ):Cray c:= fun i=> u (i.1+ step i.2)-u i.1
lemma vapors (x:Y★)(u:Site c→ℝ)(a:ℝ): cv (a • glaze u+x)= Lattice.gauge (fun i=> bird g (-a*u i)) (cv x):=by
    funext i; change bird g (a* (u (i.1+step i.2)-u i.1)+ x i)= bird g (-a*u i.1) * bird g (x i)* (bird g (-a*u (i.1+step i.2)))⁻¹; rw [Rudder.bird_inv,bright,bright]; apply congr_arg; ring
lemma shunt (x:Y★)(F:Grid c→E)(hF:Lattice.GaugeInvariant F)(v: Site c→ℝ)(hf:DifferentiableAt ℝ (F∘cv) x): fderiv ℝ (F∘cv) x (glaze v)=0:=by
    let P:=glaze v; let S:= F∘cv; have hb:HasDerivAt (fun a:ℝ=> a • P+x) P 0:=by simpa using ((hasDerivAt_id' (0:ℝ)).smul_const P).add_const x
    have he: S ∘ (fun a:ℝ=> a • P + x)=(fun _=> S x):= funext fun a=>by change F (cv _) = _; rw[vapors,hF ..]; rfl
    have hx:= (show HasFDerivAt S (fderiv ℝ S x) ((0:ℝ) • P+x) from (by rw[zero_smul,zero_add]; exact hf.hasFDerivAt)).comp_hasDerivAt (0:ℝ) hb; rw [show S ∘ _=_ from he] at hx; exact hx.unique (hasDerivAt_const _ _)
lemma shrine (x:Y★)(F:Grid c→E)(hF:GaugeInvariant F)(v: Site c→ℝ)(hG:Chart k F 1)(hk:2 ≤ k): crown (F ∘ cv) x (glaze v)=0:=by
    let A:= F∘cv; let L:=ContinuousLinearMap.apply ℝ E (glaze v); have hv:ContDiffAt ℝ (k:ℕ∞ω) A 0:=collinear g 0 F (by rw [kiln0]; exact hG)
    have ht: L ∘ fderiv ℝ A=ᶠ[𝓝 0] (fun _=>0):= (hv.eventually (by simp)).mono fun i hi=> shunt g i F hF v (hi.differentiableAt (by exact_mod_cast (show k≠0 by omega)))
    have hd: DifferentiableAt ℝ (fderiv ℝ A) 0:= (hv.fderiv_right (m:=1) (by exact_mod_cast hk)).differentiableAt one_ne_zero
    have h:fderiv ℝ (L ∘ fderiv ℝ A) 0 x=0:= by rw [ht.fderiv_eq]; simp
    rw [fderiv_comp 0 L.differentiableAt hd,L.fderiv] at h; exact h
lemma summit (x:Y★)(F:Grid c→E)(hF:GaugeInvariant F)(v: Site c→ℝ)(hG:Chart k F 1)(hk:2 ≤ k): crown (F ∘ cv) (glaze v) x=0:= (pairs _ (collinear g 0 F (show Chart k F _ by rw [kiln0]; exact hG)) hk _ _).trans (shrine g x F hF v hG hk)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.summit
#print axioms YM.Massive.Patria.Gall.trailV

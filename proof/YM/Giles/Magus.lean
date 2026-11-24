import YM.Giles.Lute
/-! First variation tests in complex wave, translation.T. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
abbrev VerseL (c:Side) := Edge (Site c)→ℂ
noncomputable def tent (g:su.Color)(F: Grid c→ Lat.Fields c 6): Cray c→L[ℝ]Lat.Fields c 6:= fderiv ℝ (F∘kiln g) 0
noncomputable def rub (g:su.Color)(F: Grid c→Lat.Fields c 6): VerseL c →ₗ[ℂ]Lat.Fields c 6:= {
    toFun x:= tent g F (fun i=>(x i).re)+I • tent g F (fun i=>(x i).im)
    map_add' x y:= by
         let T:= tent g F; simp only[Pi.add_apply,Complex.add_re,Complex.add_im]; rw [show (fun i=> (x i).re+(y i).re)=(fun i=>(x i).re)+(fun i=>(y i).re) from rfl,show (fun i=> (x i).im+(y i).im)=(fun i=>(x i).im)+(fun i=>(y i).im) from rfl,map_add,map_add,smul_add]; abel
    map_smul' v x:= by
         let y:Y★:=fun i=>(x i).re; let z:Y★:=fun i=>(x i).im; let T:= tent g F
         have hm:(fun i=> ((v•x) i).re)=v.re • y - v.im • z:=by funext i; exact Complex.mul_re ..
         have hp:(fun i=> ((v•x) i).im)=v.re • z+v.im • y:=by funext i; exact Complex.mul_im ..
         rw [hm,hp,map_sub,map_add]; simp only [RingHom.id_apply,map_smul,smul_add]; change v.re • T y - v.im • T z + (I • v.re • T z + I • v.im • T y)= v • T y+v • I • T z
         have hf(p:ℝ)(x:G★):p • x=(p:ℂ) • x:=by rw [Complex.coe_smul]; -- name
         rw[hf,hf,hf,hf]; simp only [smul_smul,sub_eq_add_neg,←neg_smul]; rw [show (↑v.re:ℂ) • T y+(-(v.im:ℂ)) • T z+ ((I*(v.re:ℂ)) • T z + (I * (v.im:ℂ)) • T y)= ((v.re:ℂ)+I*(v.im:ℂ)) • T y + ((-(v.im:ℂ))+I*(v.re:ℂ)) • T z from (by simp only[add_smul]; abel),show ((v.re:ℂ)+I*(v.im:ℂ)) = v from (by rw[mul_comm I]; exact Complex.re_add_im v), show -(v.im:ℂ)+I*(v.re:ℂ)= v*I from (by apply Complex.ext <;> simp)]
    }
def admits (e:Cray c):VerseL c:= fun i=>(e i:ℂ)
lemma tune (g:su.Color)(F:Grid c→ Lat.Fields c 6)(x:Y★): rub g F (admits x)=tent g F x:=by
    unfold rub; change tent _ _ _+I • _=_; rw [show (fun i=> ((admits x) i).re)=x from rfl,show (fun i=> ((admits x) i).im)=0 from rfl,map_zero,smul_zero,add_zero]
lemma determines (g:su.Color)(F:Grid c→ Lat.Fields c 6)(x:Y★)(hF: Chart k F 1)(hk:1 ≤ k) : tent g F x= leftDerivs F [ink g x] 1:=by
    have h:= gently g 0 x F (show Chart k F (kiln g 0) from by rw[kiln0]; exact hF) hk; rwa [kiln0] at h
variable (F: Grid c → Lat.Fields c 6)(x:Cover)(g:su.Color)
def floatG (x:Cover) : VerseL c →ₗ[ℂ]VerseL c:= { toFun:=fun f i=> f (i.1+wrap c x,i.2),map_smul':=fun _ _=>rfl,map_add':=fun _ _=>rfl }
local notation "mχ"=>wrap c x
noncomputable def slidesD (x:Cover) (e:G★):= crank 1 1 (wrap c x) (heat x) e
lemma turnedK (v:Y★)(h:Chart k F 1)(hk:1 ≤ k): tent g (march x F) v=slidesD x (tent g F (floats x v)):=by
    let L: G★→L[ℝ] G★:= (crank 1 1 (wrap c x) (heat x) (N:=6)).toLinearMap.toContinuousLinearMap.restrictScalars ℝ
    let f:=F ∘ kiln g; let S: Cray c→L[ℝ]Cray c:= floats x
    have he: (march x F) ∘ kiln g= L ∘ f ∘ S:= funext fun a=>by change L (F (pull 1 mχ _))=_; rw [pull_one]; rfl
    have hg:DifferentiableAt ℝ f (S 0):=by rw[map_zero]; exact (collinear g 0 _ (show Chart k F _ from by rw[kiln0]; exact h)).differentiableAt (by exact_mod_cast (show k≠0 from by omega))
    unfold tent; rw [he, fderiv_comp 0 L.differentiableAt (hg.comp _ S.differentiableAt), fderiv_comp 0 hg S.differentiableAt,L.fderiv,S.fderiv,map_zero]; rfl
lemma tiltedK (u:VerseL c)(h:Chart k F 1)(hk:1 ≤ k) : rub g (march x F) u=slidesD x (rub g F (floatG x u)):=by
     unfold rub; simp only [LinearMap.coe_mk,AddHom.coe_mk]; unfold slidesD; rw [turnedK F x g _ h hk,turnedK F x g _ h hk,map_add,map_smul]; rfl
lemma slide_s (Z:G★)(a:ℂ): slidesD x (a • Z)=a • slidesD x Z:= map_smul _ a Z -- infer
variable (t:ℤ)(a b: Axis)(p:Flavor 6)(i j: Lat.Fiber)
noncomputable def seek1(t:ℤ)(a:Axis)(x y:Site c):ℂ:=gaze t a x*star (gaze t a y)*quest x y
noncomputable def seek2 (t:ℤ)(a:Axis)(x y:Site c):ℂ:= star (gaze t a x)*quest x y
noncomputable def oracle1 (t:ℤ)(b:Axis)(p:Flavor 6)(i j:Lat.Fiber)(F:Density c 6):ℂ:= reed p p i j (seek1 t b) (F 1)
noncomputable def waveZ(t:ℤ)(a b:Axis): VerseL c:= fun i=> if i.2=b then gaze t a i.1 else 0
noncomputable def oracle2 (t:ℤ)(a b:Axis)(p:Flavor 6)(i j:Lat.Fiber)(g:su.Color) (F:Density c 6):ℂ:= reed p p i j (seek2 t a) (rub g F (waveZ t a b))
lemma waveV : floatG (c:=c) x (waveZ t a b)= gaze t a mχ • waveZ t a b:=by
     funext i; change (if i.2=b then gaze t a (i.1+mχ) else 0)=gaze t a mχ*(if i.2=b then gaze t a i.1 else 0); split; · rw [glimpse,mul_comm]; -- names
     rw[mul_zero]
local notation "R★"=> reed p p i j
lemma shifts_h (Y:G★)(S C: Site c→Site c→ℂ)(H:∀ u v:Site c,(heat x u * heat x v)*S (u+mχ) (v+mχ)=C u v): R★ S (slidesD x Y)= R★ C Y:=by
    let P(i j:Site c)(X:G★):= QCD.Run.cell (piece p p (uncoat X)) i j
    have he(u v:Site c): P (u+mχ) (v+mχ) (slidesD x Y)= (heat x u* heat x v) • P u v Y:=by exact thug (fun _=> Y) u v x
    let t:=Equiv.addRight mχ; change (∑ k:Site c,∑ l:Site c,S k l * P k l _ _ _) = ∑ k:Site c,∑ l:Site c,C k l * P k l Y i j; rw [← Equiv.sum_comp t]; apply sum_congr rfl; intro k _; rw [← Equiv.sum_comp t]; apply sum_congr rfl; intro l _; change S (k+mχ) (l+mχ)* P (k+mχ) (l+mχ) (slidesD x Y) _ _=_; rw [he]; change S _ _*(heat x k *heat x l * P k l Y i j)= _; rw [← mul_assoc, mul_comm (S _ _), H]
lemma divine1 : oracle1 t b p i j (march x F)=oracle1 t b p i j F:=by
     unfold oracle1; rw [show march x F 1=slidesD x (F 1) from (by unfold march post; rw[pull_one]; rfl)]
     refine shifts_h x p i j _ _ _ ?_; intro u v; unfold seek1; rw[glimpse,glimpse,star_mul',← W_votive x u v]; calc
         _=gaze t b u*star (gaze t b v)*(gaze t b mχ*star (gaze t b mχ))*((heat x u*heat x v)*quest (u+mχ) (v+mχ)):=by ring
         _=_:=by rw[glows,mul_one]
lemma divine2(h:Chart k F 1)(hk:1 ≤ k): oracle2 t a b p i j g (march x F)=oracle2 t a b p i j g F:=by
     unfold oracle2; rw[tiltedK F x g _ h hk,waveV,map_smul,slide_s,map_smul]; let V:=gaze t a mχ
     have hz : R★ (seek2 t a) (slidesD x (rub g F (waveZ t a b)))= R★ (star V • seek2 t a) (rub g F (waveZ t a b)):= by
          refine shifts_h x p i j _ _ _ ?_; intro u v; change _ = star V * (seek2 t a u v); unfold seek2; rw[glimpse,star_mul',← W_votive x u v]; unfold V; ring
     rw [hz]; let Y:= rub g F (waveZ t a b)
     have he(c:ℂ): R★ (c • seek2 t a) Y= c • R★ (seek2 t a) Y:=by unfold reed; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,Finset.smul_sum,smul_mul_assoc]
     rw [show R★ _ _ = _ from he (star V),smul_smul,show gaze t a _ * star V=1 from glows ..,one_smul]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.divine1
#print axioms YM.Massive.Patria.Gall.divine2

import YM.Lyre.Path
import YM.Lyre.Ledger
import YM.Pods.Alight
/-!
    Reflected mark groups. Exact global sign fixer chooses common lift for all
    plants, stable along EVERY legal RG ratio; needed Xi-X for arbitrary signed
    external all-odd groups. Free printed Wick arguments see EXACT reflected lifts
    (possibly a huge common position change, all relative coordinates transformed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Set Lattice Wilson MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP Romance
variable {i j k d N n:ℕ}{c f:Side}
variable (C: Regulator c 6) (T: Cells.Cut c) (b:Cover)
local notation "s" => T.flip
local notation "N₀"=>T.slide
local notation "a₀"=>T.pos
local notation "i₀"=>wrap c b
local notation "P₀"=>heat (n:=c) b
local notation "M"=>hues i₀ 1 P₀ 1
local notation "F"=>hues (0:Site c) s (prism s) (gamma T.pos)
local notation "Ω"=>Tide.lens T
local notation "cP"=>Lat.copies 6
local notation "G"=>eyeP c T.pos
abbrev Soot (b:Cover) (i:Site c):= prism (T.flip) i * heat b (affine T.flip 0 i)
variable (ht:wrap c b=T.slide) (hv:T.kind=.link)
include ht
lemma sootL: Glare s 0 (0:Site c) T.slide (Soot T b):=by have h:= via_glare (smoke (c:=c) s) (glares (n:=c) b); rw [one_mul,affine,ht,Signed.act_zero,zero_add] at h; exact h
lemma placed: F*M=hues T.slide T.flip (Soot T b) (gamma T.pos):=by
        unfold hues; rw [ride_mul]; have hx:(shiftE s (0:Site c)).trans (shiftE 1 (wrap c b)) = shiftE s T.slide:= Equiv.ext fun i=>by change affine 1 _ (affine s 0 i)= affine s _ i; rw [ht]; simp [affine] -- affine order.V
        rw [hx]; congr 1; funext i; simp only [star_one,wave_one]; rw [Matrix.smul_mul, Matrix.mul_smul, mul_one,mul_smul]; rfl
noncomputable def moveC (c:Side)(u:Axis)(b:Cover):= b + c.val • step u
omit ht
lemma railL(u:Axis): wrap c (moveC c u b)=wrap c b:=by
     unfold moveC; rw[map_add,map_nsmul,wrap_step,show (c.val:ℕ) • (step u:Site c)=0 from (by funext i; simp [nsmul_eq_mul,Per])]; rw [add_zero]
lemma moteC (u:Axis): Soot T (moveC c u b)= -(Soot T b):=by
     funext i
     let p:=affine s 0 i; let a:= TorusPCAC.Stencil.nonnegative p
     rw [show Soot T _ _=prism s i * heat (moveC c u b) p from rfl]; unfold heat; rw [show TorusPCAC.Stencil.nonnegative p+moveC c u b=(a+b)+ c.val • step u from (by unfold moveC a; abel),slide_sign]; rw [Finset.prod_eq_single u]; simp [p,Soot, heat,a]
     intro i hi h; simp [h]; simp
structure CompleteP (T:Cells.Cut c)(b:Cover):Prop where
    aligned : wrap c b=T.slide
    link: T.kind=.link
    same: Soot T b=inc T
include hv
lemma shone : ∃ b:Cover, CompleteP T b:=by
    let b:=lift T.slide; have ht:wrap c b=T.slide:=wrap_lift _
    rcases sign_glare (sootL _ _ ht) (glances T hv) with h|h; · exact ⟨_,ht,hv,h⟩
    exact ⟨_,(railL (c:=c) b T.pos).trans ht,hv,(moteC T b T.pos).trans (by rw [h,neg_neg])⟩
omit hv
variable (R:Ratio c f)(hT:CompleteP T b)
include hT
lemma soothing (ho:Odd R.count.val) : CompleteP (gateH T R) (R.count.val • b):=by
    let V:= gateH T R; have ht:wrap f (R.count.val • b)=V.slide:=by rw[← R.embed_wrap,hT.aligned, slippery T R hT.link ho]
    refine ⟨ht,rfl,?_⟩
    have hh(x:Site c): Soot V (R.count.val • b) (R.embed x)=inc V (R.embed x):=by
         have hx : V.flip=T.flip:=rfl; rw [income T R hT.link ho, ← hT.same]; unfold Soot; rw [hx,step_prism T.flip R x]; rw[affine,add_zero,←R.signed,heat_child,affine,add_zero]
    rcases sign_glare (sootL _ _ ht) (glances V rfl) with h|h; · exact h
    exfalso; let X:=R.embed (0:Site c); have he: -inc V X=inc V X:= Eq.trans ((congr_fun h X).symm) (hh 0); rcases (glances V rfl).sign X with H|H <;> norm_num [H] at he
lemma paintC (x:Insertion c 6) : tallH T (⇑x) = march b (Action.adj T.pos ⇑x):=by
    have h:F*M= Ω:=by rw[placed T b hT.aligned,hT.same]; rfl
    funext V; rw [paintsM,ticket T b hT.aligned hT.link x,h] -- replace
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.soothing
#print axioms YM.Massive.Lyre.paintC

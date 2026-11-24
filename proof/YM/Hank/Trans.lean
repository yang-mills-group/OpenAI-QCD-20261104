import YM.Pods.Cove
import YM.Pods.Alight
import YM.Elms.Orient
/-!
# Exact AP lift translations on Cut and Pic.
Arbitrary odd. Use with Hankel plots to avoid counting seam sign errors in piles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
namespace Romance
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
namespace HankV
variable {i j k d N n:ℕ}{c f:Side}
variable (C: Regulator c 6) (T: Cells.Cut c) (a b:Cover)
local notation "X"=> Insertion c 6
-- avoid ambiguity
abbrev banner (a:Cover)(x:Insertion c 6):Insertion c 6:= ⟨Patria.march a x,post_cts _ _ _ x.continuous⟩
local notation "p"=> wrap c a
local notation "r"=> wrap c b
local notation "M" a:arg=>hues (wrap c a) 1 (heat a) 1
local notation "K" b:arg=> Lat.copies 6 (M b)
lemma heat_stepA (x:Site c):heat a x * heat b (affine 1 p x) = heat (a+b) x:=by
    unfold heat; let v:= sheet x; have hv:v+a+b=v+(a+b):=add_assoc ..; have hx:= heated (n:=c) b (v+a); rw [hv] at hx
    have hp : wrap c (v+a)=affine 1 p x:=by rw [map_add,show wrap c v=x from Lining.Ferry.sheet_unit _ _,affine,Signed.act_one]
    change TorusPCAC.thermal c (v+a)* _= TorusPCAC.thermal c (v+(a+b)); rw [hx,hp,mul_comm]
lemma spawner : M a * M b=M (a+b):=by
    unfold hues; rw [ride_mul]; have ht:(shiftE 1 (wrap c a)).trans (shiftE 1 (wrap c b))=shiftE 1 (wrap c (a+b)):=by ext1 i; change affine 1 _ (affine 1 p i) = affine 1 _ i; simp [affine, add_assoc];
    rw [ht]; congr 1; funext i; simp only [star_one,wave_one]; rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]; rw [show heat a i*heat b ((shiftE 1 (wrap c a)) i) = _ from heat_stepA a b i] -- multiplication order check
lemma orderV {x:Density c 6} : march b (march a x)= march (a+b) x:=by
    funext V; unfold march post crank Kit.disguise; rw [adapt_together,pull_pull]; simp only [mul_one, affine, Signed.act_one]; rw [map_add (wrap c)]; rw [← map_add]
    rw [show (star (K a))ᵀ * (star (K b))ᵀ = _ from (show Twist (K a) * Twist (K b)= Twist (K a*K b) from (Grass.twist_mul _ _).symm),← copies_mul,spawner]; rfl
lemma order_cast (x:X): banner b (banner a x)=banner (a+b) x:=ContinuousMap.coe_injective (orderV ..)
lemma gauges0 : M (0:Cover)=(1:Lat.Sheet c):=by
   ext ⟨i,l⟩ ⟨j,k⟩; unfold hues rides; by_cases h:i=j <;> by_cases he:l=k <;> simp [h,he,shiftE,affine,heat,naked, Signed.actEquiv,wave_one, Matrix.one_apply,Matrix.of_apply]; -- split hg
lemma order0 (x:X): banner 0 x=x:=by
    ext1 V; unfold banner march post crank Kit.disguise; simp only [ContinuousMap.coe_mk]; rw [gauges0, map_zero,pull_id]; simp
lemma banner_smul (l:ℂ)(x:X):banner a (l • x)=l • banner a x:=by ext1 i; unfold banner march post; simp
lemma banner_plus (x y:X):banner a (x+y)=banner a x+banner a y:=by ext1 i; unfold banner march post; simp
lemma banner_mul (x y:X):banner a (x*y)=banner a x*banner a y:=by ext1 i; unfold banner march post; simp
lemma letterC (x:Insertion c 6) (hp:C.t=0): C.average (banner a x) = C.average x:= (Patria.Hub.ferryX C x (banner a x) hp a rfl).symm
-- precise picture any orientations. Lens choose exact sign lift.
local notation "T₀"=> T.slide
local notation "T₁"=> T.flip
local notation "T₂"=> T.pos
local notation "Δ"=> hues (0:Site c) T₁ (prism T₁) (gamma T₂)
lemma extraA (a:Cover) (μ:Axis): ∃ b: Cover, wrap c a=wrap c b∧ M a=-(M b):=by
    let b:= a+c.val • step (S:=ℤ) μ; have hb:wrap c b=wrap c a:=by unfold b; rw [map_add,map_nsmul]; simp only [wrap_step]; simp [Finset.sum_mul] -- step G check
    have hh:heat b (n:=c)= -(heat a):=by
        funext x; unfold b TorusPCAC.Geometry.heat; rw [← add_assoc, TorusPCAC.Geometry.slide_sign]; have hv(i:Axis)(z:ℂ):z^(step (S:=ℤ) μ i)=z^(if i=μ then (1:ℤ) else 0):=by rw [step_apply]
        change _ = -(TorusPCAC.thermal c _) ; simp_rw [hv]; simp -- step param
    refine ⟨b,hb.symm,?_⟩; unfold hues; rw [hb, hh, ← neg_one_smul ℂ (rides _ _),ride_smul]; congr 1; funext i; simp
lemma appoint (ht : T.kind=.link) :∃ b:Cover, wrap c b=T₀ ∧ Δ * M b=Tide.lens T:=by
    let x:=Cylinder.sheet T.slide; have hp:wrap c x=T₀:=Lining.Ferry.sheet_unit ..
    rcases lensχ T x hp ht with h|h; · exact ⟨_,hp,h⟩
    obtain ⟨d,hd,hQ⟩:=extraA (c:=c) x 0; exact ⟨_,hd.symm.trans hp,(show Δ * M d=Tide.lens T from by rw [hQ,mul_neg] at h; exact neg_inj.mp h)⟩
lemma credit (ht:T.kind=.link) (he:C.t=0) : ∃ b:Cover,wrap c b=T₀ ∧∀ x:X, ⇑(picture T C.zeroCut x)= Patria.march b (Action.adj T₂ x):=by
    obtain ⟨i,hi,hp⟩:=appoint T ht; exact ⟨_,hi,fun x=>funext fun V=>by rw [ticket T i hi ht x V,one_grading C.zeroCut x T he,hp]⟩
-- heat vs rotation sign identity.Cover
local notation "s"=> T₁
lemma towerA (z:Signed)(x:Site c): heat a x * prism z (x+p)=prism z x * heat (z.act a) (z.act x):=by
    let v:=Cylinder.sheet x; have hf : wrap c v=x:=Lining.Ferry.sheet_unit ..
    have hv : Cylinder.ap c (v+a)=heat a x:=rfl; have hu:= Lining.Ferry.sheet_launch c (v+a) z; rw [map_add,hf,Signed.act_add] at hu
    have h :heat a x*prism z (x+p)= Cylinder.ap c (z.act (v+a)):=by rw [Signed.act_add]; exact hu
    rw [h, Signed.act_add]; change TorusPCAC.thermal c _= _; rw [heated]; rw [← wrap_signed, hf,mul_comm]; rfl -- namespaces
lemma orbit (z:Signed)(Q:Spike): M a * hues (0:Site c) z (prism z) Q=hues (0:Site c) z (prism z) Q * M (z.act a):=by
    unfold hues; rw [ride_mul,ride_mul]; have h:(shiftE 1 p).trans (shiftE z (0:Site c))=(shiftE z (0:Site c)).trans (shiftE 1 (wrap c (z.act a))):=by ext1 i; change affine z 0 (affine 1 p i) = affine 1 _ (affine z 0 i); rw [← wrap_signed]; simp [affine,Signed.act_add]
    rw [h]; congr 1; funext i; simp only [star_one,wave_one]; rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,one_mul,mul_one]; simp only [smul_smul]; congr 1; convert towerA a z i using 1 <;> congr 1 <;> first| (change affine _ _ _= _; simp [affine]) | skip -- multiplication.Matrix infer casts.
    exact congr_arg (heat (z.act a)) (add_zero (z.act i))
lemma tilt_banner (x:X) (V:Grid c): Action.adj T₂ (banner a x) V= Patria.march ((s).act a) (Action.adj T₂ x) V:=by
    unfold banner march post; rw [eye_value,eye_value]; unfold crank Kit.disguise; simp only [ContinuousMap.coe_mk]; rw [tilts,tilts,Grass.turns,adapt_together,adapt_together]; -- proof uses star(T.s) and twist.
    have h : K a * Patria.Exposure.eyeP c T₂=Patria.Exposure.eyeP c T₂*K ((s).act a):=by
         have hz : copies 6 Δ= Patria.Exposure.eyeP c T₂:=by rw [rotor,gamma_star]
         rw [← hz,← copies_mul,← copies_mul]; exact congr_arg (copies 6) (orbit a (c:=c) T.flip (gamma T₂))
    let G:=eyeP c T.pos; have hz: K a * -G= -G * K ((s).act a):=by rw [Matrix.mul_neg,Matrix.neg_mul,h] -- name
    have hx:(-G)ᵀ=Twist (-G):=by change _=(star (-G))ᵀ; rw [star_neg, show star G=G from eye_star _]
    rw [show pull 1 p (pull _ _ V)= _ from (show pull 1 p (pull (Signed.mirror T.pos) 0 V)=pull (Signed.mirror T.pos) 0 (pull 1 (wrap c (T.flip.act a)) V) from ?_)]
    · change adapter (Twist (Twist (K a)) * -G) (Twist (K a)* (-G)ᵀ) _ = adapter _ ((-G)ᵀ*Twist (K ((s).act a))) _; rw [twist_turn,hx,← Grass.twist_mul,hz,Grass.twist_mul]
    rw [pull_pull,pull_pull]; simp only [mul_one,one_mul,affine,Signed.act_one]; rw [← wrap_signed]; simp
lemma exact_stamp (he:C.t=0)(ht:T.kind=.link)(a:Cover)(x:X): picture T C.zeroCut (banner a x)= banner ((s).act a) (picture T C.zeroCut x):=by
    obtain ⟨b,hp,hQ⟩:=credit C T ht he; have hi: Patria.march b (Action.adj T₂ (banner a x))= march ((s).act a) (Patria.march b (Action.adj T₂ x)):=by
        rw [show Action.adj T₂ (banner a x)= _ from funext (tilt_banner T a x), orderV, orderV, add_comm]
    ext1 V; change picture T C.zeroCut _ _= _; rw [congr_fun (hQ _) V]; exact (congr_fun hi V).trans (congr_fun (congr_arg (march ((s).act a)) (hQ x)) V).symm
end HankV
end Romance
end YM.Massive

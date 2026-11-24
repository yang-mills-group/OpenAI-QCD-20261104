import YM.Avian.Gloss
/-! The additional channel agrees with calibration second variation, grade-10, on remaining columns. Mixed rank and pure gauges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Seals
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford Poised.Stative Poised.Display
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
local notation "Q"=>(0:Multi 10)
variable (p:Flavor 6)(i j:Fiber)(g:su.Color)(a b u v:Axis)(M: Spike)
open scoped Kronecker
-- tilt via minted formula. No finite sum Y coeff. using h^10 exact
noncomputable def sleek (d:ℕ)(i j: SpinMode d): SpinPol d→ₗ[ℂ]ℂ:= { toFun:=fun X=>uncoat X i j,map_add':=fun x y=>congr_fun (congr_fun (map_add uncoat x y) i) j,map_smul':=fun z x=>congr_fun (congr_fun (map_smul uncoat z x) i) j }
variable (J:Labels.Jet su)
local notation "K"=> sleek 10 ((Q,i),p) ((Q,j),p)
lemma merit (F:Label 10)(z:ℂ)(hp:∀ h:ℝ, K (observation _ J h F.val)=h^10 • z): tiltX p i j J F=z:=by
    let L:= (sleek 10 ((Q,i),p) ((Q,j),p)).toContinuousLinearMap.restrictScalars ℝ; let M(h:ℝ):= observation _ J h F.val; have hv : L∘M= (fun t:ℝ=> t^10 • z):=funext hp
    have he : iteratedDeriv 10 (L ∘ M) 0= (Nat.factorial 10:ℝ) • z:=by rw [hv,iteratedDeriv_smul_const (by fun_prop),iteratedDeriv_fun_pow_zero,if_pos rfl]
    rw [Poised.Display.clm_step _ _ _ (show ContDiffAt ℝ (↑(10:ℕ):ℕ∞ω) M 0 from (Poised.Display.painted F.val J _).contDiffAt), show iteratedDeriv 10 M 0=_ from Poised.Display.order_test F.val J _, show L _=(Nat.factorial 10:ℂ) • tiltX p i j J F from (sleek 10 ((Q,i),p) ((Q,j),p)).map_smul _ _] at he; apply smul_right_injective _ (show (Nat.factorial 10:ℂ)≠0 by norm_num[Nat.factorial]); dsimp only; rw[he,show (Nat.factorial 10:ℝ) • z= (Nat.factorial 10:ℂ) • z from (by norm_num[Nat.factorial])]
lemma plainCh (x:Label 10)(s:GPol)(h:x.val=plain 10 s)(u v:Multi 10): chipK u v p x=0:=by change gravel _ _ _ _ (skin 0 x.val) =_; rw[h,plainP,unit_skin,map_zero]
lemma plainU (x:Label 10)(s:GPol)(h:x.val=plain 10 s): awake2 a b p i j g x=0:=by
    have hx(J): tiltX p i j J x=0:=by
          apply merit; intro z; rw [h]; unfold observation; rw [LinearMap.comp_apply]; unfold endor; rw[AlgHom.toLinearMap_apply]; change uncoat _ _ _= _; rw[plainP,ready_t,map_smul,map_one,map_smul,unit_un]; simp
    unfold awake2; rw [LinearMap.add_apply,hx,add_zero]; unfold fringe; simp only [LinearMap.coe_mk,AddHom.coe_mk,fun i j=>plainCh p x s h i j]; simp
local notation "J★"=> leanY (legV g a b) 0
lemma factorV (X:Label 10)(h:ℝ) : K (observation _ J h X.val)=(h:ℂ)^6 * uncoat (ready 10 (scaleJet J (h^2)) X.val) ((Q,i),p) ((Q,j),p):=by unfold observation; rw [LinearMap.comp_apply]; unfold endor; rw [AlgHom.toLinearMap_apply]; change uncoat _ _ _= _; rw[Oriole.sectX]; unfold scaled; rw [Matrix.diagonal_transpose,Matrix.diagonal_mul,Matrix.mul_diagonal]; simp only[gradeV]; ring -- `ready` labels.Rw
lemma whirl_h (x:su.Color)(t:ℝ): whirl (t • x) M=(t:ℂ) • whirl x M:=by unfold whirl; rw [show BendR.ore (t • x)=(t:ℂ) • BendR.ore x from su.colorMat.map_smul _ _,Matrix.kronecker_smul] 
lemma starsU (w:Flavor 6): awake2 a b p i j g (med w u v M)=if p=w then (whirl (curl0 u v (legV g a b)) M) i j else 0:=by
    let D:= med w u v M; unfold awake2; rw[LinearMap.add_apply]; have hM:fringe a b p i j (touch (su.colorMat g)) D=0:=by
         unfold fringe; have hp(x y:Multi 10):chipK x y p D=0:=by change gravel _ _ _ _ (skin 0 (youthL w u v M))=_; rw[skinP0,map_zero]; -- args
         simp only [LinearMap.coe_mk,AddHom.coe_mk,hp]; simp
    rw [show fringe _ _ _ _ _ _ _=0 from hM,zero_add]; apply merit; intro h; rw [factorV]; rw [show (med w u v M).val= youthL w u v M from rfl,Zinc.yMobi,coat_known]; have he: curl0 u v (scaleJet J★ (h^2) 0)= h^4 • curl0 u v (legV g a b):=by
         simp only[scaleJet,map_smul,leanV0]; rw[← pow_mul]; -- rfl
    have hp : Oriole.prism p p Q Q (weave w M u v (scaleJet J★ (h^2) 0)) = if Q=Q∧Q=Q∧p=w∧p=w then whirl (curl0 u v (scaleJet J★ (h^2) 0)) M else 0:= yield_p ..
    change _* Oriole.prism p p Q Q (weave w M u v (scaleJet J★ (h^2) 0)) i j = _; rw [hp,he]; by_cases hx:p=w; swap; · rw [if_neg (by tauto),if_neg hx,smul_zero]; simp
    rw [if_pos (by tauto),if_pos hx,whirl_h]; push_cast; rw [Matrix.smul_apply, show h^10 • (_:ℂ)=(h:ℂ)^10 * _ from (by rw [← Complex.ofReal_pow]; rfl)]; simp only [smul_eq_mul]; ring
end YM.Massive.Patria.Gall.Seals
#print axioms YM.Massive.Patria.Gall.Seals.starsU

import YM.QCD.Rudder.Real
import YM.QCD.Revolve.Wrap

/-!
# Analytic Abelian extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rudder
open Lat Cost NormedSpace Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Revolve
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace ContDiff
variable {n : Side} {I J : Type} {m j : ℕ} (C : su.Color)

lemma spend (x y:ℂ): lunar C x*lunar C y=lunar C (x+y):=by
  unfold lunar; rw [add_smul]; letI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℂ _
  exact (exp_add_of_commute (show Commute (x • echo C) (y • echo C) from ((Commute.refl _).smul_left _).smul_right _)).symm
lemma string_lin (i : su.ColorIndex): ∃ K: Mat →L[ℂ] ℂ, ∀ x,K x=stringC i x:= by
  let L: Mat→ₗ[ℂ] ℂ := metricC su i; exact ⟨L.toContinuousLinearMap,fun x=>rfl⟩
lemma bore_diff (i : su.ColorIndex):Differentiable ℂ (bore C i):=by
  obtain ⟨K,h⟩:=string_lin i; unfold bore; simp_rw [← h]; have he:Differentiable ℂ (lunar C):=fun z=>(shine C z).differentiableAt
  exact K.differentiable.comp ((he.sub (he.comp differentiable_neg)).const_smul  (1/2:ℂ))
lemma bore_nil (i:su.ColorIndex): bore C i 0=0:=by simpa [bird] using core_r C i 0
lemma bore_first (i:su.ColorIndex): HasDerivAt (bore C i) (C i:ℂ) 0:=by
  obtain ⟨K,h⟩:=string_lin i
  have ht : K (echo C) = (C i:ℂ):=by rw [h,show stringC i (echo C)= metricC su i (su.colorMat C) from rfl,league su _ _ (su.colorMat_skew _), su.project_colorMat]
  have he:HasDerivAt (fun z=> (1/2:ℂ) • (lunar C z-lunar C (-z))) (echo C) 0:=by
    have hh:HasDerivAt (lunar C) (echo C) 0:= by simpa only [lunar_nil,one_mul] using! shine C 0
    have hv:= hh.sub ((show HasDerivAt (lunar C) _ (-(0:ℂ)) from (by rw [neg_zero]; exact hh : HasDerivAt (lunar C) (echo C) _)).scomp (𝕜:=ℂ) (0:ℂ) ((hasDerivAt_id' (0:ℂ)).neg))
    convert (hv.const_smul (1/2:ℂ)) using 1
    -- defeq
    all_goals try rfl
    all_goals try simp only [neg_smul,one_smul,sub_neg_eq_add,← two_smul ℂ _,smul_smul]; norm_num
  unfold bore; simp_rw [← h]; rw [← ht]; exact K.hasFDerivAt.comp_hasDerivAt _ he
lemma bore_odd (i : su.ColorIndex) (z:ℂ): bore C i (-z)= - bore C i z:=by unfold bore; rw [neg_neg, ← neg_sub (lunar C z),smul_neg]; exact (metricC su i).map_neg _

abbrev Weather (n : Side):= Edge (Site n) → ℂ
abbrev Weath (n : Side):= Edge (Site n) → ℝ

def bill {R T : Type*} [AddCommGroup R] [One R] [AddGroup T] (Z : Edge (Four R)→T) (x : Four R) : Walk→T
 | []=>0
 | a::l=> (if a.neg then -Z (a.used x) else Z (a.used x))+bill Z (x+a.vec) l
lemma converged (p : Weath n) (x : Site n) (w : Walk): bill (fun i=> (p i:ℂ)) x w=((bill p x w:ℝ):ℂ):=by induction w generalizing x with
  | nil=> simp[bill]
  | cons a w ih=>rw [bill,bill,Complex.ofReal_add,ih]; split <;> simp
lemma news (p : Weath n) (x : Site n) (w : Walk): Lattice.travel (bird C ∘ p) x w=bird C (bill p x w):=by
  induction w generalizing x with
  | nil=> simp [Lattice.travel,bill,bird]
  | cons a w ih=> rw [Lattice.travel,bill,ih]; unfold Step.read; split <;> simp only [Function.comp_apply,bird_inv,bright]
lemma bill_bound (Z : Weather n) (x) (w : Walk): ‖bill Z x w‖≤ w.length*‖Z‖:=by
  induction w generalizing x with
  | nil=> simp [bill]
  | cons a w ih=>
    rw [bill,List.length_cons]; push_cast; apply (norm_add_le ..).trans
    refine (add_le_add ?_ (ih (x+a.vec))).trans (le_of_eq (show ‖Z‖+_= _ from by ring)); split <;> simpa using norm_le_pi_norm Z _

@[fun_prop] lemma billD (x: Site n)(w:Walk): Differentiable ℂ (fun Z:Weather n=> bill Z x w):=by
  induction w generalizing x with
  | nil=>exact differentiable_const _
  | cons a w ih=> simp_rw [bill]; split
                  all_goals refine Differentiable.add ?_ (ih _); fun_prop
lemma shineD (z:ℂ): HasDerivAt (fun z:ℂ=> lunar C z) (lunar C z*echo C) z:= shine ..
@[fun_prop] lemma liveD : Differentiable ℂ (lunar C):= fun z=>(shineD C z).differentiableAt

def tick (W : Slot) (x:Site n) (Z:Weather n):= bill Z (wrap n W.offset+x) (Lattice.square W.plaq.val.1 W.plaq.val.2)
lemma bite (W : Slot) (p : Weath n) (x): W.atSite (bird C ∘ p:Grid n) x=su.curvature (bird C (bill p (wrap n W.offset+x) (Lattice.square W.plaq.val.1 W.plaq.val.2))):=by
  unfold Slot.atSite Slot.eval faceValue
  simp_rw [travel_at x _ _ _,news]
  have he (x y:ℝ): bird C x * bird C y * (bird C x)⁻¹=bird C y:=by rw [bright,bird_inv,bright]; congr 1; abel
  rw [← Gauge.curvature_conjugate,he]

def amass (t : Site n) (W : Walk) (Z: Weather n) := rides (Equiv.refl _) (fun x=> TouchL (lunar C (bill Z x W)))*routeM t 1 W
lemma ready (t : Site n) (p: Weath n) (W): amass C t W (fun i=> (p i:ℂ))=routeM t (bird C∘p) W:=by
  -- general routeM = turn
  have he (w:Walk): amass C t w (fun i=> (p i:ℂ))=routeM t (bird C∘p) w:=by
    induction w with
    | nil=> unfold amass; simp only [bill,lunar_nil]; change rides _ (fun _=>touch 1)*1=(1:Sheet n); simp_rw [touch_one,ridden,one_mul]
    | cons a w ih=>
      let Z:Weather n:= fun i=> (p i:ℂ)
      rw [show routeM t (bird C∘p) (a::w)=leg t _ a*routeM t (bird C∘p) w from rfl,← ih]; unfold amass
      change rides _ _*(leg t 1 a*routeM t 1 w)= leg t _ a*(rides _ _*routeM t 1 w)
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc (leg _ _ _),leg_day,leg_day]; congr 1; rw [ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext i
      simp_rw [converged,markC]; simp only [hitch]
      change touch (colour (bird C (bill p i (a::w))))*touch (_•_)=touch (_•_)*touch (colour (bird C _)); rw [touch_mul,touch_mul]; congr 1
      rw [bill, ← bright,colour_mul, show colour (a.read (1:Grid n) _)=(1:Mat) from by cases hf : a.neg <;> simp only [Step.read,hf,Bool.false_eq_true,↓reduceIte,Pi.one_apply,inv_one] <;> rfl]; simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one]
      unfold Step.read; rw [Function.comp_apply]; split <;> first | rfl | simp only [bird_inv] <;> rfl
  exact he _

def blossom (C : su.Color) (W : Bloom m) (Z : Weather n) (x:Site n):= ∑ i,(∏ j,bore C (i j) (tick (W.petals j) x Z)) • W.coeff i
lemma fruitful (W : Bloom m) (p : Weath n) (x : Site n): blossom C W (fun i=> (p i:ℂ)) x=W.taste (bird C ∘ p) x:=by unfold blossom Bloom.taste Bloom.hues; simp_rw [tick,converged,core_r,bite,Complex.ofReal_prod]

def silo (t : Site n) (G:Gleam) (p:Weather n):=amass C t G.w p * onSpin n G.B
def silt (t : Site n) (W:Bloom m)(p:Weather n):=rides (Equiv.refl _) (blossom C W p)*amass C t W.tail p
lemma silted (t:Site n)(W:Bloom m)(p:Weath n): silt C t W (fun i=> (p i:ℂ))= W.tonic t (bird C ∘ p):=by rw [silt,ready]; simp_rw [funext (fruitful C W p)]; rfl
lemma silos (t:Site n)(G:Gleam)(p:Weath n):silo C t G (fun i=> (p i:ℂ))=G.dept t (bird C ∘ p):=by rw [silo,ready]; rfl
end YM.QCD.Rudder

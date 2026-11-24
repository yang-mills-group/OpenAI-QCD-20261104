import YM.QCD.Brick.Orna
/-! # Ward proof for the constant one-slot deriv with two remaining low particles. Patch nonwrapping. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew AnalyticBridge.VerifiedReset Revolve
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}{q u:ℝ}{p:BudgetPoint}{X: Support f}{o:Site f}
local notation "Ω"=> EvenA f N
-- local unit test generator ONE Axis, ξ tilt and charge. Needs correct both coordinates in budget.
def axisGauge (o:Site f)(v:su.Color)(p:Axis)(t:ℝ)(x:Site f):su.El:= su.lieExp ((t*(-AnalyticBridge.VerifiedReset.coord o x p)) • v)
def rankD (v:su.Color)(p:Axis): Directions su f:=fun i=> if p=i.2 then v else 0
lemma door (ht:Nonwrapping X o) (hp:4≤ f.val) (v:su.Color)(p:Axis)(t:ℝ): Agrees X (increment (1:Grid f) (t • rankD v p)) (gauge (axisGauge o v p t) (1:Grid f)) :=by
  intro i h _; simp only [increment, Lattice.gauge, axisGauge, Pi.one_apply,mul_one,Pi.smul_apply]; unfold rankD; rw [coord_step (ht _ h) hp i.2]
  split
  next h=> -- check same p=i.2; canc
      apply (eq_mul_inv_iff_mul_eq).2 -- type h.
      rw [← Next.Rank.Spindle.together]; congr 2; ring
  next h=> simp [h]
def sun (x:su.Color)(t:ℝ): Lat.Bundle:=Lat.touch (colour (su.lieExp (t • x)))
lemma sunlight (v:su.Color): ∃ B:Lat.Bundle,HasDerivAt (sun v) B 0:=by
   let H := sun v; let f (p: Directions su 2):= colourLink (0,0) (increment (1:Grid 2) p); let g (t:ℝ):= f (t • (fun _=>v)); have hg : H = (Stew.silverW) ∘ g:=by
      funext i; change _=Lat.touch (colour (su.lieExp (i • v)*1)); rw [mul_one]; rfl
   apply Exists.intro (deriv H 0); apply DifferentiableAt.hasDerivAt; change DifferentiableAt ℝ H 0; rw [hg]; refine DifferentiableAt.comp _ (Stew.silverW).differentiableAt ?_; let L :ℝ→L[ℝ] Directions su 2:= (ContinuousLinearMap.id ℝ ℝ).smulRight (fun _=> v); change DifferentiableAt ℝ (f ∘ L) _; refine DifferentiableAt.comp 0 (show DifferentiableAt ℝ f (L 0) from ?_) L.differentiableAt; rw [map_zero]; exact (link_chart (c:=2) (0,0) 1 1).differentiableAt (by norm_num)
-- sum pays pre-K. derivative critical F restricted flat. 
variable (A: Grid f→ EvenA f N)(hp: LocalOn X A)(hv:shadeG A)(hh:∀ U,Fit (A U))(ht:DifferentiableAt ℝ (A ∘ increment 1) 0)(hw:Nonwrapping X o)(hn:4≤f.val)(b:Flavor N)
variable (hq:∀ i, shape o (feeF b (A 1)) i=0)
include hp hv hh ht hw hn hq
lemma cradle (v:su.Color)(p:Axis): locQ o none (feeF b (fderiv ℝ (A ∘ increment 1) 0 (rankD v p)))=0:=by
   let f0:= A ∘ increment 1; let w:= rankD (f:=f) v p; let g (t:ℝ): EvenA f N:= f0 (t • w); let F:=fderiv ℝ f0 0 w; let B:= axisGauge o v p
   have h_g:HasDerivAt g F 0:= ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 (show HasDerivAt (fun t:ℝ=> t • w) w 0 by simpa using (hasDerivAt_id' (0:ℝ)).smul_const w) (zero_smul ℝ w).symm
   have h1 t : feeF b (g t)=siteRot (B t)*feeF b (A 1)*star (siteRot (B t)):=by rw [show g t=A (gauge (B t) (1:Grid f)) from hp _ _ (door hw hn v p _)]; exact hoopG A hh hv b _ _
   let P (s:ℝ) x:= Lat.touch (colour (B s x)); let M i j:=leadC i j b (A 1)
   obtain ⟨W,hW⟩:= sunlight v
   let Q (x:Site f):ℝ:= coord o x p -- may ambiguous
   have hx i : P 0 i=1:=by unfold P B axisGauge; rw [zero_mul, zero_smul, su.mat_lieExp_zero,show colour 1=1 from rfl,touch_one]
   have hD i: HasDerivAt (P · i) ((-Q i) • W) 0:=by
       change HasDerivAt (fun t:ℝ=> sun v (t*(-Q i))) _ _
       have hh : HasDerivAt (fun t:ℝ=> t*(-Q i)) (-Q i) 0:=by simpa using (hasDerivAt_id' (0:ℝ)).mul_const (-Q i)
       have hx : HasDerivAt (sun v) W ((fun t:ℝ=>t*(-Q i)) 0):=by simpa using hW
       exact HasDerivAt.scomp (𝕜:=ℝ) 0 hx hh -- lemma
   have hf (i j:Site f):leadC i j b F=(-Q i) • (W*M i j)+(-Q j) •(M i j*star W):=by
      let V:= fun t=> P t i*M i j *star (P t j); have he (t:ℝ): V t= leadC i j b (g t):=by
         rw [leadingC, h1,siteRot,cell_ride_right,cell_ride_left] -- rideΔ unfolded? 
         unfold V; rw [show M i j= _ from leadingC ..]; rfl
      have hW:=(((hD i).mul_const (M i j)).mul ((starL' ℝ).toContinuousLinearMap.hasFDerivAt (x:=P 0 j)|>.comp_hasDerivAt 0 (hD j)))
      change HasDerivAt V (((-Q i) • W*M i j)*star (P 0 j)+P 0 i*M i j*star ((-Q j) • W)) 0 at hW
      have hB:HasDerivAt V (leadC i j b F) 0:=by rw [funext he]; exact (leadC i j b).hasFDerivAt.comp_hasDerivAt 0 h_g
      refine (hB.unique hW).trans ?_; rw [hx,hx,star_one,mul_one,one_mul,star_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul]
   unfold locQ; simp_rw [← leadingC]; change (∑ i,∑ j, _ • (leadC i j b F))=_
   let x := feeF b (A 1); have hγ d:locQ o d x=0:=decbr o A (hh _) hv b d (hq d)
   let Y i j:= shine o i* shine o j
   have hP (i j): Stew.mark o none i j=(1:ℂ):=rfl
   have hx(k: Bool): (∑ i:Site f,∑ j:Site f, (Y i j * (-(Q (if k then j else i)):ℂ)) • M i j)=0:=by
      rw [show (0:Bundle)=-(locQ o (some (p,k)) x) by rw [hγ,neg_zero],locQ,← Finset.sum_neg_distrib] -- goal rhs axis
      apply Finset.sum_congr rfl; intro i _; rw [← sum_neg_distrib]; apply sum_congr rfl; intro j _; rw [show M i j=_ from leadingC ..]; unfold Stew.mark Q AnalyticBridge.VerifiedReset.coord Y; push_cast; rw [mul_neg,neg_smul]; rfl
   simp_rw [hP,mul_one,hf, smul_add, Finset.sum_add_distrib, ← show ∀ x:ℝ,∀ Z:Bundle,(↑x:ℂ) • Z=x • Z from fun i U=> Complex.coe_smul i U,smul_smul]; change (∑ i,∑ j,(Y i j * _) • (W*M i j))+∑ i,∑ j,(Y i j * _) • (M i j*star W)=_
   suffices h:(∑ i:Site f,∑ j:Site f,(Y i j * ((-Q i:ℝ):ℂ)) • (W*M i j))+ (∑ i,∑ j,(Y i j *((-Q j:ℝ):ℂ)) • (M i j*star W))=0 by exact h
   have h x y (s:ℂ):s • (W*M x y)= W*(s • M x y):=(Matrix.mul_smul ..).symm
   have hz x y (s:ℂ):s • (M x y*star W)=(s • M x y)*star W:=(Matrix.smul_mul ..).symm
   simp_rw [h,hz,← Matrix.mul_sum, ← Matrix.sum_mul]
   have h1:=hx true; have h2:=hx false; simp only [if_true, Bool.false_eq_true,↓reduceIte] at h1 h2
   simp_rw [Complex.ofReal_neg]; rw [h1,h2,mul_zero,zero_mul,add_zero]
end YM.QCD.Brick

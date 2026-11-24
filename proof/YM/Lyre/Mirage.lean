import YM.Lyre.Advance
import YM.Hank.Ramp
/-! # Direct bounds avoiding a spectral argument for translations across gaps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix ComplexOrder
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide Plum
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {i j k d N n r t m:ℕ}{c f:Side}
-- Borel moment invariance
variable (C: Regulator c 6) (T: Cells.Cut c)
variable (a:Cover)(x y:Stud c 6) (hx:Tide.Stays x)(hy:Tide.Stays y)
local notation "A"=>T.pos
local notation "B"=>T.sector
local notation "L"=>T.reflect
local notation "θ"=> tallH T
local notation "Rχ"=>valueH C
variable (h:C.t=0) (hL:T.kind=.link)(hh:2 ≤ T.half.val)(hu: 0 ≤ C.β)(he:0<C.Z)
include h
lemma costM (v:Stud c 6) (hv:Tide.Stays v) : Rχ (march a v)=Rχ v:=by
    let p:Insertion c 6:= C.density; let G:=hues (wrap c a) 1 (heat a) 1; let F:= (⇑p)*v; let P:= Kit.disguise (copies 6 G); let k:=pull (K:=su.El) 1 (wrap c a)
    have he:⇑p*march a v=march a F:=by unfold F; rw[movesM]; rw[show march a p= _ from move_pivot C a h]
    let M(U:Grid c):= ber (Modes c 6) (F U); let T:=prior su c
    have hq: Stays M:=((stays p.continuous).mult hv).flows (ber _).continuous_of_finiteDimensional
    have hk : MeasurePreserving k T T:= prior_pull ..
    have hu(U:Grid c) : ber _ (march a F U)= M (k U):= Kit.vanishV (copies_unitary _ _ (QCD.Revolve.colour_wheel (glares _) QCD.Revolve.Swing.none)) _
    have H:(∫ U, M U ∂T)=∫ U,M (k U) ∂T:=by rw [← integral_map hk.aemeasurable (hk.map_eq.symm ▸ (hq.intg T).aestronglyMeasurable),hk.map_eq]
    unfold valueH; congr 1; unfold rawK; change joint (⇑p*_)=joint F; rw [he]; unfold joint; simp_rw [hu]; exact H.symm
omit h
noncomputable def depthM(i:ℕ):Stud c 6:= Patria.march (i • a) x
noncomputable def meritX(x y:Stud c 6):ℂ:= valueH C (tallH T x*y)
local notation "K"=> meritX C T
local notation "ρ" i:arg => depthM a x i
local notation "η" i:arg=> depthM a y i
noncomputable abbrev bodyF (x: Stud c 6)(i:ℕ):= (meritX C T (depthM a x i) (depthM a x i)).re
include h hL hx hy
variable (ha:T.flip.act a= -a)
include ha
lemma bothM : K (ρ i) (η j) = K x (depthM a y (i+j)):=by
    unfold meritX depthM
    have hz(k:ℕ):T.flip.act (k • a
          )=-(k •a):=by change T.flip.actEquiv (k • a) =_; rw[map_nsmul,show T.flip.actEquiv a= _ from ha,smul_neg] -- parse binder
    let x':= Patria.march (i • a) x; let y':= Patria.march (j • a) y; have HV:= ((tallCost (R:=T) x' (marchP (i • a) x hx)).mult (marchP (j • a) y hy))
    rw [← costM C (i • a) h _ HV, movesM,show tallH T x'=march (-(i • a)) (tallH T x) from (by rw [← hz]; exact funext fun V=> commend (i • a) x T hL V),marched,neg_add_cancel,march0, show march (i • a) y'= _ from marched (j • a) (i • a) y,add_smul,add_comm (i • a)]
omit ha hx hy
include hh hu he
lemma spends (x:Stud c 6)(hx:Fence B x) : K x x= ((K x x).re:ℂ) ∧ 0 ≤ (K x x).re ∧ ‖K x x‖=(K x x).re:=by
    have hz:0 ≤ K x x:=by unfold meritX valueH rawK; rw [← tallC x C.zeroCut (show C.zeroCut.t=0 from h)]; exact mul_nonneg (inv_nonneg.mpr he.le) (Regulator.signed hL hu hh x hx)
    obtain ⟨hp,hx⟩:=Complex.nonneg_iff.mp hz; have hk:K x x=((K x x).re:ℂ):=Complex.ext (by simp) (by simpa using hx.symm); exact ⟨hk,hp,(congr_arg Norm.norm hk).trans (by rw [Complex.norm_real,Real.norm_of_nonneg hp])⟩
lemma costX (x y:Stud c 6)(hx:Fence B x)(hy:Fence B y): ‖K x y‖^2 ≤ ‖K x x‖*‖K y y‖:=by
    have hP := shears C h hu hx hy hL hh; dsimp only at hP; unfold meritX valueH; simp only [norm_mul]; nlinarith only [mul_le_mul_of_nonneg_left hP (sq_nonneg ‖C.Z⁻¹‖)]
omit hh hu he h hL
lemma relax (u v p q: Stud c 6)(c:ℂ)(hp:Tide.Stays u)(hq:Tide.Stays v)(hT:Tide.Stays p)(hY:Tide.Stays q):
    meritX C T (u+c • v) (p+c • q)=K u p+c*K u q+star c*K v p+star c*c*K v q:=by
    unfold meritX; let x:=tallH T u; let y:=tallH T v; have hx:Tide.Stays x:=tallCost (R:=T) u hp; have hy:Tide.Stays y:=tallCost (R:=T) v hq
    rw [show tallH T (u+c • v)= x+star c • y from (by funext i; simp [huesT,x,y]), add_mul,mul_add,mul_add]
    have hK:= stockC y (star c) hy; have hz:= stockC q c hY; rw [spentA C (x:=x*p+x*c • q) (y:=star c • y*p+star c • y* c • q) (((hx.mult hT).both (hx.mult hz)).flows continuous_add) (((hK.mult hT).both (hK.mult hz)).flows continuous_add), spentA C (hx.mult hT) (hx.mult hz),spentA C (hK.mult hT) (hK.mult hz)]; simp only [mul_smul_comm,smul_mul_assoc,Lyre.spend,smul_eq_mul]; unfold x y; ring
lemma growM (u v:Stud c 6)(z:ℂ) : depthM a (u+z • v) i = depthM a u i+ z • depthM a v i:=by funext V; unfold depthM march post; simp
include h hL hh hu he ha
lemma stroll (hp:∀ i≤n, Fence B (depthM a x i))(hv:i+2≤n):
    bodyF C T a x (i+1)-bodyF C T a x i ≤ bodyF C T a x (i+2)-bodyF C T a x (i+1):=by
   let v:=depthM a x; have hV(i:ℕ) (h:i≤n) : Fence B (v i):=hp i h
   have hx:Tide.Stays x:=by have hm:= (hp 0 (Nat.zero_le _)).hp; unfold depthM at hm; rw[zero_smul,march0 x] at hm; exact hm
   have h' := costX C T h hL hh hu he (v i) (v (i+2)) (hV i (by omega)) (hV (i+2) hv) -- arguments?
   have hQ : K (v i) (v (i+2))=K (v (i+1)) (v (i+1)):=by unfold v; rw [bothM C T a x x hx hx h hL ha,bothM C T a x x hx hx h hL ha,show i+(i+2)=i+1+(i+1) by omega]
   let F:=bodyF C T a x
   have hP(i:ℕ)(hm:i≤n):0 ≤ F i ∧ ‖K (v i) (v i)‖= F i:= (spends C T h hL hh hu he (v i) (hV i hm)).2
   rw [hQ,(hP (i+1) (by omega)).2,(hP i (by omega)).2,(hP _ hv).2] at h'; change F (i+1)-F i ≤ F (i+2)-F (i+1); nlinarith only [(hP _ hv).1,(hP i (by omega)).1,(hP (i+1) (by omega)).1,h',sq_nonneg (F (i+2)-F i)]
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.stroll

import YM.QCD.Raft.Energy

/-! # base kinetic and winding loss in leg charge for a real axial probe -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Bid Eyrie Stationary Quarry Work.F03 Exterior Matrix
open YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {n:Side}{η C:ℝ}
-- curvature of low read

def keyP:PlaqAxes:=⟨(0,1),by decide⟩
def melody (t:ℝ):TypeFace 2→ℂ:=Pi.single (plaquette keyP) (q (strandT t) 0)
abbrev poke (a:su.Color)(n:Side):=brace (pointT n 1) a
lemma residentQ (n:Side): Push.Loops.Matches (strandT (Pearl.beamH n)) (step 0:Site n):=by rw [← causeT,← wrap_step]; exact Push.Loops.quant_matches ..
lemma voicedG (n:Side): symbol 1 (strandT (Pearl.beamH n))*ᵥ sun 1=melody (Pearl.beamH n):=by
  funext i; obtain ⟨x,rfl⟩:=plaqEquiv.surjective i; rcases x with ⟨⟨p,Q⟩,h⟩; let A:PlaqAxes:=⟨(p,Q),h⟩; change (symbol 1 (strandT (Pearl.beamH n))*ᵥ sun 1) (plaquette A)=melody _ (plaquette A)
  rw [vapors_s (residentQ n)]; unfold A
  fin_cases p <;> fin_cases Q <;> first| contradiction| (simp +decide [q,melody,sun,Pi.single_apply,keyP,show ∀ i x:PlaqAxes,plaquette i=plaquette x ↔ i=x from fun i x=> plaqEquiv.injective.eq_iff,strandT]) -- parse q var
lemma packsG (a:su.Color)(k:ℕ)(x: Exterior.form k n)(i:su.ColorIndex): parts su k (arm su n k (career n k a x)) i= a i • x:=rfl
lemma cornS (a:su.Color)(p:TypeFace 2) (x:Site n)(i:su.ColorIndex): Exterior.d 1 n *ᵥ parts su 1 (arm su n 1 (poke a n).1) i = a i • vision (vw (step 0:Site n) (melody (Pearl.beamH n))) ∧ Exterior.d 1 n *ᵥ parts su 1 (arm su n 1 (poke a n).2) i = a i • desire (vw (step 0:Site n) (melody (Pearl.beamH n))):=by
  unfold poke brace; dsimp only
  rw [packsG,packsG, Matrix.mulVec_smul, Matrix.mulVec_smul, ← see, ← believe]; unfold pointT; rw [gradient_s (residentQ n),voicedG]; exact ⟨rfl,rfl⟩
lemma inkG (T:Bed)(a:su.Color)(hp:T.metric.strip η C)(he:0<η)(ha:‖a‖=1):
    let x:=arm su n 1 (poke a n).1; let y:=arm su n 1 (poke a n).2; let p:=strandT (Pearl.beamH n); let u:=plaquette keyP
    gaugeFiscal T x x+gaugeFiscal T y y=cap n* ‖Exterior.q p 0‖^2*(T.metric.read p u u).re:=by
  intro x y p u; let v:=step 0 (S:=Per n); let V:= melody (Pearl.beamH n); let F:=T.metric.read p
  let P:= vw v V; let A:= T.metric.acts n; let Z:= Exterior.q p 0
  let G:= vw v (F*ᵥ V)
  have hh : Push.Loops.cmat A *ᵥ P=G:=vw_fetch (Row.rights _ _ hp he.le) _ (residentQ n)
  have hg : vision P ⬝ᵥ (A*ᵥ vision P) + desire P ⬝ᵥ (A*ᵥ desire P) =(dotProduct (star P) (Push.Loops.cmat A *ᵥ P)).re:=by
    rw [← see,← believe]; unfold dotProduct; rw [Complex.re_sum, ← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; unfold vision desire; simp[Complex.mul_re]
  have hm : dotProduct (star P) G= (cap n:ℂ) * ((‖Z‖^2:ℝ):ℂ)*F u u :=by
    unfold dotProduct; rw [Fintype.sum_prod_type]; let X(h:Site n):= ∑ i:TypeFace 2, star P (h,i)*G (h,i)
    have he z:X z=((‖Z‖^2:ℝ):ℂ)*F u u:=by
      unfold X; rw [sum_eq_single u]; swap
      · intro b _ h; change star (_*V b)*_= _; unfold V melody; rw [Pi.single_eq_of_ne (show b ≠plaquette keyP from h)]; simp
      · unfold P G vw; dsimp only; unfold V melody; rw [Matrix.mulVec_single]; simp only [u,Pi.star_apply, Pi.single_eq_same]; -- inspect
        change star (cell v z * Z)*(cell v z*(F u u* Z))= _; rw [star_mul, Complex.star_def, cell_bar,Complex.sq_norm, ← Complex.mul_conj]; field_simp [show cell v z ≠0 from Complex.exp_ne_zero _]; unfold u; ring
      simp
    change ∑ z,X z=_; rw [sum_congr rfl fun a _=>he a,sum_const,card_univ,nsmul_eq_mul]; unfold cap; push_cast; ring
  have hC : ∑ i:su.ColorIndex,a i*a i=1:=by rw [← inner_color (G:=su), real_inner_self_eq_norm_sq,ha]; ring
  have hp i:= cornS a u (0:Site n) i; rw [Channel.fiscal_flux,Channel.fiscal_flux, ← Finset.sum_add_distrib]; -- replace
  let Q : ℝ:= cap n* ‖Z‖^2 * (F u u).re
  calc
    _ = ∑ i: su.ColorIndex,(a i*a i)*Q:=by
      apply sum_congr rfl; intro i _; rw [(hp i).1,(hp i).2,mulVec_smul,mulVec_smul,smul_dotProduct,smul_dotProduct,dotProduct_smul,dotProduct_smul]; rw [hh,hm] at hg; simp only [Complex.mul_re,Complex.ofReal_re, Complex.mul_im,Complex.ofReal_im, mul_zero,zero_mul, add_zero,sub_zero] at hg; change a i*(a i*_)+a i*(a i*_)=_ ; unfold Q; nlinarith only [show vision P ⬝ᵥ _+ desire P ⬝ᵥ _=Q from hg] -- inspect
    _= _ := by rw [← sum_mul,hC,one_mul]
end YM.QCD.Raft

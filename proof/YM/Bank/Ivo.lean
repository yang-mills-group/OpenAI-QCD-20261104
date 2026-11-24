import YM.Bank.Plank
import YM.Bank.Warm
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Ivo
open Function Precision Laurent Bloch Metric Gauge Wilson RG Finset Filter Lattice Exterior Next.Free
open Glyph Palm Jule Kith Peak Osc Pilot Bee Wale Analysis Maxwell Plank Learn
open Matrix
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators ComplexConjugate
variable {p q:Momentum}
open Complex (I)
lemma τ_formula (p:Momentum)(x:PlaqAxes)(y:Axis) : τ p 1 (plaquette x) (Exterior.coord y)= (if x.val.2=y then I*p x.val.1 else 0) -(if x.val.1=y then I*p x.val.2 else 0):=by
    let z:= x.val.1; let v:=x.val.2; have hz:z<v:= x.property
    let T:=plaquette x; have hh:T.val={z,v}:=rfl
    unfold τ wedge; rw [Matrix.sum_apply]; rw [← sum_subset (subset_univ ({z,v}: Finset Axis)), sum_insert (by simp [hz.ne]), sum_singleton]
    · have hv:z∈T.val:= mem_insert_self ..; have hw:v∈T.val:=mem_insert_of_mem (mem_singleton_self v)
      have hp : parity T.val z ℂ=1 :=by simp [parity,pre,hh,Finset.filter_insert,Finset.filter_singleton,hz.not_gt]; -- inspect
      have ht : parity T.val v ℂ = -1:=by simp [parity,pre,hh,Finset.filter_insert,Finset.filter_singleton,hz]
      have h₁: Exterior.remove z T hv=Exterior.coord v:=by ext; simp [Exterior.remove, Exterior.coord,hh]; rintro rfl; exact hz.ne'
      have h₂ : Exterior.remove v T hw=Exterior.coord z:=by ext i; by_cases hx : i=v <;> simp [hx,hh,Exterior.coord,Exterior.remove,hz.ne']
      simp only [Matrix.smul_apply,left,Matrix.of_apply,smul_eq_mul]; change I*_*(if h:z∈T.val then _ else 0)+I*_*(if h:v∈T.val then _ else 0)= (if v=y then _ else 0)-(if z=y then _ else 0); rw [dif_pos hv,dif_pos hw,h₁,h₂,hp,ht]; simp only [(show ∀ z k:Axis, Exterior.coord z=Exterior.coord k↔ z=k from fun _ _=>axisEquiv.injective.eq_iff)]; split_ifs <;> simp [z,v]<;>rfl
    intro i _ hi; change i∉ T.val at hi; rw [Matrix.smul_apply,left,of_apply,dif_neg hi,smul_zero]
lemma pow_home (p:Momentum)(hp:physical p) : (home p)⁻¹=(axle p)⁻¹ • (1:Matrix (TypeFace 1) (TypeFace 1) ℂ):=by
    by_cases he:p=0; · subst p; simp [home,lengthSq]
    have hg := lengthSq_pos he; apply Matrix.inv_eq_right_inv; unfold home; rw [axle_w hp,Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,smul_smul,mul_inv_cancel₀ (by exact_mod_cast hg.ne'),one_smul]
lemma grad_C (i:Axis)(f:E4→ℝ)(x:E4)(h:DifferentiableAt ℝ f x): Analysis.D (basis i) (fun x=> (f x:ℂ)) x = (↑(grad i f x:ℝ)):=by unfold grad Analysis.D; change fderiv ℝ (Complex.ofRealCLM ∘ f) x (basis i)=_; rw [fderiv_comp _ Complex.ofRealCLM.differentiableAt h, Complex.ofRealCLM.fderiv]; rfl
lemma green_one (a:Axis)(x:E4)(hx:x≠0): current [a] x=((grad a Green x:ℝ):ℂ):= grad_C _ _ x ((freeSmooth hx).differentiableAt (by simp))
lemma color2 (a b:Axis){x:E4}(hx:x≠0):current [a,b] x=↑(grad a (grad b Maxwell.Green) x:ℝ):=by
    refine (GermD (f:=current [b]) (g:=fun x=>↑(grad b Green x:ℝ)) (basis a) ((Eventually.mono (open_away.mem_nhds hx) fun y hy=> green_one b y hy))).trans (grad_C a (grad b Green) x ?_); exact (gradGradientSmooth hx b).differentiableAt (by simp)

def from_p (p q:PlaqAxes) : E4→ℂ:= fun x=> (bareCurl p.val.1 p.val.2 q.val.1 q.val.2 x:ℂ)
lemma kettle (p q:PlaqAxes): Flute (fun k=> oldG k (plaquette p) (plaquette q)) (from_p p q) 1:=by
    let A:=p.val.1; let B:=p.val.2; let C:=q.val.1; let D:=q.val.2
    let P : Axis→Axis→Axis→Axis→ Momentum→ℂ:=fun i b k l=> if i=b then Bee.field [k,l] else 0
    let S: Axis→Axis→Axis→Axis→ E4→ℂ:=fun i b k l=> if i=b then current [k,l] else 0
    have he i b k l: Flute (P i b k l) (S i b k l) 1:=by unfold P S; split; exact Flute.ful _ rfl; exact Flute.empty
    apply Flute.fiat (((he C B A D).sub (he D B A C)).sub ((he C A B D).sub (he D A B C))) -- orientation check Maxwell formula
    · intro k hk; unfold oldG; rw [pow_home k hk,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul, Matrix.smul_apply,Matrix.mul_apply,←Equiv.sum_comp axisEquiv];
      have hm(y:Axis): star (I*k y)= -(I*k y):=by rw [star_mul,show star (k y)=k y from congr_fun hk y]; simp[mul_comm]
      have hΔ (f:Momentum)(p:PlaqAxes)(b:Axis):τ f 1 (plaquette p) (axisEquiv b)=_:=τ_formula f p b
      simp only [Matrix.conjTranspose_apply, hΔ, apply_ite (star:ℂ→ℂ), star_zero, star_sub,hm,sub_mul,mul_sub,ite_mul,mul_ite,zero_mul,mul_zero, sum_sub_distrib,sum_ite_eq, sum_ite_eq', mem_univ, if_true]; unfold P Bee.field; simp only [Pi.sub_apply,apply_ite (fun F:Momentum→ℂ => F k),barrier,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]; unfold A B C D; simp only [eq_comm,dite_mul,mul_dite,Pi.zero_apply]; split_ifs <;> ring
    intro x hx; unfold S from_p bareCurl; simp only [Pi.sub_apply, ite_apply,Pi.zero_apply,color2 _ _ hx, Bare.opp_grad hx,Complex.ofReal_sub,apply_ite ((↑):ℝ→ℂ), Complex.ofReal_zero]; rfl
open QCD.Lat QCD
open Pearl Massive.UV.Free
def s_k (a b:Fiber): E4→ℂ:= fun x=> if a.2=b.2 then dirac a.1 b.1 x else 0
lemma fine_spin (p :Momentum)(hp:physical p)(x y:Fiber): vase shaft p x y = -(axle p)⁻¹ * ∑ i,I * p i * Lat.wave (gamma i) x y:=by
   have he: Flume.Para.quad (shaft p)=axle p:=by simp [Flume.Para.quad,shaft,axle]
   unfold vase Flume.Para.reciprocalP; rw [he,Flume.Para.model_smul,Matrix.smul_apply]; unfold Flume.Para.model Flume.Para.hiss Flume.Para.turn shaft
   simp only [zero_smul,zero_add,Matrix.smul_apply,Matrix.sum_apply,Pi.neg_apply,smul_eq_mul,mul_sum]; refine sum_congr rfl fun i _=>?_ ; ring
lemma vista (x y:Fiber): Flute (fun p=>Pearl.vase shaft p x y) (s_k x y) 0:=by
    let Z(i:Axis):= -(Lat.wave (gamma i) x y)
    apply Flute.fiat (Flute.tall univ (fun i=> Z i • Bee.field [i]) (fun i=> Z i • current [i]) (fun i _=> (Flute.ful _ (show [i].length=0+1 from rfl)).scale (Z i)))
    · intro p hp; rw [fine_spin p hp,Finset.sum_apply,Finset.mul_sum]; apply sum_congr rfl; intro i _; unfold Bee.field; simp [Z,barrier]; ring
    intro p hp; rw [Finset.sum_apply]; unfold s_k; have hv(i:Axis):Lat.wave (gamma i) x y= if x.2=y.2 then gamma i x.1 y.1 else 0:=by obtain ⟨a,b⟩:=x; obtain ⟨l,v⟩:=y; by_cases h:b=v<;>simp [Lat.wave,Matrix.one_apply,h]
    have he i:Analysis.D (basis i) Green p=grad i Green p:=rfl
    simp_rw [dirac,Pi.smul_apply,green_one _ _ hp,smul_eq_mul, Z,hv,he,←sum_neg_distrib]; split<;> simp_all
end YM.Bank.Ivo
#print axioms YM.Bank.Ivo.kettle
#print axioms YM.Bank.Ivo.vista

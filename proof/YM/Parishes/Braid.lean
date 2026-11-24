import YM.Parishes.Stair
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
set_option quotPrecheck false
namespace Stair
variable {w w' a b c₁ d₁ e y₃ ε ε' ε₁:ℝ}{Pt P Q R:BudgetPoint}
local notation "Wd" => fun (i:Jars d)=> u^(weightJ i)*princS x i P w
local notation "Sd"=>toted u x P w
local notation "W₁"=>wealth y.val Q.threshold w'
local notation "Wi"=>wealth x.val P.threshold w
variable {x y}
lemma wealth_zero (x:Label d)(p:BudgetPoint)(h:ℝ) (ht:x=0): wealth x.val p.threshold h=0:=by subst x; exact Finset.sum_eq_zero fun i _=> by rw [show (0:Label d).val=(0:Pol d) from rfl]; unfold Stative.fare; rw [map_zero,map_zero,norm_zero]
variable (x y)
lemma wealth_scale (z:ℂ) : wealth (z • x).val P.threshold w=‖z‖*Wi:= by unfold wealth; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> by change ‖chartL P w i (z • x)‖=‖z‖* _; rw [map_smul,norm_smul]; rfl)
lemma princ_scale (i:Jars d)(z:ℂ):princS (z • x) i P w=‖z‖*princS x i P w:= by unfold princS; rw [map_smul, wealth_scale]
lemma toted_g (z:ℂ): toted u (z • x) P w=‖z‖*Sd:=by unfold toted; rw [Finset.mul_sum]; exact sum_congr rfl fun i _=> by rw [princ_scale,mul_left_comm]
lemma climb (hY:TypeBeta u w w' v a ε' ε₁ P Q x y)(hp:ε₁≤ c₁)(he:ε' ≤ d₁): TypeBeta u w w' v a d₁ c₁ P Q x y:=by
    obtain ⟨g,hm,hK⟩:= hY.paid; exact ⟨g,fun i=>⟨(hm i).1,fun j hi=> ((hm i).2 j hi).trans (mul_le_mul_of_nonneg_right he (wealth_ge ..))⟩, hK.trans hp⟩
set_option maxHeartbeats 900000 in
lemma scaleK (hY: TypeBeta u w w' v a ε' ε₁ P Q x y) (z:ℂ): TypeBeta u w w' v a ε' (‖z‖*ε₁) P Q (z • x) (z • y):=by
   obtain ⟨g,hm,hP⟩:= hY.paid; refine ⟨(fun i=>z • g i),fun i=>⟨?_,?_⟩,?_⟩
   · rw [princ_scale,wealth_scale,mul_left_comm]; exact mul_le_mul_of_nonneg_left (hm i).1 (norm_nonneg _)
   · intro j hj; let k:ℂ:=(u:ℂ)^(UV.weight j.val); change ‖chartL Q w' j (z • g i)- k * chartL Q v j (gradeCut d i.val (z • x))‖ ≤ _; rw [map_smul,map_smul,map_smul,mul_smul_comm,← smul_sub,norm_smul,princ_scale x i z]; exact (mul_le_mul_of_nonneg_left ((hm i).2 j hj) (norm_nonneg _)).trans_eq (mul_left_comm ..)
   rw [← smul_sum, ← smul_sub,wealth_scale]; exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
lemma wealth_plus (p:BudgetPoint)(a:ℝ): wealth (x+y).val p.threshold a ≤ wealth x.val p.threshold a+wealth y.val p.threshold a:=by unfold wealth; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; change ‖chartL p a i (x+y)‖ ≤ _; rw [map_add]; exact norm_add_le ..
variable (y' :Label d)
-- for coadding copies on same input positive ray
set_option maxHeartbeats 850000 in
lemma merges (t₁ t₂ α₁ α₂:ℝ)(ht:0 ≤ t₁)(hv:0 ≤t₂)(hx:TypeBeta u w w' v a ε' α₁ P Q ((t₁:ℂ) • x) y) (hz:TypeBeta u w w' v a ε' α₂ P Q ((t₂:ℂ) • x) y'): TypeBeta u w w' v a ε' (α₁+α₂) P Q (((t₁+t₂:ℝ):ℂ) • x) (y+y'):=by
   obtain ⟨g,hg,hP⟩:= hx.paid; obtain ⟨f,hf,hQ⟩:= hz.paid; let X:= fun t:ℝ=>(t:ℂ) • x; have hp(i:Jars d): princS (X (t₁+t₂)) i P w=princS (X t₁) i P w+princS (X t₂) i P w:=by unfold X; rw [princ_scale,princ_scale,princ_scale]; simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,abs_of_nonneg hv,abs_of_nonneg (add_nonneg ht hv),add_mul]
   refine ⟨(fun i=>g i+f i),fun i=>⟨(wealth_plus ..).trans ((add_le_add (hg i).1 (hf i).1).trans_eq ?_),fun j hj=>?_⟩,?_⟩; · exact (congr_arg (fun x:ℝ=>a*u^weightJ i*x) (hp i).symm|> fun h=>by rw [mul_add] at h; exact h) -- edit
   · let k:ℂ:=(u:ℂ)^(UV.weight j.val); rw [show princS _ i P w=_ from hp i,mul_add,Complex.ofReal_add,add_smul]; change ‖chartL Q w' j (g i+f i)-k*chartL Q v j (gradeCut d i.val (X t₁+X t₂))‖≤_; rw [map_add,map_add,map_add,mul_add,add_sub_add_comm]; exact (norm_add_le ..).trans (add_le_add ((hg i).2 j hj) ((hf i).2 j hj))
   rw [sum_add_distrib,add_sub_add_comm]; exact (wealth_plus ..).trans (add_le_add hP hQ)
-- finite usage.Palette
variable {ι :Type}[Fintype ι][Nonempty ι]
lemma costsV (p:ι→ℝ)(H:ι→Label d)(hA:∀ i,0≤ p i)(h:∑ i,p i=1) (he:∀ i,TypeBeta u w w' v a ε' c₁ P Q x (H i)):TypeBeta u w w' v a ε' c₁ P Q x (∑ i,(p i:ℂ) • H i):=by
   let U (i:Finset ι):= ∑ j∈i,(p j:ℂ) • H j; have hf (i:Finset ι)(hx:i.Nonempty) : TypeBeta u w w' v a ε' ((∑ j∈i,p j)*c₁) P Q ( (↑(∑ j∈i,p j):ℂ) • x) (U i):=by
       induction i using Finset.induction_on with
       | empty=> exact (not_nonempty_empty hx).elim
       | @insert i s hi ih=>
            have he₁:=scaleK x (H i) (he i) (p i); rw [Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg (hA i)] at he₁
            by_cases hz:s.Nonempty; · rw [sum_insert hi,add_mul]; unfold U; rw [sum_insert hi]; exact merges x _ _ _ _ _ _ (hA i) (sum_nonneg fun j _=>hA _) he₁ (ih hz)
            rw [Finset.not_nonempty_iff_eq_empty] at hz; subst s; simpa only [sum_insert hi, sum_empty,U,add_zero] using he₁ -- simplify
   have he':= hf Finset.univ univ_nonempty; rw [h,one_mul,Complex.ofReal_one,one_smul] at he'; exact he'
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.costsV
